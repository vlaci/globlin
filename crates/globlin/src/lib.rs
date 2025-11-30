// SPDX-FileCopyrightText: 2023 Devon Govett <devongovett@gmail.com>
// SPDX-License-Identifier: MIT
//
// SPDX-FileCopyrightText: 2025 László Vaskó <opensource@vlaci.email>
// SPDX-License-Identifier: EUPL-1.2
use std::{ops::Range, path::is_separator};

#[derive(Clone, Copy, Debug, Default)]
struct State {
    // These store character indices into the glob and path strings.
    path_index: usize,
    glob_index: usize,

    // The current index into the captures list.
    capture_index: usize,

    // When we hit a * or **, we store the state for backtracking.
    wildcard: Wildcard,
    globstar: Wildcard,
}

#[derive(Clone, Copy, Debug, Default)]
struct Wildcard {
    // Using u32 rather than usize for these results in 10% faster performance.
    glob_index: u32,
    path_index: u32,
    capture_index: u32,
}

pub mod flags {
    pub const EMPTY: u8 = 0;
    pub const GLOB_STAR: u8 = 1 << 0;
    pub const BRACKET_EXPANSION: u8 = 1 << 1;
    pub const BRACE_EXPANSION: u8 = 1 << 2;
    pub const NEGATE: u8 = 1 << 3;
    pub const ESCAPE: u8 = 1 << 4;
    pub const DEFAULT: u8 = (1 << 5) - 1;
    pub const NO_PATH: u8 = 1 << 5;
}

macro_rules! flag_set {
    ($flags:ident, $check:expr) => {
        ($flags & $check) != 0
    };
}
macro_rules! flag_unset {
    ($flags:ident, $check:expr) => {
        ($flags & $check) == 0
    };
}

type Capture = Range<usize>;

pub fn glob_match(glob: &str, path: &str, flags: u8) -> bool {
    glob_match_internal(glob, path, None, flags)
}

#[allow(dead_code)] // TODO: figure out if we want capture support
pub fn glob_match_with_captures(glob: &str, path: &str) -> Option<Vec<Capture>> {
    let mut captures = Vec::new();
    if glob_match_internal(glob, path, Some(&mut captures), flags::DEFAULT) {
        return Some(captures);
    }
    None
}

fn glob_match_internal(
    glob: &str,
    path: &str,
    mut captures: Option<&mut Vec<Capture>>,
    flags: u8,
) -> bool {
    // This algorithm is based on https://research.swtch.com/glob
    let glob = glob.as_bytes();
    let path = path.as_bytes();

    let glob_star_enabled = flag_set!(flags, flags::GLOB_STAR);
    let bracket_expansion_enabled = flag_set!(flags, flags::BRACKET_EXPANSION);
    let brace_expansion_enabled = flag_set!(flags, flags::BRACE_EXPANSION);
    let escaping_enabled = flag_set!(flags, flags::ESCAPE);
    let negating_enabled = flag_set!(flags, flags::NEGATE);
    let path_separator_enabled = flag_unset!(flags, flags::NO_PATH);

    let mut state = State::default();

    // Store the state when we see an opening '{' brace in a stack.
    // Up to 10 nested braces are supported.
    let mut brace_stack = BraceStack::default();

    // First, check if the pattern is negated with a leading '!' character.
    // Multiple negations can occur.
    let mut negated = false;
    while negating_enabled && state.glob_index < glob.len() && glob[state.glob_index] == b'!' {
        negated = !negated;
        state.glob_index += 1;
    }

    while state.glob_index < glob.len() || state.path_index < path.len() {
        if state.glob_index < glob.len() {
            match glob[state.glob_index] {
                b'*' => {
                    let is_globstar = glob_star_enabled
                        && (state.glob_index + 1 < glob.len()
                            && glob[state.glob_index + 1] == b'*');
                    if is_globstar {
                        // Coalesce multiple ** segments into one.
                        state.glob_index = skip_globstars(glob, state.glob_index + 2) - 2;
                    }

                    // If we are on a different glob index than before, start a new capture.
                    // Otherwise, extend the active one.
                    if captures.is_some()
                        && (captures.as_ref().unwrap().is_empty()
                            || state.glob_index != state.wildcard.glob_index as usize)
                    {
                        state.wildcard.capture_index = state.capture_index as u32;
                        state.begin_capture(&mut captures, state.path_index..state.path_index);
                    } else {
                        state.extend_capture(&mut captures);
                    }

                    state.wildcard.glob_index = state.glob_index as u32;
                    state.wildcard.path_index = state.path_index as u32 + 1;

                    // ** allows path separators, whereas * does not.
                    // However, ** must be a full path component, i.e. a/**/b not a**b.
                    if is_globstar {
                        state.glob_index += 2;

                        if glob.len() == state.glob_index {
                            // A trailing ** segment without a following separator.
                            state.globstar = state.wildcard;
                        } else if (state.glob_index < 3 || glob[state.glob_index - 3] == b'/')
                            && glob[state.glob_index] == b'/'
                        {
                            // Matched a full /**/ segment. If the last character in the path was a separator,
                            // skip the separator in the glob so we search for the next character.
                            // In effect, this makes the whole segment optional so that a/**/b matches a/b.
                            if state.path_index == 0
                                || (state.path_index < path.len()
                                    && is_separator(path[state.path_index - 1] as char))
                            {
                                state.end_capture(&mut captures);
                                state.glob_index += 1;
                            }

                            // The allows_sep flag allows separator characters in ** matches.
                            // one is a '/', which prevents a/**/b from matching a/bb.
                            state.globstar = state.wildcard;
                        }
                    } else {
                        state.glob_index += 1;
                    }

                    // If we are in a * segment and hit a separator,
                    // either jump back to a previous ** or end the wildcard.
                    if path_separator_enabled
                        && state.globstar.path_index != state.wildcard.path_index
                        && state.path_index < path.len()
                        && is_separator(path[state.path_index] as char)
                    {
                        // Special case: don't jump back for a / at the end of the glob.
                        if state.globstar.path_index > 0 && state.path_index + 1 < path.len() {
                            state.glob_index = state.globstar.glob_index as usize;
                            state.capture_index = state.globstar.capture_index as usize;
                            state.wildcard.glob_index = state.globstar.glob_index;
                            state.wildcard.capture_index = state.globstar.capture_index;
                        } else {
                            state.wildcard.path_index = 0;
                        }
                    }

                    // If the next char is a special brace separator,
                    // skip to the end of the braces so we don't try to match it.
                    if brace_stack.length > 0
                        && state.glob_index < glob.len()
                        && matches!(glob[state.glob_index], b',' | b'}')
                        && state.skip_braces(glob, &mut captures, false) == BraceState::Invalid
                    {
                        // invalid pattern!
                        return false;
                    }

                    continue;
                }
                b'?' if state.path_index < path.len() => {
                    if !path_separator_enabled || !is_separator(path[state.path_index] as char) {
                        state.add_char_capture(&mut captures);
                        state.glob_index += 1;
                        state.path_index += 1;
                        continue;
                    }
                }
                b'[' if bracket_expansion_enabled && state.path_index < path.len() => {
                    state.glob_index += 1;
                    let c = path[state.path_index];

                    // Check if the character class is negated.
                    let mut negated = false;
                    if state.glob_index < glob.len()
                        && matches!(glob[state.glob_index], b'^' | b'!')
                    {
                        negated = true;
                        state.glob_index += 1;
                    }

                    // Try each range.
                    let mut first = true;
                    let mut is_match = false;
                    while state.glob_index < glob.len() && (first || glob[state.glob_index] != b']')
                    {
                        let mut low = glob[state.glob_index];
                        if escaping_enabled && !unescape(&mut low, glob, &mut state.glob_index) {
                            // Invalid pattern!
                            return false;
                        }
                        state.glob_index += 1;

                        // If there is a - and the following character is not ], read the range end character.
                        let high = if state.glob_index + 1 < glob.len()
                            && glob[state.glob_index] == b'-'
                            && glob[state.glob_index + 1] != b']'
                        {
                            state.glob_index += 1;
                            let mut high = glob[state.glob_index];
                            if escaping_enabled && !unescape(&mut high, glob, &mut state.glob_index)
                            {
                                // Invalid pattern!
                                return false;
                            }
                            state.glob_index += 1;
                            high
                        } else {
                            low
                        };

                        if low <= c && c <= high {
                            is_match = true;
                        }
                        first = false;
                    }
                    if state.glob_index >= glob.len() {
                        // invalid pattern!
                        return false;
                    }
                    state.glob_index += 1;
                    if is_match != negated {
                        state.add_char_capture(&mut captures);
                        state.path_index += 1;
                        continue;
                    }
                }
                b'{' if brace_expansion_enabled && state.path_index < path.len() => {
                    if brace_stack.length as usize >= brace_stack.stack.len() {
                        // Invalid pattern! Too many nested braces.
                        return false;
                    }

                    state.end_capture(&mut captures);
                    state.begin_capture(&mut captures, state.path_index..state.path_index);

                    // Push old state to the stack, and reset current state.
                    state = brace_stack.push(&state);
                    continue;
                }
                b'}' if brace_stack.length > 0 => {
                    // If we hit the end of the braces, we matched the last option.
                    brace_stack.longest_brace_match =
                        brace_stack.longest_brace_match.max(state.path_index as u32);
                    state.glob_index += 1;
                    state = brace_stack.pop(&state, &mut captures);
                    continue;
                }
                b',' if brace_stack.length > 0 => {
                    // If we hit a comma, we matched one of the options!
                    // But we still need to check the others in case there is a longer match.
                    brace_stack.longest_brace_match =
                        brace_stack.longest_brace_match.max(state.path_index as u32);
                    state.path_index = brace_stack.last().path_index;
                    state.glob_index += 1;
                    state.wildcard = Wildcard::default();
                    state.globstar = Wildcard::default();
                    continue;
                }
                mut c if state.path_index < path.len() => {
                    // Match escaped characters as literals.
                    if escaping_enabled && !unescape(&mut c, glob, &mut state.glob_index) {
                        // Invalid pattern!
                        return false;
                    }

                    let is_match = if c == b'/' {
                        is_separator(path[state.path_index] as char)
                    } else {
                        path[state.path_index] == c
                    };

                    if is_match {
                        state.end_capture(&mut captures);

                        if brace_stack.length > 0
                            && state.glob_index > 0
                            && glob[state.glob_index - 1] == b'}'
                        {
                            brace_stack.longest_brace_match = state.path_index as u32;
                            state = brace_stack.pop(&state, &mut captures);
                        }
                        state.glob_index += 1;
                        state.path_index += 1;

                        // If this is not a separator, lock in the previous globstar.
                        if c != b'/' {
                            state.globstar.path_index = 0;
                        }
                        continue;
                    }
                }
                _ => {}
            }
        }

        // If we didn't match, restore state to the previous star pattern.
        if state.wildcard.path_index > 0 && state.wildcard.path_index as usize <= path.len() {
            state.backtrack();
            continue;
        }

        if brace_stack.length > 0 {
            // If in braces, find next option and reset path to index where we saw the '{'
            match state.skip_braces(glob, &mut captures, true) {
                BraceState::Invalid => return false,
                BraceState::Comma => {
                    state.path_index = brace_stack.last().path_index;
                    continue;
                }
                BraceState::EndBrace => {}
            }

            // Hit the end. Pop the stack.
            // If we matched a previous option, use that.
            if brace_stack.longest_brace_match > 0 {
                state = brace_stack.pop(&state, &mut captures);
                continue;
            } else {
                // Didn't match. Restore state, and check if we need to jump back to a star pattern.
                state = *brace_stack.last();
                brace_stack.length -= 1;
                if let Some(captures) = &mut captures {
                    captures.truncate(state.capture_index);
                }
                if state.wildcard.path_index > 0 && state.wildcard.path_index as usize <= path.len()
                {
                    state.backtrack();
                    continue;
                }
            }
        }

        return negated;
    }

    if brace_stack.length > 0 && state.glob_index > 0 && glob[state.glob_index - 1] == b'}' {
        brace_stack.longest_brace_match = state.path_index as u32;
        brace_stack.pop(&state, &mut captures);
    }

    !negated
}

#[inline(always)]
fn unescape(c: &mut u8, glob: &[u8], glob_index: &mut usize) -> bool {
    if *c == b'\\' {
        *glob_index += 1;
        if *glob_index >= glob.len() {
            // Invalid pattern!
            return false;
        }
        *c = match glob[*glob_index] {
            b'a' => b'\x61',
            b'b' => b'\x08',
            b'n' => b'\n',
            b'r' => b'\r',
            b't' => b'\t',
            c => c,
        }
    }
    true
}

#[derive(PartialEq)]
enum BraceState {
    Invalid,
    Comma,
    EndBrace,
}

impl State {
    #[inline(always)]
    fn backtrack(&mut self) {
        self.glob_index = self.wildcard.glob_index as usize;
        self.path_index = self.wildcard.path_index as usize;
        self.capture_index = self.wildcard.capture_index as usize;
    }

    #[inline(always)]
    fn begin_capture(&self, captures: &mut Option<&mut Vec<Capture>>, capture: Capture) {
        if let Some(captures) = captures {
            if self.capture_index < captures.len() {
                captures[self.capture_index] = capture;
            } else {
                captures.push(capture);
            }
        }
    }

    #[inline(always)]
    fn extend_capture(&self, captures: &mut Option<&mut Vec<Capture>>) {
        if let Some(captures) = captures {
            if self.capture_index < captures.len() {
                captures[self.capture_index].end = self.path_index;
            }
        }
    }

    #[inline(always)]
    fn end_capture(&mut self, captures: &mut Option<&mut Vec<Capture>>) {
        if let Some(captures) = captures {
            if self.capture_index < captures.len() {
                self.capture_index += 1;
            }
        }
    }

    #[inline(always)]
    fn add_char_capture(&mut self, captures: &mut Option<&mut Vec<Capture>>) {
        self.end_capture(captures);
        self.begin_capture(captures, self.path_index..self.path_index + 1);
        self.capture_index += 1;
    }

    fn skip_braces(
        &mut self,
        glob: &[u8],
        captures: &mut Option<&mut Vec<Capture>>,
        stop_on_comma: bool,
    ) -> BraceState {
        let mut braces = 1;
        let mut in_brackets = false;
        let mut capture_index = self.capture_index + 1;
        while self.glob_index < glob.len() && braces > 0 {
            match glob[self.glob_index] {
                // Skip nested braces.
                b'{' if !in_brackets => braces += 1,
                b'}' if !in_brackets => braces -= 1,
                b',' if stop_on_comma && braces == 1 && !in_brackets => {
                    self.glob_index += 1;
                    return BraceState::Comma;
                }
                c @ (b'*' | b'?' | b'[') if !in_brackets => {
                    if c == b'[' {
                        in_brackets = true;
                    }
                    if let Some(captures) = captures {
                        if capture_index < captures.len() {
                            captures[capture_index] = self.path_index..self.path_index;
                        } else {
                            captures.push(self.path_index..self.path_index);
                        }
                        capture_index += 1;
                    }
                    if c == b'*'
                        && self.glob_index + 1 < glob.len()
                        && glob[self.glob_index + 1] == b'*'
                    {
                        self.glob_index = skip_globstars(glob, self.glob_index + 2) - 2;
                        self.glob_index += 1;
                    }
                }
                b']' => in_brackets = false,
                b'\\' => {
                    self.glob_index += 1;
                }
                _ => {}
            }
            self.glob_index += 1;
        }

        if braces != 0 {
            return BraceState::Invalid;
        }

        BraceState::EndBrace
    }
}

#[inline(always)]
fn skip_globstars(glob: &[u8], mut glob_index: usize) -> usize {
    // Coalesce multiple ** segments into one.
    while glob_index + 3 <= glob.len()
        && unsafe { glob.get_unchecked(glob_index..glob_index + 3) } == b"/**"
    {
        glob_index += 3;
    }
    glob_index
}

struct BraceStack {
    stack: [State; 10],
    length: u32,
    longest_brace_match: u32,
}

impl Default for BraceStack {
    #[inline]
    fn default() -> Self {
        // Manual implementation is faster than the automatically derived one.
        BraceStack {
            stack: [State::default(); 10],
            length: 0,
            longest_brace_match: 0,
        }
    }
}

impl BraceStack {
    #[inline(always)]
    fn push(&mut self, state: &State) -> State {
        // Push old state to the stack, and reset current state.
        self.stack[self.length as usize] = *state;
        self.length += 1;
        State {
            path_index: state.path_index,
            glob_index: state.glob_index + 1,
            capture_index: state.capture_index + 1,
            ..State::default()
        }
    }

    #[inline(always)]
    fn pop(&mut self, state: &State, captures: &mut Option<&mut Vec<Capture>>) -> State {
        self.length -= 1;
        let mut state = State {
            path_index: self.longest_brace_match as usize,
            glob_index: state.glob_index,
            // But restore star state if needed later.
            wildcard: self.stack[self.length as usize].wildcard,
            globstar: self.stack[self.length as usize].globstar,
            capture_index: self.stack[self.length as usize].capture_index,
        };
        if self.length == 0 {
            self.longest_brace_match = 0;
        }
        state.extend_capture(captures);
        if let Some(captures) = captures {
            state.capture_index = captures.len();
        }

        state
    }

    #[inline(always)]
    fn last(&self) -> &State {
        &self.stack[self.length as usize - 1]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        assert!(glob_match("abc", "abc", flags::DEFAULT));
        assert!(glob_match("*", "abc", flags::DEFAULT));
        assert!(glob_match("*", "", flags::DEFAULT));
        assert!(glob_match("**", "", flags::DEFAULT));
        assert!(glob_match("*c", "abc", flags::DEFAULT));
        assert!(!glob_match("*b", "abc", flags::DEFAULT));
        assert!(glob_match("a*", "abc", flags::DEFAULT));
        assert!(!glob_match("b*", "abc", flags::DEFAULT));
        assert!(glob_match("a*", "a", flags::DEFAULT));
        assert!(glob_match("*a", "a", flags::DEFAULT));
        assert!(glob_match("a*b*c*d*e*", "axbxcxdxe", flags::DEFAULT));
        assert!(glob_match("a*b*c*d*e*", "axbxcxdxexxx", flags::DEFAULT));
        assert!(glob_match("a*b?c*x", "abxbbxdbxebxczzx", flags::DEFAULT));
        assert!(!glob_match("a*b?c*x", "abxbbxdbxebxczzy", flags::DEFAULT));

        assert!(glob_match("a/*/test", "a/foo/test", flags::DEFAULT));
        assert!(!glob_match("a/*/test", "a/foo/bar/test", flags::DEFAULT));
        assert!(glob_match("a/**/test", "a/foo/test", flags::DEFAULT));
        assert!(glob_match("a/**/test", "a/foo/bar/test", flags::DEFAULT));
        assert!(glob_match("a/**/b/c", "a/foo/bar/b/c", flags::DEFAULT));
        assert!(glob_match("a\\*b", "a*b", flags::DEFAULT));
        assert!(!glob_match("a\\*b", "axb", flags::DEFAULT));

        assert!(glob_match("[abc]", "a", flags::DEFAULT));
        assert!(glob_match("[abc]", "b", flags::DEFAULT));
        assert!(glob_match("[abc]", "c", flags::DEFAULT));
        assert!(!glob_match("[abc]", "d", flags::DEFAULT));
        assert!(glob_match("x[abc]x", "xax", flags::DEFAULT));
        assert!(glob_match("x[abc]x", "xbx", flags::DEFAULT));
        assert!(glob_match("x[abc]x", "xcx", flags::DEFAULT));
        assert!(!glob_match("x[abc]x", "xdx", flags::DEFAULT));
        assert!(!glob_match("x[abc]x", "xay", flags::DEFAULT));
        assert!(glob_match("[?]", "?", flags::DEFAULT));
        assert!(!glob_match("[?]", "a", flags::DEFAULT));
        assert!(glob_match("[*]", "*", flags::DEFAULT));
        assert!(!glob_match("[*]", "a", flags::DEFAULT));

        assert!(glob_match("[a-cx]", "a", flags::DEFAULT));
        assert!(glob_match("[a-cx]", "b", flags::DEFAULT));
        assert!(glob_match("[a-cx]", "c", flags::DEFAULT));
        assert!(!glob_match("[a-cx]", "d", flags::DEFAULT));
        assert!(glob_match("[a-cx]", "x", flags::DEFAULT));

        assert!(!glob_match("[^abc]", "a", flags::DEFAULT));
        assert!(!glob_match("[^abc]", "b", flags::DEFAULT));
        assert!(!glob_match("[^abc]", "c", flags::DEFAULT));
        assert!(glob_match("[^abc]", "d", flags::DEFAULT));
        assert!(!glob_match("[!abc]", "a", flags::DEFAULT));
        assert!(!glob_match("[!abc]", "b", flags::DEFAULT));
        assert!(!glob_match("[!abc]", "c", flags::DEFAULT));
        assert!(glob_match("[!abc]", "d", flags::DEFAULT));
        assert!(glob_match("[\\!]", "!", flags::DEFAULT));

        assert!(glob_match("a*b*[cy]*d*e*", "axbxcxdxexxx", flags::DEFAULT));
        assert!(glob_match("a*b*[cy]*d*e*", "axbxyxdxexxx", flags::DEFAULT));
        assert!(glob_match(
            "a*b*[cy]*d*e*",
            "axbxxxyxdxexxx",
            flags::DEFAULT
        ));

        assert!(glob_match("test.{jpg,png}", "test.jpg", flags::DEFAULT));
        assert!(glob_match("test.{jpg,png}", "test.png", flags::DEFAULT));
        assert!(glob_match("test.{j*g,p*g}", "test.jpg", flags::DEFAULT));
        assert!(glob_match("test.{j*g,p*g}", "test.jpxxxg", flags::DEFAULT));
        assert!(glob_match("test.{j*g,p*g}", "test.jxg", flags::DEFAULT));
        assert!(!glob_match("test.{j*g,p*g}", "test.jnt", flags::DEFAULT));
        assert!(glob_match("test.{j*g,j*c}", "test.jnc", flags::DEFAULT));
        assert!(glob_match("test.{jpg,p*g}", "test.png", flags::DEFAULT));
        assert!(glob_match("test.{jpg,p*g}", "test.pxg", flags::DEFAULT));
        assert!(!glob_match("test.{jpg,p*g}", "test.pnt", flags::DEFAULT));
        assert!(glob_match("test.{jpeg,png}", "test.jpeg", flags::DEFAULT));
        assert!(!glob_match("test.{jpeg,png}", "test.jpg", flags::DEFAULT));
        assert!(glob_match("test.{jpeg,png}", "test.png", flags::DEFAULT));
        assert!(glob_match("test.{jp\\,g,png}", "test.jp,g", flags::DEFAULT));
        assert!(!glob_match("test.{jp\\,g,png}", "test.jxg", flags::DEFAULT));
        assert!(glob_match(
            "test/{foo,bar}/baz",
            "test/foo/baz",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "test/{foo,bar}/baz",
            "test/bar/baz",
            flags::DEFAULT
        ));
        assert!(!glob_match(
            "test/{foo,bar}/baz",
            "test/baz/baz",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "test/{foo*,bar*}/baz",
            "test/foooooo/baz",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "test/{foo*,bar*}/baz",
            "test/barrrrr/baz",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "test/{*foo,*bar}/baz",
            "test/xxxxfoo/baz",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "test/{*foo,*bar}/baz",
            "test/xxxxbar/baz",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "test/{foo/**,bar}/baz",
            "test/bar/baz",
            flags::DEFAULT
        ));
        assert!(!glob_match(
            "test/{foo/**,bar}/baz",
            "test/bar/test/baz",
            flags::DEFAULT
        ));

        assert!(!glob_match(
            "*.txt",
            "some/big/path/to/the/needle.txt",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "some/**/needle.{js,tsx,mdx,ts,jsx,txt}",
            "some/a/bigger/path/to/the/crazy/needle.txt",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "some/**/{a,b,c}/**/needle.txt",
            "some/foo/a/bigger/path/to/the/crazy/needle.txt",
            flags::DEFAULT
        ));
        assert!(!glob_match(
            "some/**/{a,b,c}/**/needle.txt",
            "some/foo/d/bigger/path/to/the/crazy/needle.txt",
            flags::DEFAULT
        ));
        assert!(glob_match("a/{a{a,b},b}", "a/aa", flags::DEFAULT));
        assert!(glob_match("a/{a{a,b},b}", "a/ab", flags::DEFAULT));
        assert!(!glob_match("a/{a{a,b},b}", "a/ac", flags::DEFAULT));
        assert!(glob_match("a/{a{a,b},b}", "a/b", flags::DEFAULT));
        assert!(!glob_match("a/{a{a,b},b}", "a/c", flags::DEFAULT));
        assert!(glob_match("a/{b,c[}]*}", "a/b", flags::DEFAULT));
        assert!(glob_match("a/{b,c[}]*}", "a/c}xx", flags::DEFAULT));
    }

    #[test]
    fn no_globstar() {
        assert!(glob_match(
            "some/**/needle.txt",
            "some/path/needle.txt",
            flags::DEFAULT ^ flags::GLOB_STAR
        ));
        assert!(!glob_match(
            "some/**/needle.txt",
            "some/big/path/to/needle.txt",
            flags::DEFAULT ^ flags::GLOB_STAR
        ));
        assert!(!glob_match(
            "some/b**o/needle.txt",
            "some/big/path/to/needle.txt",
            flags::DEFAULT ^ flags::GLOB_STAR
        ));
    }

    #[test]
    fn no_path() {
        assert!(glob_match(
            "some/*/needle.txt",
            "some/path/needle.txt",
            flags::DEFAULT | flags::NO_PATH
        ));
        assert!(glob_match(
            "some/*/needle.txt",
            "some/big/path/to/needle.txt",
            flags::DEFAULT | flags::NO_PATH
        ));
        assert!(!glob_match(
            "some/small/*/needle.txt",
            "some/big/path/to/needle.txt",
            flags::DEFAULT | flags::NO_PATH
        ));
        assert!(glob_match(
            "some?needle.txt",
            "some/needle.txt",
            flags::DEFAULT | flags::NO_PATH
        ));
    }

    #[test]
    fn no_bracket_expansion() {
        assert!(!glob_match(
            "[ab]",
            "a",
            flags::DEFAULT ^ flags::BRACKET_EXPANSION
        ));
        assert!(!glob_match(
            "[a-z]",
            "c",
            flags::DEFAULT ^ flags::BRACKET_EXPANSION
        ));
        assert!(glob_match(
            "[ab]",
            "[ab]",
            flags::DEFAULT ^ flags::BRACKET_EXPANSION
        ));
        assert!(glob_match(
            "[a-z]",
            "[a-z]",
            flags::DEFAULT ^ flags::BRACKET_EXPANSION
        ));
        assert!(glob_match(
            "[!?]",
            "[!a]",
            flags::DEFAULT ^ flags::BRACKET_EXPANSION
        ));
    }
    #[test]
    fn no_brace_expansion() {
        assert!(!glob_match(
            "{a,b}",
            "a",
            flags::DEFAULT ^ flags::BRACE_EXPANSION
        ));
        assert!(!glob_match(
            "{a,?}",
            "c",
            flags::DEFAULT ^ flags::BRACE_EXPANSION
        ));
        assert!(glob_match(
            "{a,a}",
            "{a,a}",
            flags::DEFAULT ^ flags::BRACE_EXPANSION
        ));
        assert!(glob_match(
            "{a,?}",
            "{a,z}",
            flags::DEFAULT ^ flags::BRACE_EXPANSION
        ));
    }

    #[test]
    fn no_escape() {
        assert!(!glob_match(r"\*", "*", flags::DEFAULT ^ flags::ESCAPE));
        assert!(glob_match(
            r"\*",
            r"\needle.txt",
            flags::DEFAULT ^ flags::ESCAPE
        ));
        assert!(glob_match(r"\?", r"\a", flags::DEFAULT ^ flags::ESCAPE));
        assert!(glob_match(r"\[ab]", r"\a", flags::DEFAULT ^ flags::ESCAPE));
    }
    #[test]
    fn no_negate() {
        assert!(!glob_match("!a", "b", flags::DEFAULT ^ flags::NEGATE));
        assert!(glob_match("!a", "!a", flags::DEFAULT ^ flags::NEGATE));
        assert!(glob_match("!?", "!!", flags::DEFAULT ^ flags::NEGATE));
    }

    // The below tests are based on Bash and micromatch.
    // https://github.com/micromatch/picomatch/blob/master/test/bash.js
    // Converted using the following find and replace regex:
    // find: assert\(([!])?isMatch\('(.*?)', ['"](.*?)['"]\)\);
    // replace: assert!($1glob_match("$3", "$2", flags::DEFAULT));

    #[test]
    fn bash() {
        assert!(!glob_match("a*", "*", flags::DEFAULT));
        assert!(!glob_match("a*", "**", flags::DEFAULT));
        assert!(!glob_match("a*", "\\*", flags::DEFAULT));
        assert!(!glob_match("a*", "a/*", flags::DEFAULT));
        assert!(!glob_match("a*", "b", flags::DEFAULT));
        assert!(!glob_match("a*", "bc", flags::DEFAULT));
        assert!(!glob_match("a*", "bcd", flags::DEFAULT));
        assert!(!glob_match("a*", "bdir/", flags::DEFAULT));
        assert!(!glob_match("a*", "Beware", flags::DEFAULT));
        assert!(glob_match("a*", "a", flags::DEFAULT));
        assert!(glob_match("a*", "ab", flags::DEFAULT));
        assert!(glob_match("a*", "abc", flags::DEFAULT));

        assert!(!glob_match("\\a*", "*", flags::DEFAULT));
        assert!(!glob_match("\\a*", "**", flags::DEFAULT));
        assert!(!glob_match("\\a*", "\\*", flags::DEFAULT));

        assert!(glob_match("\\a*", "a", flags::DEFAULT));
        assert!(!glob_match("\\a*", "a/*", flags::DEFAULT));
        assert!(glob_match("\\a*", "abc", flags::DEFAULT));
        assert!(glob_match("\\a*", "abd", flags::DEFAULT));
        assert!(glob_match("\\a*", "abe", flags::DEFAULT));
        assert!(!glob_match("\\a*", "b", flags::DEFAULT));
        assert!(!glob_match("\\a*", "bb", flags::DEFAULT));
        assert!(!glob_match("\\a*", "bcd", flags::DEFAULT));
        assert!(!glob_match("\\a*", "bdir/", flags::DEFAULT));
        assert!(!glob_match("\\a*", "Beware", flags::DEFAULT));
        assert!(!glob_match("\\a*", "c", flags::DEFAULT));
        assert!(!glob_match("\\a*", "ca", flags::DEFAULT));
        assert!(!glob_match("\\a*", "cb", flags::DEFAULT));
        assert!(!glob_match("\\a*", "d", flags::DEFAULT));
        assert!(!glob_match("\\a*", "dd", flags::DEFAULT));
        assert!(!glob_match("\\a*", "de", flags::DEFAULT));
    }

    #[test]
    fn bash_directories() {
        assert!(!glob_match("b*/", "*", flags::DEFAULT));
        assert!(!glob_match("b*/", "**", flags::DEFAULT));
        assert!(!glob_match("b*/", "\\*", flags::DEFAULT));
        assert!(!glob_match("b*/", "a", flags::DEFAULT));
        assert!(!glob_match("b*/", "a/*", flags::DEFAULT));
        assert!(!glob_match("b*/", "abc", flags::DEFAULT));
        assert!(!glob_match("b*/", "abd", flags::DEFAULT));
        assert!(!glob_match("b*/", "abe", flags::DEFAULT));
        assert!(!glob_match("b*/", "b", flags::DEFAULT));
        assert!(!glob_match("b*/", "bb", flags::DEFAULT));
        assert!(!glob_match("b*/", "bcd", flags::DEFAULT));
        assert!(glob_match("b*/", "bdir/", flags::DEFAULT));
        assert!(!glob_match("b*/", "Beware", flags::DEFAULT));
        assert!(!glob_match("b*/", "c", flags::DEFAULT));
        assert!(!glob_match("b*/", "ca", flags::DEFAULT));
        assert!(!glob_match("b*/", "cb", flags::DEFAULT));
        assert!(!glob_match("b*/", "d", flags::DEFAULT));
        assert!(!glob_match("b*/", "dd", flags::DEFAULT));
        assert!(!glob_match("b*/", "de", flags::DEFAULT));
    }

    #[test]
    fn bash_escaping() {
        assert!(!glob_match("\\^", "*", flags::DEFAULT));
        assert!(!glob_match("\\^", "**", flags::DEFAULT));
        assert!(!glob_match("\\^", "\\*", flags::DEFAULT));
        assert!(!glob_match("\\^", "a", flags::DEFAULT));
        assert!(!glob_match("\\^", "a/*", flags::DEFAULT));
        assert!(!glob_match("\\^", "abc", flags::DEFAULT));
        assert!(!glob_match("\\^", "abd", flags::DEFAULT));
        assert!(!glob_match("\\^", "abe", flags::DEFAULT));
        assert!(!glob_match("\\^", "b", flags::DEFAULT));
        assert!(!glob_match("\\^", "bb", flags::DEFAULT));
        assert!(!glob_match("\\^", "bcd", flags::DEFAULT));
        assert!(!glob_match("\\^", "bdir/", flags::DEFAULT));
        assert!(!glob_match("\\^", "Beware", flags::DEFAULT));
        assert!(!glob_match("\\^", "c", flags::DEFAULT));
        assert!(!glob_match("\\^", "ca", flags::DEFAULT));
        assert!(!glob_match("\\^", "cb", flags::DEFAULT));
        assert!(!glob_match("\\^", "d", flags::DEFAULT));
        assert!(!glob_match("\\^", "dd", flags::DEFAULT));
        assert!(!glob_match("\\^", "de", flags::DEFAULT));

        assert!(glob_match("\\*", "*", flags::DEFAULT));
        // assert!(glob_match("\\*", "\\*", flags::DEFAULT));
        assert!(!glob_match("\\*", "**", flags::DEFAULT));
        assert!(!glob_match("\\*", "a", flags::DEFAULT));
        assert!(!glob_match("\\*", "a/*", flags::DEFAULT));
        assert!(!glob_match("\\*", "abc", flags::DEFAULT));
        assert!(!glob_match("\\*", "abd", flags::DEFAULT));
        assert!(!glob_match("\\*", "abe", flags::DEFAULT));
        assert!(!glob_match("\\*", "b", flags::DEFAULT));
        assert!(!glob_match("\\*", "bb", flags::DEFAULT));
        assert!(!glob_match("\\*", "bcd", flags::DEFAULT));
        assert!(!glob_match("\\*", "bdir/", flags::DEFAULT));
        assert!(!glob_match("\\*", "Beware", flags::DEFAULT));
        assert!(!glob_match("\\*", "c", flags::DEFAULT));
        assert!(!glob_match("\\*", "ca", flags::DEFAULT));
        assert!(!glob_match("\\*", "cb", flags::DEFAULT));
        assert!(!glob_match("\\*", "d", flags::DEFAULT));
        assert!(!glob_match("\\*", "dd", flags::DEFAULT));
        assert!(!glob_match("\\*", "de", flags::DEFAULT));

        assert!(!glob_match("a\\*", "*", flags::DEFAULT));
        assert!(!glob_match("a\\*", "**", flags::DEFAULT));
        assert!(!glob_match("a\\*", "\\*", flags::DEFAULT));
        assert!(!glob_match("a\\*", "a", flags::DEFAULT));
        assert!(!glob_match("a\\*", "a/*", flags::DEFAULT));
        assert!(!glob_match("a\\*", "abc", flags::DEFAULT));
        assert!(!glob_match("a\\*", "abd", flags::DEFAULT));
        assert!(!glob_match("a\\*", "abe", flags::DEFAULT));
        assert!(!glob_match("a\\*", "b", flags::DEFAULT));
        assert!(!glob_match("a\\*", "bb", flags::DEFAULT));
        assert!(!glob_match("a\\*", "bcd", flags::DEFAULT));
        assert!(!glob_match("a\\*", "bdir/", flags::DEFAULT));
        assert!(!glob_match("a\\*", "Beware", flags::DEFAULT));
        assert!(!glob_match("a\\*", "c", flags::DEFAULT));
        assert!(!glob_match("a\\*", "ca", flags::DEFAULT));
        assert!(!glob_match("a\\*", "cb", flags::DEFAULT));
        assert!(!glob_match("a\\*", "d", flags::DEFAULT));
        assert!(!glob_match("a\\*", "dd", flags::DEFAULT));
        assert!(!glob_match("a\\*", "de", flags::DEFAULT));

        assert!(glob_match("*q*", "aqa", flags::DEFAULT));
        assert!(glob_match("*q*", "aaqaa", flags::DEFAULT));
        assert!(!glob_match("*q*", "*", flags::DEFAULT));
        assert!(!glob_match("*q*", "**", flags::DEFAULT));
        assert!(!glob_match("*q*", "\\*", flags::DEFAULT));
        assert!(!glob_match("*q*", "a", flags::DEFAULT));
        assert!(!glob_match("*q*", "a/*", flags::DEFAULT));
        assert!(!glob_match("*q*", "abc", flags::DEFAULT));
        assert!(!glob_match("*q*", "abd", flags::DEFAULT));
        assert!(!glob_match("*q*", "abe", flags::DEFAULT));
        assert!(!glob_match("*q*", "b", flags::DEFAULT));
        assert!(!glob_match("*q*", "bb", flags::DEFAULT));
        assert!(!glob_match("*q*", "bcd", flags::DEFAULT));
        assert!(!glob_match("*q*", "bdir/", flags::DEFAULT));
        assert!(!glob_match("*q*", "Beware", flags::DEFAULT));
        assert!(!glob_match("*q*", "c", flags::DEFAULT));
        assert!(!glob_match("*q*", "ca", flags::DEFAULT));
        assert!(!glob_match("*q*", "cb", flags::DEFAULT));
        assert!(!glob_match("*q*", "d", flags::DEFAULT));
        assert!(!glob_match("*q*", "dd", flags::DEFAULT));
        assert!(!glob_match("*q*", "de", flags::DEFAULT));

        assert!(glob_match("\\**", "*", flags::DEFAULT));
        assert!(glob_match("\\**", "**", flags::DEFAULT));
        assert!(!glob_match("\\**", "\\*", flags::DEFAULT));
        assert!(!glob_match("\\**", "a", flags::DEFAULT));
        assert!(!glob_match("\\**", "a/*", flags::DEFAULT));
        assert!(!glob_match("\\**", "abc", flags::DEFAULT));
        assert!(!glob_match("\\**", "abd", flags::DEFAULT));
        assert!(!glob_match("\\**", "abe", flags::DEFAULT));
        assert!(!glob_match("\\**", "b", flags::DEFAULT));
        assert!(!glob_match("\\**", "bb", flags::DEFAULT));
        assert!(!glob_match("\\**", "bcd", flags::DEFAULT));
        assert!(!glob_match("\\**", "bdir/", flags::DEFAULT));
        assert!(!glob_match("\\**", "Beware", flags::DEFAULT));
        assert!(!glob_match("\\**", "c", flags::DEFAULT));
        assert!(!glob_match("\\**", "ca", flags::DEFAULT));
        assert!(!glob_match("\\**", "cb", flags::DEFAULT));
        assert!(!glob_match("\\**", "d", flags::DEFAULT));
        assert!(!glob_match("\\**", "dd", flags::DEFAULT));
        assert!(!glob_match("\\**", "de", flags::DEFAULT));
    }

    #[test]
    fn bash_classes() {
        assert!(!glob_match("a*[^c]", "*", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "**", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "\\*", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "a", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "a/*", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "abc", flags::DEFAULT));
        assert!(glob_match("a*[^c]", "abd", flags::DEFAULT));
        assert!(glob_match("a*[^c]", "abe", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "b", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "bb", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "bcd", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "bdir/", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "Beware", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "c", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "ca", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "cb", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "d", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "dd", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "de", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "baz", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "bzz", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "BZZ", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "beware", flags::DEFAULT));
        assert!(!glob_match("a*[^c]", "BewAre", flags::DEFAULT));

        assert!(glob_match("a[X-]b", "a-b", flags::DEFAULT));
        assert!(glob_match("a[X-]b", "aXb", flags::DEFAULT));

        assert!(!glob_match("[a-y]*[^c]", "*", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "a*", flags::DEFAULT));
        assert!(!glob_match("[a-y]*[^c]", "**", flags::DEFAULT));
        assert!(!glob_match("[a-y]*[^c]", "\\*", flags::DEFAULT));
        assert!(!glob_match("[a-y]*[^c]", "a", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "a123b", flags::DEFAULT));
        assert!(!glob_match("[a-y]*[^c]", "a123c", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "ab", flags::DEFAULT));
        assert!(!glob_match("[a-y]*[^c]", "a/*", flags::DEFAULT));
        assert!(!glob_match("[a-y]*[^c]", "abc", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "abd", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "abe", flags::DEFAULT));
        assert!(!glob_match("[a-y]*[^c]", "b", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "bd", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "bb", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "bcd", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "bdir/", flags::DEFAULT));
        assert!(!glob_match("[a-y]*[^c]", "Beware", flags::DEFAULT));
        assert!(!glob_match("[a-y]*[^c]", "c", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "ca", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "cb", flags::DEFAULT));
        assert!(!glob_match("[a-y]*[^c]", "d", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "dd", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "dd", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "dd", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "de", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "baz", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "bzz", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "bzz", flags::DEFAULT));
        // assert(!isMatch('bzz', '[a-y]*[^c]', { regex: true }));
        assert!(!glob_match("[a-y]*[^c]", "BZZ", flags::DEFAULT));
        assert!(glob_match("[a-y]*[^c]", "beware", flags::DEFAULT));
        assert!(!glob_match("[a-y]*[^c]", "BewAre", flags::DEFAULT));

        assert!(glob_match("a\\*b/*", "a*b/ooo", flags::DEFAULT));
        assert!(glob_match("a\\*?/*", "a*b/ooo", flags::DEFAULT));

        assert!(!glob_match("a[b]c", "*", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "**", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "\\*", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "a", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "a/*", flags::DEFAULT));
        assert!(glob_match("a[b]c", "abc", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "abd", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "abe", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "b", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "bb", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "bcd", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "bdir/", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "Beware", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "c", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "ca", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "cb", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "d", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "dd", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "de", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "baz", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "bzz", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "BZZ", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "beware", flags::DEFAULT));
        assert!(!glob_match("a[b]c", "BewAre", flags::DEFAULT));

        assert!(!glob_match("a[\"b\"]c", "*", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "**", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "\\*", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "a", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "a/*", flags::DEFAULT));
        assert!(glob_match("a[\"b\"]c", "abc", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "abd", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "abe", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "b", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "bb", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "bcd", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "bdir/", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "Beware", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "c", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "ca", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "cb", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "d", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "dd", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "de", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "baz", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "bzz", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "BZZ", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "beware", flags::DEFAULT));
        assert!(!glob_match("a[\"b\"]c", "BewAre", flags::DEFAULT));

        assert!(!glob_match("a[\\\\b]c", "*", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "**", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "\\*", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "a", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "a/*", flags::DEFAULT));
        assert!(glob_match("a[\\\\b]c", "abc", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "abd", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "abe", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "b", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "bb", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "bcd", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "bdir/", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "Beware", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "c", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "ca", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "cb", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "d", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "dd", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "de", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "baz", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "bzz", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "BZZ", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "beware", flags::DEFAULT));
        assert!(!glob_match("a[\\\\b]c", "BewAre", flags::DEFAULT));

        assert!(!glob_match("a[\\b]c", "*", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "**", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "\\*", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "a", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "a/*", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "abc", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "abd", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "abe", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "b", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "bb", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "bcd", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "bdir/", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "Beware", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "c", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "ca", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "cb", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "d", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "dd", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "de", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "baz", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "bzz", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "BZZ", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "beware", flags::DEFAULT));
        assert!(!glob_match("a[\\b]c", "BewAre", flags::DEFAULT));

        assert!(!glob_match("a[b-d]c", "*", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "**", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "\\*", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "a", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "a/*", flags::DEFAULT));
        assert!(glob_match("a[b-d]c", "abc", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "abd", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "abe", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "b", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "bb", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "bcd", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "bdir/", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "Beware", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "c", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "ca", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "cb", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "d", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "dd", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "de", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "baz", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "bzz", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "BZZ", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "beware", flags::DEFAULT));
        assert!(!glob_match("a[b-d]c", "BewAre", flags::DEFAULT));

        assert!(!glob_match("a?c", "*", flags::DEFAULT));
        assert!(!glob_match("a?c", "**", flags::DEFAULT));
        assert!(!glob_match("a?c", "\\*", flags::DEFAULT));
        assert!(!glob_match("a?c", "a", flags::DEFAULT));
        assert!(!glob_match("a?c", "a/*", flags::DEFAULT));
        assert!(glob_match("a?c", "abc", flags::DEFAULT));
        assert!(!glob_match("a?c", "abd", flags::DEFAULT));
        assert!(!glob_match("a?c", "abe", flags::DEFAULT));
        assert!(!glob_match("a?c", "b", flags::DEFAULT));
        assert!(!glob_match("a?c", "bb", flags::DEFAULT));
        assert!(!glob_match("a?c", "bcd", flags::DEFAULT));
        assert!(!glob_match("a?c", "bdir/", flags::DEFAULT));
        assert!(!glob_match("a?c", "Beware", flags::DEFAULT));
        assert!(!glob_match("a?c", "c", flags::DEFAULT));
        assert!(!glob_match("a?c", "ca", flags::DEFAULT));
        assert!(!glob_match("a?c", "cb", flags::DEFAULT));
        assert!(!glob_match("a?c", "d", flags::DEFAULT));
        assert!(!glob_match("a?c", "dd", flags::DEFAULT));
        assert!(!glob_match("a?c", "de", flags::DEFAULT));
        assert!(!glob_match("a?c", "baz", flags::DEFAULT));
        assert!(!glob_match("a?c", "bzz", flags::DEFAULT));
        assert!(!glob_match("a?c", "BZZ", flags::DEFAULT));
        assert!(!glob_match("a?c", "beware", flags::DEFAULT));
        assert!(!glob_match("a?c", "BewAre", flags::DEFAULT));

        assert!(glob_match(
            "*/man*/bash.*",
            "man/man1/bash.1",
            flags::DEFAULT
        ));

        assert!(glob_match("[^a-c]*", "*", flags::DEFAULT));
        assert!(glob_match("[^a-c]*", "**", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "a", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "a/*", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "abc", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "abd", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "abe", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "b", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "bb", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "bcd", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "bdir/", flags::DEFAULT));
        assert!(glob_match("[^a-c]*", "Beware", flags::DEFAULT));
        assert!(glob_match("[^a-c]*", "Beware", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "c", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "ca", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "cb", flags::DEFAULT));
        assert!(glob_match("[^a-c]*", "d", flags::DEFAULT));
        assert!(glob_match("[^a-c]*", "dd", flags::DEFAULT));
        assert!(glob_match("[^a-c]*", "de", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "baz", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "bzz", flags::DEFAULT));
        assert!(glob_match("[^a-c]*", "BZZ", flags::DEFAULT));
        assert!(!glob_match("[^a-c]*", "beware", flags::DEFAULT));
        assert!(glob_match("[^a-c]*", "BewAre", flags::DEFAULT));
    }

    #[test]
    fn bash_wildmatch() {
        assert!(!glob_match("a[]-]b", "aab", flags::DEFAULT));
        assert!(!glob_match("[ten]", "ten", flags::DEFAULT));
        assert!(glob_match("]", "]", flags::DEFAULT));
        assert!(glob_match("a[]-]b", "a-b", flags::DEFAULT));
        assert!(glob_match("a[]-]b", "a]b", flags::DEFAULT));
        assert!(glob_match("a[]]b", "a]b", flags::DEFAULT));
        assert!(glob_match("a[\\]a\\-]b", "aab", flags::DEFAULT));
        assert!(glob_match("t[a-g]n", "ten", flags::DEFAULT));
        assert!(glob_match("t[^a-g]n", "ton", flags::DEFAULT));
    }

    #[test]
    fn bash_slashmatch() {
        // assert!(!glob_match("f[^eiu][^eiu][^eiu][^eiu][^eiu]r", "foo/bar", flags::DEFAULT));
        assert!(glob_match("foo[/]bar", "foo/bar", flags::DEFAULT));
        assert!(glob_match(
            "f[^eiu][^eiu][^eiu][^eiu][^eiu]r",
            "foo-bar",
            flags::DEFAULT
        ));
    }

    #[test]
    fn bash_extra_stars() {
        assert!(!glob_match("a**c", "bbc", flags::DEFAULT));
        assert!(glob_match("a**c", "abc", flags::DEFAULT));
        assert!(!glob_match("a**c", "bbd", flags::DEFAULT));

        assert!(!glob_match("a***c", "bbc", flags::DEFAULT));
        assert!(glob_match("a***c", "abc", flags::DEFAULT));
        assert!(!glob_match("a***c", "bbd", flags::DEFAULT));

        assert!(!glob_match("a*****?c", "bbc", flags::DEFAULT));
        assert!(glob_match("a*****?c", "abc", flags::DEFAULT));
        assert!(!glob_match("a*****?c", "bbc", flags::DEFAULT));

        assert!(glob_match("?*****??", "bbc", flags::DEFAULT));
        assert!(glob_match("?*****??", "abc", flags::DEFAULT));

        assert!(glob_match("*****??", "bbc", flags::DEFAULT));
        assert!(glob_match("*****??", "abc", flags::DEFAULT));

        assert!(glob_match("?*****?c", "bbc", flags::DEFAULT));
        assert!(glob_match("?*****?c", "abc", flags::DEFAULT));

        assert!(glob_match("?***?****c", "bbc", flags::DEFAULT));
        assert!(glob_match("?***?****c", "abc", flags::DEFAULT));
        assert!(!glob_match("?***?****c", "bbd", flags::DEFAULT));

        assert!(glob_match("?***?****?", "bbc", flags::DEFAULT));
        assert!(glob_match("?***?****?", "abc", flags::DEFAULT));

        assert!(glob_match("?***?****", "bbc", flags::DEFAULT));
        assert!(glob_match("?***?****", "abc", flags::DEFAULT));

        assert!(glob_match("*******c", "bbc", flags::DEFAULT));
        assert!(glob_match("*******c", "abc", flags::DEFAULT));

        assert!(glob_match("*******?", "bbc", flags::DEFAULT));
        assert!(glob_match("*******?", "abc", flags::DEFAULT));

        assert!(glob_match("a*cd**?**??k", "abcdecdhjk", flags::DEFAULT));
        assert!(glob_match("a**?**cd**?**??k", "abcdecdhjk", flags::DEFAULT));
        assert!(glob_match(
            "a**?**cd**?**??k***",
            "abcdecdhjk",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a**?**cd**?**??***k",
            "abcdecdhjk",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a**?**cd**?**??***k**",
            "abcdecdhjk",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a****c**?**??*****",
            "abcdecdhjk",
            flags::DEFAULT
        ));
    }

    #[test]
    fn stars() {
        assert!(!glob_match("*.js", "a/b/c/z.js", flags::DEFAULT));
        assert!(!glob_match("*.js", "a/b/z.js", flags::DEFAULT));
        assert!(!glob_match("*.js", "a/z.js", flags::DEFAULT));
        assert!(glob_match("*.js", "z.js", flags::DEFAULT));

        // assert!(!glob_match("*/*", "a/.ab", flags::DEFAULT));
        // assert!(!glob_match("*", ".ab", flags::DEFAULT));

        assert!(glob_match("z*.js", "z.js", flags::DEFAULT));
        assert!(glob_match("*/*", "a/z", flags::DEFAULT));
        assert!(glob_match("*/z*.js", "a/z.js", flags::DEFAULT));
        assert!(glob_match("a/z*.js", "a/z.js", flags::DEFAULT));

        assert!(glob_match("*", "ab", flags::DEFAULT));
        assert!(glob_match("*", "abc", flags::DEFAULT));

        assert!(!glob_match("f*", "bar", flags::DEFAULT));
        assert!(!glob_match("*r", "foo", flags::DEFAULT));
        assert!(!glob_match("b*", "foo", flags::DEFAULT));
        assert!(!glob_match("*", "foo/bar", flags::DEFAULT));
        assert!(glob_match("*c", "abc", flags::DEFAULT));
        assert!(glob_match("a*", "abc", flags::DEFAULT));
        assert!(glob_match("a*c", "abc", flags::DEFAULT));
        assert!(glob_match("*r", "bar", flags::DEFAULT));
        assert!(glob_match("b*", "bar", flags::DEFAULT));
        assert!(glob_match("f*", "foo", flags::DEFAULT));

        assert!(glob_match("*abc*", "one abc two", flags::DEFAULT));
        assert!(glob_match("a*b", "a         b", flags::DEFAULT));

        assert!(!glob_match("*a*", "foo", flags::DEFAULT));
        assert!(glob_match("*a*", "bar", flags::DEFAULT));
        assert!(glob_match("*abc*", "oneabctwo", flags::DEFAULT));
        assert!(!glob_match("*-bc-*", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("*-*.*-*", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("*-b*c-*", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("*-b.c-*", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("*.*", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("*.*-*", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("*.*-d", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("*.c-*", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("*b.*d", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("a*.c*", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("a-*.*-d", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("*.*", "a.b", flags::DEFAULT));
        assert!(glob_match("*.b", "a.b", flags::DEFAULT));
        assert!(glob_match("a.*", "a.b", flags::DEFAULT));
        assert!(glob_match("a.b", "a.b", flags::DEFAULT));

        assert!(!glob_match("**-bc-**", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("**-**.**-**", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("**-b**c-**", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("**-b.c-**", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("**.**", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("**.**-**", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("**.**-d", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("**.c-**", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("**b.**d", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("a**.c**", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("a-**.**-d", "a-b.c-d", flags::DEFAULT));
        assert!(glob_match("**.**", "a.b", flags::DEFAULT));
        assert!(glob_match("**.b", "a.b", flags::DEFAULT));
        assert!(glob_match("a.**", "a.b", flags::DEFAULT));
        assert!(glob_match("a.b", "a.b", flags::DEFAULT));

        assert!(glob_match("*/*", "/ab", flags::DEFAULT));
        assert!(glob_match(".", ".", flags::DEFAULT));
        assert!(!glob_match("a/", "a/.b", flags::DEFAULT));
        assert!(glob_match("/*", "/ab", flags::DEFAULT));
        assert!(glob_match("/??", "/ab", flags::DEFAULT));
        assert!(glob_match("/?b", "/ab", flags::DEFAULT));
        assert!(glob_match("/*", "/cd", flags::DEFAULT));
        assert!(glob_match("a", "a", flags::DEFAULT));
        assert!(glob_match("a/.*", "a/.b", flags::DEFAULT));
        assert!(glob_match("?/?", "a/b", flags::DEFAULT));
        assert!(glob_match(
            "a/**/j/**/z/*.md",
            "a/b/c/d/e/j/n/p/o/z/c.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/**/z/*.md",
            "a/b/c/d/e/z/c.md",
            flags::DEFAULT
        ));
        assert!(glob_match("a/b/c/*.md", "a/b/c/xyz.md", flags::DEFAULT));
        assert!(glob_match("a/b/c/*.md", "a/b/c/xyz.md", flags::DEFAULT));
        assert!(glob_match("a/*/z/.a", "a/b/z/.a", flags::DEFAULT));
        assert!(!glob_match("bz", "a/b/z/.a", flags::DEFAULT));
        assert!(glob_match(
            "a/**/c/*.md",
            "a/bb.bb/aa/b.b/aa/c/xyz.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/**/c/*.md",
            "a/bb.bb/aa/bb/aa/c/xyz.md",
            flags::DEFAULT
        ));
        assert!(glob_match("a/*/c/*.md", "a/bb.bb/c/xyz.md", flags::DEFAULT));
        assert!(glob_match("a/*/c/*.md", "a/bb/c/xyz.md", flags::DEFAULT));
        assert!(glob_match("a/*/c/*.md", "a/bbbb/c/xyz.md", flags::DEFAULT));
        assert!(glob_match("*", "aaa", flags::DEFAULT));
        assert!(glob_match("*", "ab", flags::DEFAULT));
        assert!(glob_match("ab", "ab", flags::DEFAULT));

        assert!(!glob_match("*/*/*", "aaa", flags::DEFAULT));
        assert!(!glob_match("*/*/*", "aaa/bb/aa/rr", flags::DEFAULT));
        assert!(!glob_match("aaa*", "aaa/bba/ccc", flags::DEFAULT));
        // assert!(!glob_match("aaa**", "aaa/bba/ccc", flags::DEFAULT));
        assert!(!glob_match("aaa/*", "aaa/bba/ccc", flags::DEFAULT));
        assert!(!glob_match("aaa/*ccc", "aaa/bba/ccc", flags::DEFAULT));
        assert!(!glob_match("aaa/*z", "aaa/bba/ccc", flags::DEFAULT));
        assert!(!glob_match("*/*/*", "aaa/bbb", flags::DEFAULT));
        assert!(!glob_match("*/*jk*/*i", "ab/zzz/ejkl/hi", flags::DEFAULT));
        assert!(glob_match("*/*/*", "aaa/bba/ccc", flags::DEFAULT));
        assert!(glob_match("aaa/**", "aaa/bba/ccc", flags::DEFAULT));
        assert!(glob_match("aaa/*", "aaa/bbb", flags::DEFAULT));
        assert!(glob_match("*/*z*/*/*i", "ab/zzz/ejkl/hi", flags::DEFAULT));
        assert!(glob_match("*j*i", "abzzzejklhi", flags::DEFAULT));

        assert!(glob_match("*", "a", flags::DEFAULT));
        assert!(glob_match("*", "b", flags::DEFAULT));
        assert!(!glob_match("*", "a/a", flags::DEFAULT));
        assert!(!glob_match("*", "a/a/a", flags::DEFAULT));
        assert!(!glob_match("*", "a/a/b", flags::DEFAULT));
        assert!(!glob_match("*", "a/a/a/a", flags::DEFAULT));
        assert!(!glob_match("*", "a/a/a/a/a", flags::DEFAULT));

        assert!(!glob_match("*/*", "a", flags::DEFAULT));
        assert!(glob_match("*/*", "a/a", flags::DEFAULT));
        assert!(!glob_match("*/*", "a/a/a", flags::DEFAULT));

        assert!(!glob_match("*/*/*", "a", flags::DEFAULT));
        assert!(!glob_match("*/*/*", "a/a", flags::DEFAULT));
        assert!(glob_match("*/*/*", "a/a/a", flags::DEFAULT));
        assert!(!glob_match("*/*/*", "a/a/a/a", flags::DEFAULT));

        assert!(!glob_match("*/*/*/*", "a", flags::DEFAULT));
        assert!(!glob_match("*/*/*/*", "a/a", flags::DEFAULT));
        assert!(!glob_match("*/*/*/*", "a/a/a", flags::DEFAULT));
        assert!(glob_match("*/*/*/*", "a/a/a/a", flags::DEFAULT));
        assert!(!glob_match("*/*/*/*", "a/a/a/a/a", flags::DEFAULT));

        assert!(!glob_match("*/*/*/*/*", "a", flags::DEFAULT));
        assert!(!glob_match("*/*/*/*/*", "a/a", flags::DEFAULT));
        assert!(!glob_match("*/*/*/*/*", "a/a/a", flags::DEFAULT));
        assert!(!glob_match("*/*/*/*/*", "a/a/b", flags::DEFAULT));
        assert!(!glob_match("*/*/*/*/*", "a/a/a/a", flags::DEFAULT));
        assert!(glob_match("*/*/*/*/*", "a/a/a/a/a", flags::DEFAULT));
        assert!(!glob_match("*/*/*/*/*", "a/a/a/a/a/a", flags::DEFAULT));

        assert!(!glob_match("a/*", "a", flags::DEFAULT));
        assert!(glob_match("a/*", "a/a", flags::DEFAULT));
        assert!(!glob_match("a/*", "a/a/a", flags::DEFAULT));
        assert!(!glob_match("a/*", "a/a/a/a", flags::DEFAULT));
        assert!(!glob_match("a/*", "a/a/a/a/a", flags::DEFAULT));

        assert!(!glob_match("a/*/*", "a", flags::DEFAULT));
        assert!(!glob_match("a/*/*", "a/a", flags::DEFAULT));
        assert!(glob_match("a/*/*", "a/a/a", flags::DEFAULT));
        assert!(!glob_match("a/*/*", "b/a/a", flags::DEFAULT));
        assert!(!glob_match("a/*/*", "a/a/a/a", flags::DEFAULT));
        assert!(!glob_match("a/*/*", "a/a/a/a/a", flags::DEFAULT));

        assert!(!glob_match("a/*/*/*", "a", flags::DEFAULT));
        assert!(!glob_match("a/*/*/*", "a/a", flags::DEFAULT));
        assert!(!glob_match("a/*/*/*", "a/a/a", flags::DEFAULT));
        assert!(glob_match("a/*/*/*", "a/a/a/a", flags::DEFAULT));
        assert!(!glob_match("a/*/*/*", "a/a/a/a/a", flags::DEFAULT));

        assert!(!glob_match("a/*/*/*/*", "a", flags::DEFAULT));
        assert!(!glob_match("a/*/*/*/*", "a/a", flags::DEFAULT));
        assert!(!glob_match("a/*/*/*/*", "a/a/a", flags::DEFAULT));
        assert!(!glob_match("a/*/*/*/*", "a/a/b", flags::DEFAULT));
        assert!(!glob_match("a/*/*/*/*", "a/a/a/a", flags::DEFAULT));
        assert!(glob_match("a/*/*/*/*", "a/a/a/a/a", flags::DEFAULT));

        assert!(!glob_match("a/*/a", "a", flags::DEFAULT));
        assert!(!glob_match("a/*/a", "a/a", flags::DEFAULT));
        assert!(glob_match("a/*/a", "a/a/a", flags::DEFAULT));
        assert!(!glob_match("a/*/a", "a/a/b", flags::DEFAULT));
        assert!(!glob_match("a/*/a", "a/a/a/a", flags::DEFAULT));
        assert!(!glob_match("a/*/a", "a/a/a/a/a", flags::DEFAULT));

        assert!(!glob_match("a/*/b", "a", flags::DEFAULT));
        assert!(!glob_match("a/*/b", "a/a", flags::DEFAULT));
        assert!(!glob_match("a/*/b", "a/a/a", flags::DEFAULT));
        assert!(glob_match("a/*/b", "a/a/b", flags::DEFAULT));
        assert!(!glob_match("a/*/b", "a/a/a/a", flags::DEFAULT));
        assert!(!glob_match("a/*/b", "a/a/a/a/a", flags::DEFAULT));

        assert!(!glob_match("*/**/a", "a", flags::DEFAULT));
        assert!(!glob_match("*/**/a", "a/a/b", flags::DEFAULT));
        assert!(glob_match("*/**/a", "a/a", flags::DEFAULT));
        assert!(glob_match("*/**/a", "a/a/a", flags::DEFAULT));
        assert!(glob_match("*/**/a", "a/a/a/a", flags::DEFAULT));
        assert!(glob_match("*/**/a", "a/a/a/a/a", flags::DEFAULT));

        assert!(!glob_match("*/", "a", flags::DEFAULT));
        assert!(!glob_match("*/*", "a", flags::DEFAULT));
        assert!(!glob_match("a/*", "a", flags::DEFAULT));
        // assert!(!glob_match("*/*", "a/", flags::DEFAULT));
        // assert!(!glob_match("a/*", "a/", flags::DEFAULT));
        assert!(!glob_match("*", "a/a", flags::DEFAULT));
        assert!(!glob_match("*/", "a/a", flags::DEFAULT));
        assert!(!glob_match("*/", "a/x/y", flags::DEFAULT));
        assert!(!glob_match("*/*", "a/x/y", flags::DEFAULT));
        assert!(!glob_match("a/*", "a/x/y", flags::DEFAULT));
        // assert!(glob_match("*", "a/", flags::DEFAULT));
        assert!(glob_match("*", "a", flags::DEFAULT));
        assert!(glob_match("*/", "a/", flags::DEFAULT));
        assert!(glob_match("*{,/}", "a/", flags::DEFAULT));
        assert!(glob_match("*/*", "a/a", flags::DEFAULT));
        assert!(glob_match("a/*", "a/a", flags::DEFAULT));

        assert!(!glob_match("a/**/*.txt", "a.txt", flags::DEFAULT));
        assert!(glob_match("a/**/*.txt", "a/x/y.txt", flags::DEFAULT));
        assert!(!glob_match("a/**/*.txt", "a/x/y/z", flags::DEFAULT));

        assert!(!glob_match("a/*.txt", "a.txt", flags::DEFAULT));
        assert!(glob_match("a/*.txt", "a/b.txt", flags::DEFAULT));
        assert!(!glob_match("a/*.txt", "a/x/y.txt", flags::DEFAULT));
        assert!(!glob_match("a/*.txt", "a/x/y/z", flags::DEFAULT));

        assert!(glob_match("a*.txt", "a.txt", flags::DEFAULT));
        assert!(!glob_match("a*.txt", "a/b.txt", flags::DEFAULT));
        assert!(!glob_match("a*.txt", "a/x/y.txt", flags::DEFAULT));
        assert!(!glob_match("a*.txt", "a/x/y/z", flags::DEFAULT));

        assert!(glob_match("*.txt", "a.txt", flags::DEFAULT));
        assert!(!glob_match("*.txt", "a/b.txt", flags::DEFAULT));
        assert!(!glob_match("*.txt", "a/x/y.txt", flags::DEFAULT));
        assert!(!glob_match("*.txt", "a/x/y/z", flags::DEFAULT));

        assert!(!glob_match("a*", "a/b", flags::DEFAULT));
        assert!(!glob_match("a/**/b", "a/a/bb", flags::DEFAULT));
        assert!(!glob_match("a/**/b", "a/bb", flags::DEFAULT));

        assert!(!glob_match("*/**", "foo", flags::DEFAULT));
        assert!(!glob_match("**/", "foo/bar", flags::DEFAULT));
        assert!(!glob_match("**/*/", "foo/bar", flags::DEFAULT));
        assert!(!glob_match("*/*/", "foo/bar", flags::DEFAULT));

        assert!(glob_match("**/..", "/home/foo/..", flags::DEFAULT));
        assert!(glob_match("**/a", "a", flags::DEFAULT));
        assert!(glob_match("**", "a/a", flags::DEFAULT));
        assert!(glob_match("a/**", "a/a", flags::DEFAULT));
        assert!(glob_match("a/**", "a/", flags::DEFAULT));
        // assert!(glob_match("a/**", "a", flags::DEFAULT));
        assert!(!glob_match("**/", "a/a", flags::DEFAULT));
        // assert!(glob_match("**/a/**", "a", flags::DEFAULT));
        // assert!(glob_match("a/**", "a", flags::DEFAULT));
        assert!(!glob_match("**/", "a/a", flags::DEFAULT));
        assert!(glob_match("*/**/a", "a/a", flags::DEFAULT));
        // assert!(glob_match("a/**", "a", flags::DEFAULT));
        assert!(glob_match("*/**", "foo/", flags::DEFAULT));
        assert!(glob_match("**/*", "foo/bar", flags::DEFAULT));
        assert!(glob_match("*/*", "foo/bar", flags::DEFAULT));
        assert!(glob_match("*/**", "foo/bar", flags::DEFAULT));
        assert!(glob_match("**/", "foo/bar/", flags::DEFAULT));
        // assert!(glob_match("**/*", "foo/bar/", flags::DEFAULT));
        assert!(glob_match("**/*/", "foo/bar/", flags::DEFAULT));
        assert!(glob_match("*/**", "foo/bar/", flags::DEFAULT));
        assert!(glob_match("*/*/", "foo/bar/", flags::DEFAULT));

        assert!(!glob_match("*/foo", "bar/baz/foo", flags::DEFAULT));
        assert!(!glob_match("**/bar/*", "deep/foo/bar", flags::DEFAULT));
        assert!(!glob_match(
            "*/bar/**",
            "deep/foo/bar/baz/x",
            flags::DEFAULT
        ));
        assert!(!glob_match("/*", "ef", flags::DEFAULT));
        assert!(!glob_match("foo?bar", "foo/bar", flags::DEFAULT));
        assert!(!glob_match("**/bar*", "foo/bar/baz", flags::DEFAULT));
        // assert!(!glob_match("**/bar**", "foo/bar/baz", flags::DEFAULT));
        assert!(!glob_match("foo**bar", "foo/baz/bar", flags::DEFAULT));
        assert!(!glob_match("foo*bar", "foo/baz/bar", flags::DEFAULT));
        // assert!(glob_match("foo/**", "foo", flags::DEFAULT));
        assert!(glob_match("/*", "/ab", flags::DEFAULT));
        assert!(glob_match("/*", "/cd", flags::DEFAULT));
        assert!(glob_match("/*", "/ef", flags::DEFAULT));
        assert!(glob_match(
            "a/**/j/**/z/*.md",
            "a/b/j/c/z/x.md",
            flags::DEFAULT
        ));
        assert!(glob_match("a/**/j/**/z/*.md", "a/j/z/x.md", flags::DEFAULT));

        assert!(glob_match("**/foo", "bar/baz/foo", flags::DEFAULT));
        assert!(glob_match("**/bar/*", "deep/foo/bar/baz", flags::DEFAULT));
        assert!(glob_match("**/bar/**", "deep/foo/bar/baz/", flags::DEFAULT));
        assert!(glob_match(
            "**/bar/*/*",
            "deep/foo/bar/baz/x",
            flags::DEFAULT
        ));
        assert!(glob_match("foo/**/**/bar", "foo/b/a/z/bar", flags::DEFAULT));
        assert!(glob_match("foo/**/bar", "foo/b/a/z/bar", flags::DEFAULT));
        assert!(glob_match("foo/**/**/bar", "foo/bar", flags::DEFAULT));
        assert!(glob_match("foo/**/bar", "foo/bar", flags::DEFAULT));
        assert!(glob_match("*/bar/**", "foo/bar/baz/x", flags::DEFAULT));
        assert!(glob_match("foo/**/**/bar", "foo/baz/bar", flags::DEFAULT));
        assert!(glob_match("foo/**/bar", "foo/baz/bar", flags::DEFAULT));
        assert!(glob_match("**/foo", "XXX/foo", flags::DEFAULT));
    }

    #[test]
    fn globstars() {
        assert!(glob_match("**/*.js", "a/b/c/d.js", flags::DEFAULT));
        assert!(glob_match("**/*.js", "a/b/c.js", flags::DEFAULT));
        assert!(glob_match("**/*.js", "a/b.js", flags::DEFAULT));
        assert!(glob_match("a/b/**/*.js", "a/b/c/d/e/f.js", flags::DEFAULT));
        assert!(glob_match("a/b/**/*.js", "a/b/c/d/e.js", flags::DEFAULT));
        assert!(glob_match("a/b/c/**/*.js", "a/b/c/d.js", flags::DEFAULT));
        assert!(glob_match("a/b/**/*.js", "a/b/c/d.js", flags::DEFAULT));
        assert!(glob_match("a/b/**/*.js", "a/b/d.js", flags::DEFAULT));
        assert!(!glob_match("a/b/**/*.js", "a/d.js", flags::DEFAULT));
        assert!(!glob_match("a/b/**/*.js", "d.js", flags::DEFAULT));

        assert!(!glob_match("**c", "a/b/c", flags::DEFAULT));
        assert!(!glob_match("a/**c", "a/b/c", flags::DEFAULT));
        assert!(!glob_match("a/**z", "a/b/c", flags::DEFAULT));
        assert!(!glob_match("a/**b**/c", "a/b/c/b/c", flags::DEFAULT));
        assert!(!glob_match("a/b/c**/*.js", "a/b/c/d/e.js", flags::DEFAULT));
        assert!(glob_match("a/**/b/**/c", "a/b/c/b/c", flags::DEFAULT));
        assert!(glob_match("a/**b**/c", "a/aba/c", flags::DEFAULT));
        assert!(glob_match("a/**b**/c", "a/b/c", flags::DEFAULT));
        assert!(glob_match("a/b/c**/*.js", "a/b/c/d.js", flags::DEFAULT));

        assert!(!glob_match("a/**/*", "a", flags::DEFAULT));
        assert!(!glob_match("a/**/**/*", "a", flags::DEFAULT));
        assert!(!glob_match("a/**/**/**/*", "a", flags::DEFAULT));
        assert!(!glob_match("**/a", "a/", flags::DEFAULT));
        assert!(!glob_match("a/**/*", "a/", flags::DEFAULT));
        assert!(!glob_match("a/**/**/*", "a/", flags::DEFAULT));
        assert!(!glob_match("a/**/**/**/*", "a/", flags::DEFAULT));
        assert!(!glob_match("**/a", "a/b", flags::DEFAULT));
        assert!(!glob_match(
            "a/**/j/**/z/*.md",
            "a/b/c/j/e/z/c.txt",
            flags::DEFAULT
        ));
        assert!(!glob_match("a/**/b", "a/bb", flags::DEFAULT));
        assert!(!glob_match("**/a", "a/c", flags::DEFAULT));
        assert!(!glob_match("**/a", "a/b", flags::DEFAULT));
        assert!(!glob_match("**/a", "a/x/y", flags::DEFAULT));
        assert!(!glob_match("**/a", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("**", "a", flags::DEFAULT));
        assert!(glob_match("**/a", "a", flags::DEFAULT));
        // assert!(glob_match("a/**", "a", flags::DEFAULT));
        assert!(glob_match("**", "a/", flags::DEFAULT));
        assert!(glob_match("**/a/**", "a/", flags::DEFAULT));
        assert!(glob_match("a/**", "a/", flags::DEFAULT));
        assert!(glob_match("a/**/**", "a/", flags::DEFAULT));
        assert!(glob_match("**/a", "a/a", flags::DEFAULT));
        assert!(glob_match("**", "a/b", flags::DEFAULT));
        assert!(glob_match("*/*", "a/b", flags::DEFAULT));
        assert!(glob_match("a/**", "a/b", flags::DEFAULT));
        assert!(glob_match("a/**/*", "a/b", flags::DEFAULT));
        assert!(glob_match("a/**/**/*", "a/b", flags::DEFAULT));
        assert!(glob_match("a/**/**/**/*", "a/b", flags::DEFAULT));
        assert!(glob_match("a/**/b", "a/b", flags::DEFAULT));
        assert!(glob_match("**", "a/b/c", flags::DEFAULT));
        assert!(glob_match("**/*", "a/b/c", flags::DEFAULT));
        assert!(glob_match("**/**", "a/b/c", flags::DEFAULT));
        assert!(glob_match("*/**", "a/b/c", flags::DEFAULT));
        assert!(glob_match("a/**", "a/b/c", flags::DEFAULT));
        assert!(glob_match("a/**/*", "a/b/c", flags::DEFAULT));
        assert!(glob_match("a/**/**/*", "a/b/c", flags::DEFAULT));
        assert!(glob_match("a/**/**/**/*", "a/b/c", flags::DEFAULT));
        assert!(glob_match("**", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("a/**", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("a/**/*", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("a/**/**/*", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("a/**/**/**/*", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("a/b/**/c/**/*.*", "a/b/c/d.e", flags::DEFAULT));
        assert!(glob_match(
            "a/**/f/*.md",
            "a/b/c/d/e/f/g.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/**/f/**/k/*.md",
            "a/b/c/d/e/f/g/h/i/j/k/l.md",
            flags::DEFAULT
        ));
        assert!(glob_match("a/b/c/*.md", "a/b/c/def.md", flags::DEFAULT));
        assert!(glob_match("a/*/c/*.md", "a/bb.bb/c/ddd.md", flags::DEFAULT));
        assert!(glob_match(
            "a/**/f/*.md",
            "a/bb.bb/cc/d.d/ee/f/ggg.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/**/f/*.md",
            "a/bb.bb/cc/dd/ee/f/ggg.md",
            flags::DEFAULT
        ));
        assert!(glob_match("a/*/c/*.md", "a/bb/c/ddd.md", flags::DEFAULT));
        assert!(glob_match("a/*/c/*.md", "a/bbbb/c/ddd.md", flags::DEFAULT));

        assert!(glob_match(
            "foo/bar/**/one/**/*.*",
            "foo/bar/baz/one/image.png",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "foo/bar/**/one/**/*.*",
            "foo/bar/baz/one/two/image.png",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "foo/bar/**/one/**/*.*",
            "foo/bar/baz/one/two/three/image.png",
            flags::DEFAULT
        ));
        assert!(!glob_match("a/b/**/f", "a/b/c/d/", flags::DEFAULT));
        // assert!(glob_match("a/**", "a", flags::DEFAULT));
        assert!(glob_match("**", "a", flags::DEFAULT));
        // assert!(glob_match("a{,/**}", "a", flags::DEFAULT));
        assert!(glob_match("**", "a/", flags::DEFAULT));
        assert!(glob_match("a/**", "a/", flags::DEFAULT));
        assert!(glob_match("**", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("**", "a/b/c/d/", flags::DEFAULT));
        assert!(glob_match("**/**", "a/b/c/d/", flags::DEFAULT));
        assert!(glob_match("**/b/**", "a/b/c/d/", flags::DEFAULT));
        assert!(glob_match("a/b/**", "a/b/c/d/", flags::DEFAULT));
        assert!(glob_match("a/b/**/", "a/b/c/d/", flags::DEFAULT));
        assert!(glob_match("a/b/**/c/**/", "a/b/c/d/", flags::DEFAULT));
        assert!(glob_match("a/b/**/c/**/d/", "a/b/c/d/", flags::DEFAULT));
        assert!(glob_match("a/b/**/**/*.*", "a/b/c/d/e.f", flags::DEFAULT));
        assert!(glob_match("a/b/**/*.*", "a/b/c/d/e.f", flags::DEFAULT));
        assert!(glob_match(
            "a/b/**/c/**/d/*.*",
            "a/b/c/d/e.f",
            flags::DEFAULT
        ));
        assert!(glob_match("a/b/**/d/**/*.*", "a/b/c/d/e.f", flags::DEFAULT));
        assert!(glob_match(
            "a/b/**/d/**/*.*",
            "a/b/c/d/g/e.f",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/b/**/d/**/*.*",
            "a/b/c/d/g/g/e.f",
            flags::DEFAULT
        ));
        assert!(glob_match("a/b-*/**/z.js", "a/b-c/z.js", flags::DEFAULT));
        assert!(glob_match(
            "a/b-*/**/z.js",
            "a/b-c/d/e/z.js",
            flags::DEFAULT
        ));

        assert!(glob_match("*/*", "a/b", flags::DEFAULT));
        assert!(glob_match("a/b/c/*.md", "a/b/c/xyz.md", flags::DEFAULT));
        assert!(glob_match("a/*/c/*.md", "a/bb.bb/c/xyz.md", flags::DEFAULT));
        assert!(glob_match("a/*/c/*.md", "a/bb/c/xyz.md", flags::DEFAULT));
        assert!(glob_match("a/*/c/*.md", "a/bbbb/c/xyz.md", flags::DEFAULT));

        assert!(glob_match("**/*", "a/b/c", flags::DEFAULT));
        assert!(glob_match("**/**", "a/b/c", flags::DEFAULT));
        assert!(glob_match("*/**", "a/b/c", flags::DEFAULT));
        assert!(glob_match(
            "a/**/j/**/z/*.md",
            "a/b/c/d/e/j/n/p/o/z/c.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/**/z/*.md",
            "a/b/c/d/e/z/c.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/**/c/*.md",
            "a/bb.bb/aa/b.b/aa/c/xyz.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/**/c/*.md",
            "a/bb.bb/aa/bb/aa/c/xyz.md",
            flags::DEFAULT
        ));
        assert!(!glob_match(
            "a/**/j/**/z/*.md",
            "a/b/c/j/e/z/c.txt",
            flags::DEFAULT
        ));
        assert!(!glob_match(
            "a/b/**/c{d,e}/**/xyz.md",
            "a/b/c/xyz.md",
            flags::DEFAULT
        ));
        assert!(!glob_match(
            "a/b/**/c{d,e}/**/xyz.md",
            "a/b/d/xyz.md",
            flags::DEFAULT
        ));
        assert!(!glob_match("a/**/", "a/b", flags::DEFAULT));
        // assert!(!glob_match("**/*", "a/b/.js/c.txt", flags::DEFAULT));
        assert!(!glob_match("a/**/", "a/b/c/d", flags::DEFAULT));
        assert!(!glob_match("a/**/", "a/bb", flags::DEFAULT));
        assert!(!glob_match("a/**/", "a/cb", flags::DEFAULT));
        assert!(glob_match("/**", "/a/b", flags::DEFAULT));
        assert!(glob_match("**/*", "a.b", flags::DEFAULT));
        assert!(glob_match("**/*", "a.js", flags::DEFAULT));
        assert!(glob_match("**/*.js", "a.js", flags::DEFAULT));
        // assert!(glob_match("a/**/", "a/", flags::DEFAULT));
        assert!(glob_match("**/*.js", "a/a.js", flags::DEFAULT));
        assert!(glob_match("**/*.js", "a/a/b.js", flags::DEFAULT));
        assert!(glob_match("a/**/b", "a/b", flags::DEFAULT));
        assert!(glob_match("a/**b", "a/b", flags::DEFAULT));
        assert!(glob_match("**/*.md", "a/b.md", flags::DEFAULT));
        assert!(glob_match("**/*", "a/b/c.js", flags::DEFAULT));
        assert!(glob_match("**/*", "a/b/c.txt", flags::DEFAULT));
        assert!(glob_match("a/**/", "a/b/c/d/", flags::DEFAULT));
        assert!(glob_match("**/*", "a/b/c/d/a.js", flags::DEFAULT));
        assert!(glob_match("a/b/**/*.js", "a/b/c/z.js", flags::DEFAULT));
        assert!(glob_match("a/b/**/*.js", "a/b/z.js", flags::DEFAULT));
        assert!(glob_match("**/*", "ab", flags::DEFAULT));
        assert!(glob_match("**/*", "ab/c", flags::DEFAULT));
        assert!(glob_match("**/*", "ab/c/d", flags::DEFAULT));
        assert!(glob_match("**/*", "abc.js", flags::DEFAULT));

        assert!(!glob_match("**/", "a", flags::DEFAULT));
        assert!(!glob_match("**/a/*", "a", flags::DEFAULT));
        assert!(!glob_match("**/a/*/*", "a", flags::DEFAULT));
        assert!(!glob_match("*/a/**", "a", flags::DEFAULT));
        assert!(!glob_match("a/**/*", "a", flags::DEFAULT));
        assert!(!glob_match("a/**/**/*", "a", flags::DEFAULT));
        assert!(!glob_match("**/", "a/b", flags::DEFAULT));
        assert!(!glob_match("**/b/*", "a/b", flags::DEFAULT));
        assert!(!glob_match("**/b/*/*", "a/b", flags::DEFAULT));
        assert!(!glob_match("b/**", "a/b", flags::DEFAULT));
        assert!(!glob_match("**/", "a/b/c", flags::DEFAULT));
        assert!(!glob_match("**/**/b", "a/b/c", flags::DEFAULT));
        assert!(!glob_match("**/b", "a/b/c", flags::DEFAULT));
        assert!(!glob_match("**/b/*/*", "a/b/c", flags::DEFAULT));
        assert!(!glob_match("b/**", "a/b/c", flags::DEFAULT));
        assert!(!glob_match("**/", "a/b/c/d", flags::DEFAULT));
        assert!(!glob_match("**/d/*", "a/b/c/d", flags::DEFAULT));
        assert!(!glob_match("b/**", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("**", "a", flags::DEFAULT));
        assert!(glob_match("**/**", "a", flags::DEFAULT));
        assert!(glob_match("**/**/*", "a", flags::DEFAULT));
        assert!(glob_match("**/**/a", "a", flags::DEFAULT));
        assert!(glob_match("**/a", "a", flags::DEFAULT));
        // assert!(glob_match("**/a/**", "a", flags::DEFAULT));
        // assert!(glob_match("a/**", "a", flags::DEFAULT));
        assert!(glob_match("**", "a/b", flags::DEFAULT));
        assert!(glob_match("**/**", "a/b", flags::DEFAULT));
        assert!(glob_match("**/**/*", "a/b", flags::DEFAULT));
        assert!(glob_match("**/**/b", "a/b", flags::DEFAULT));
        assert!(glob_match("**/b", "a/b", flags::DEFAULT));
        // assert!(glob_match("**/b/**", "a/b", flags::DEFAULT));
        // assert!(glob_match("*/b/**", "a/b", flags::DEFAULT));
        assert!(glob_match("a/**", "a/b", flags::DEFAULT));
        assert!(glob_match("a/**/*", "a/b", flags::DEFAULT));
        assert!(glob_match("a/**/**/*", "a/b", flags::DEFAULT));
        assert!(glob_match("**", "a/b/c", flags::DEFAULT));
        assert!(glob_match("**/**", "a/b/c", flags::DEFAULT));
        assert!(glob_match("**/**/*", "a/b/c", flags::DEFAULT));
        assert!(glob_match("**/b/*", "a/b/c", flags::DEFAULT));
        assert!(glob_match("**/b/**", "a/b/c", flags::DEFAULT));
        assert!(glob_match("*/b/**", "a/b/c", flags::DEFAULT));
        assert!(glob_match("a/**", "a/b/c", flags::DEFAULT));
        assert!(glob_match("a/**/*", "a/b/c", flags::DEFAULT));
        assert!(glob_match("a/**/**/*", "a/b/c", flags::DEFAULT));
        assert!(glob_match("**", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("**/**", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("**/**/*", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("**/**/d", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("**/b/**", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("**/b/*/*", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("**/d", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("*/b/**", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("a/**", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("a/**/*", "a/b/c/d", flags::DEFAULT));
        assert!(glob_match("a/**/**/*", "a/b/c/d", flags::DEFAULT));
    }

    #[test]
    fn utf8() {
        assert!(glob_match("フ*/**/*", "フォルダ/aaa.js", flags::DEFAULT));
        assert!(glob_match("フォ*/**/*", "フォルダ/aaa.js", flags::DEFAULT));
        assert!(glob_match(
            "フォル*/**/*",
            "フォルダ/aaa.js",
            flags::DEFAULT
        ));
        assert!(glob_match("フ*ル*/**/*", "フォルダ/aaa.js", flags::DEFAULT));
        assert!(glob_match(
            "フォルダ/**/*",
            "フォルダ/aaa.js",
            flags::DEFAULT
        ));
    }

    #[test]
    fn negation() {
        assert!(!glob_match("!*", "abc", flags::DEFAULT));
        assert!(!glob_match("!abc", "abc", flags::DEFAULT));
        assert!(!glob_match("*!.md", "bar.md", flags::DEFAULT));
        assert!(!glob_match("foo!.md", "bar.md", flags::DEFAULT));
        assert!(!glob_match("\\!*!*.md", "foo!.md", flags::DEFAULT));
        assert!(!glob_match("\\!*!*.md", "foo!bar.md", flags::DEFAULT));
        assert!(glob_match("*!*.md", "!foo!.md", flags::DEFAULT));
        assert!(glob_match("\\!*!*.md", "!foo!.md", flags::DEFAULT));
        assert!(glob_match("!*foo", "abc", flags::DEFAULT));
        assert!(glob_match("!foo*", "abc", flags::DEFAULT));
        assert!(glob_match("!xyz", "abc", flags::DEFAULT));
        assert!(glob_match("*!*.*", "ba!r.js", flags::DEFAULT));
        assert!(glob_match("*.md", "bar.md", flags::DEFAULT));
        assert!(glob_match("*!*.*", "foo!.md", flags::DEFAULT));
        assert!(glob_match("*!*.md", "foo!.md", flags::DEFAULT));
        assert!(glob_match("*!.md", "foo!.md", flags::DEFAULT));
        assert!(glob_match("*.md", "foo!.md", flags::DEFAULT));
        assert!(glob_match("foo!.md", "foo!.md", flags::DEFAULT));
        assert!(glob_match("*!*.md", "foo!bar.md", flags::DEFAULT));
        assert!(glob_match("*b*.md", "foobar.md", flags::DEFAULT));

        assert!(!glob_match("a!!b", "a", flags::DEFAULT));
        assert!(!glob_match("a!!b", "aa", flags::DEFAULT));
        assert!(!glob_match("a!!b", "a/b", flags::DEFAULT));
        assert!(!glob_match("a!!b", "a!b", flags::DEFAULT));
        assert!(glob_match("a!!b", "a!!b", flags::DEFAULT));
        assert!(!glob_match("a!!b", "a/!!/b", flags::DEFAULT));

        assert!(!glob_match("!a/b", "a/b", flags::DEFAULT));
        assert!(glob_match("!a/b", "a", flags::DEFAULT));
        assert!(glob_match("!a/b", "a.b", flags::DEFAULT));
        assert!(glob_match("!a/b", "a/a", flags::DEFAULT));
        assert!(glob_match("!a/b", "a/c", flags::DEFAULT));
        assert!(glob_match("!a/b", "b/a", flags::DEFAULT));
        assert!(glob_match("!a/b", "b/b", flags::DEFAULT));
        assert!(glob_match("!a/b", "b/c", flags::DEFAULT));

        assert!(!glob_match("!abc", "abc", flags::DEFAULT));
        assert!(glob_match("!!abc", "abc", flags::DEFAULT));
        assert!(!glob_match("!!!abc", "abc", flags::DEFAULT));
        assert!(glob_match("!!!!abc", "abc", flags::DEFAULT));
        assert!(!glob_match("!!!!!abc", "abc", flags::DEFAULT));
        assert!(glob_match("!!!!!!abc", "abc", flags::DEFAULT));
        assert!(!glob_match("!!!!!!!abc", "abc", flags::DEFAULT));
        assert!(glob_match("!!!!!!!!abc", "abc", flags::DEFAULT));

        // assert!(!glob_match("!(*/*)", "a/a", flags::DEFAULT));
        // assert!(!glob_match("!(*/*)", "a/b", flags::DEFAULT));
        // assert!(!glob_match("!(*/*)", "a/c", flags::DEFAULT));
        // assert!(!glob_match("!(*/*)", "b/a", flags::DEFAULT));
        // assert!(!glob_match("!(*/*)", "b/b", flags::DEFAULT));
        // assert!(!glob_match("!(*/*)", "b/c", flags::DEFAULT));
        // assert!(!glob_match("!(*/b)", "a/b", flags::DEFAULT));
        // assert!(!glob_match("!(*/b)", "b/b", flags::DEFAULT));
        // assert!(!glob_match("!(a/b)", "a/b", flags::DEFAULT));
        assert!(!glob_match("!*", "a", flags::DEFAULT));
        assert!(!glob_match("!*", "a.b", flags::DEFAULT));
        assert!(!glob_match("!*/*", "a/a", flags::DEFAULT));
        assert!(!glob_match("!*/*", "a/b", flags::DEFAULT));
        assert!(!glob_match("!*/*", "a/c", flags::DEFAULT));
        assert!(!glob_match("!*/*", "b/a", flags::DEFAULT));
        assert!(!glob_match("!*/*", "b/b", flags::DEFAULT));
        assert!(!glob_match("!*/*", "b/c", flags::DEFAULT));
        assert!(!glob_match("!*/b", "a/b", flags::DEFAULT));
        assert!(!glob_match("!*/b", "b/b", flags::DEFAULT));
        assert!(!glob_match("!*/c", "a/c", flags::DEFAULT));
        assert!(!glob_match("!*/c", "a/c", flags::DEFAULT));
        assert!(!glob_match("!*/c", "b/c", flags::DEFAULT));
        assert!(!glob_match("!*/c", "b/c", flags::DEFAULT));
        assert!(!glob_match("!*a*", "bar", flags::DEFAULT));
        assert!(!glob_match("!*a*", "fab", flags::DEFAULT));
        // assert!(!glob_match("!a/(*)", "a/a", flags::DEFAULT));
        // assert!(!glob_match("!a/(*)", "a/b", flags::DEFAULT));
        // assert!(!glob_match("!a/(*)", "a/c", flags::DEFAULT));
        // assert!(!glob_match("!a/(b)", "a/b", flags::DEFAULT));
        assert!(!glob_match("!a/*", "a/a", flags::DEFAULT));
        assert!(!glob_match("!a/*", "a/b", flags::DEFAULT));
        assert!(!glob_match("!a/*", "a/c", flags::DEFAULT));
        assert!(!glob_match("!f*b", "fab", flags::DEFAULT));
        // assert!(glob_match("!(*/*)", "a", flags::DEFAULT));
        // assert!(glob_match("!(*/*)", "a.b", flags::DEFAULT));
        // assert!(glob_match("!(*/b)", "a", flags::DEFAULT));
        // assert!(glob_match("!(*/b)", "a.b", flags::DEFAULT));
        // assert!(glob_match("!(*/b)", "a/a", flags::DEFAULT));
        // assert!(glob_match("!(*/b)", "a/c", flags::DEFAULT));
        // assert!(glob_match("!(*/b)", "b/a", flags::DEFAULT));
        // assert!(glob_match("!(*/b)", "b/c", flags::DEFAULT));
        // assert!(glob_match("!(a/b)", "a", flags::DEFAULT));
        // assert!(glob_match("!(a/b)", "a.b", flags::DEFAULT));
        // assert!(glob_match("!(a/b)", "a/a", flags::DEFAULT));
        // assert!(glob_match("!(a/b)", "a/c", flags::DEFAULT));
        // assert!(glob_match("!(a/b)", "b/a", flags::DEFAULT));
        // assert!(glob_match("!(a/b)", "b/b", flags::DEFAULT));
        // assert!(glob_match("!(a/b)", "b/c", flags::DEFAULT));
        assert!(glob_match("!*", "a/a", flags::DEFAULT));
        assert!(glob_match("!*", "a/b", flags::DEFAULT));
        assert!(glob_match("!*", "a/c", flags::DEFAULT));
        assert!(glob_match("!*", "b/a", flags::DEFAULT));
        assert!(glob_match("!*", "b/b", flags::DEFAULT));
        assert!(glob_match("!*", "b/c", flags::DEFAULT));
        assert!(glob_match("!*/*", "a", flags::DEFAULT));
        assert!(glob_match("!*/*", "a.b", flags::DEFAULT));
        assert!(glob_match("!*/b", "a", flags::DEFAULT));
        assert!(glob_match("!*/b", "a.b", flags::DEFAULT));
        assert!(glob_match("!*/b", "a/a", flags::DEFAULT));
        assert!(glob_match("!*/b", "a/c", flags::DEFAULT));
        assert!(glob_match("!*/b", "b/a", flags::DEFAULT));
        assert!(glob_match("!*/b", "b/c", flags::DEFAULT));
        assert!(glob_match("!*/c", "a", flags::DEFAULT));
        assert!(glob_match("!*/c", "a.b", flags::DEFAULT));
        assert!(glob_match("!*/c", "a/a", flags::DEFAULT));
        assert!(glob_match("!*/c", "a/b", flags::DEFAULT));
        assert!(glob_match("!*/c", "b/a", flags::DEFAULT));
        assert!(glob_match("!*/c", "b/b", flags::DEFAULT));
        assert!(glob_match("!*a*", "foo", flags::DEFAULT));
        // assert!(glob_match("!a/(*)", "a", flags::DEFAULT));
        // assert!(glob_match("!a/(*)", "a.b", flags::DEFAULT));
        // assert!(glob_match("!a/(*)", "b/a", flags::DEFAULT));
        // assert!(glob_match("!a/(*)", "b/b", flags::DEFAULT));
        // assert!(glob_match("!a/(*)", "b/c", flags::DEFAULT));
        // assert!(glob_match("!a/(b)", "a", flags::DEFAULT));
        // assert!(glob_match("!a/(b)", "a.b", flags::DEFAULT));
        // assert!(glob_match("!a/(b)", "a/a", flags::DEFAULT));
        // assert!(glob_match("!a/(b)", "a/c", flags::DEFAULT));
        // assert!(glob_match("!a/(b)", "b/a", flags::DEFAULT));
        // assert!(glob_match("!a/(b)", "b/b", flags::DEFAULT));
        // assert!(glob_match("!a/(b)", "b/c", flags::DEFAULT));
        assert!(glob_match("!a/*", "a", flags::DEFAULT));
        assert!(glob_match("!a/*", "a.b", flags::DEFAULT));
        assert!(glob_match("!a/*", "b/a", flags::DEFAULT));
        assert!(glob_match("!a/*", "b/b", flags::DEFAULT));
        assert!(glob_match("!a/*", "b/c", flags::DEFAULT));
        assert!(glob_match("!f*b", "bar", flags::DEFAULT));
        assert!(glob_match("!f*b", "foo", flags::DEFAULT));

        assert!(!glob_match("!.md", ".md", flags::DEFAULT));
        assert!(glob_match("!**/*.md", "a.js", flags::DEFAULT));
        // assert!(!glob_match("!**/*.md", "b.md", flags::DEFAULT));
        assert!(glob_match("!**/*.md", "c.txt", flags::DEFAULT));
        assert!(glob_match("!*.md", "a.js", flags::DEFAULT));
        assert!(!glob_match("!*.md", "b.md", flags::DEFAULT));
        assert!(glob_match("!*.md", "c.txt", flags::DEFAULT));
        assert!(!glob_match("!*.md", "abc.md", flags::DEFAULT));
        assert!(glob_match("!*.md", "abc.txt", flags::DEFAULT));
        assert!(!glob_match("!*.md", "foo.md", flags::DEFAULT));
        assert!(glob_match("!.md", "foo.md", flags::DEFAULT));

        assert!(glob_match("!*.md", "a.js", flags::DEFAULT));
        assert!(glob_match("!*.md", "b.txt", flags::DEFAULT));
        assert!(!glob_match("!*.md", "c.md", flags::DEFAULT));
        assert!(!glob_match("!a/*/a.js", "a/a/a.js", flags::DEFAULT));
        assert!(!glob_match("!a/*/a.js", "a/b/a.js", flags::DEFAULT));
        assert!(!glob_match("!a/*/a.js", "a/c/a.js", flags::DEFAULT));
        assert!(!glob_match("!a/*/*/a.js", "a/a/a/a.js", flags::DEFAULT));
        assert!(glob_match("!a/*/*/a.js", "b/a/b/a.js", flags::DEFAULT));
        assert!(glob_match("!a/*/*/a.js", "c/a/c/a.js", flags::DEFAULT));
        assert!(!glob_match("!a/a*.txt", "a/a.txt", flags::DEFAULT));
        assert!(glob_match("!a/a*.txt", "a/b.txt", flags::DEFAULT));
        assert!(glob_match("!a/a*.txt", "a/c.txt", flags::DEFAULT));
        assert!(!glob_match("!a.a*.txt", "a.a.txt", flags::DEFAULT));
        assert!(glob_match("!a.a*.txt", "a.b.txt", flags::DEFAULT));
        assert!(glob_match("!a.a*.txt", "a.c.txt", flags::DEFAULT));
        assert!(!glob_match("!a/*.txt", "a/a.txt", flags::DEFAULT));
        assert!(!glob_match("!a/*.txt", "a/b.txt", flags::DEFAULT));
        assert!(!glob_match("!a/*.txt", "a/c.txt", flags::DEFAULT));

        assert!(glob_match("!*.md", "a.js", flags::DEFAULT));
        assert!(glob_match("!*.md", "b.txt", flags::DEFAULT));
        assert!(!glob_match("!*.md", "c.md", flags::DEFAULT));
        // assert!(!glob_match("!**/a.js", "a/a/a.js", flags::DEFAULT));
        // assert!(!glob_match("!**/a.js", "a/b/a.js", flags::DEFAULT));
        // assert!(!glob_match("!**/a.js", "a/c/a.js", flags::DEFAULT));
        assert!(glob_match("!**/a.js", "a/a/b.js", flags::DEFAULT));
        assert!(!glob_match("!a/**/a.js", "a/a/a/a.js", flags::DEFAULT));
        assert!(glob_match("!a/**/a.js", "b/a/b/a.js", flags::DEFAULT));
        assert!(glob_match("!a/**/a.js", "c/a/c/a.js", flags::DEFAULT));
        assert!(glob_match("!**/*.md", "a/b.js", flags::DEFAULT));
        assert!(glob_match("!**/*.md", "a.js", flags::DEFAULT));
        assert!(!glob_match("!**/*.md", "a/b.md", flags::DEFAULT));
        // assert!(!glob_match("!**/*.md", "a.md", flags::DEFAULT));
        assert!(!glob_match("**/*.md", "a/b.js", flags::DEFAULT));
        assert!(!glob_match("**/*.md", "a.js", flags::DEFAULT));
        assert!(glob_match("**/*.md", "a/b.md", flags::DEFAULT));
        assert!(glob_match("**/*.md", "a.md", flags::DEFAULT));
        assert!(glob_match("!**/*.md", "a/b.js", flags::DEFAULT));
        assert!(glob_match("!**/*.md", "a.js", flags::DEFAULT));
        assert!(!glob_match("!**/*.md", "a/b.md", flags::DEFAULT));
        // assert!(!glob_match("!**/*.md", "a.md", flags::DEFAULT));
        assert!(glob_match("!*.md", "a/b.js", flags::DEFAULT));
        assert!(glob_match("!*.md", "a.js", flags::DEFAULT));
        assert!(glob_match("!*.md", "a/b.md", flags::DEFAULT));
        assert!(!glob_match("!*.md", "a.md", flags::DEFAULT));
        assert!(glob_match("!**/*.md", "a.js", flags::DEFAULT));
        // assert!(!glob_match("!**/*.md", "b.md", flags::DEFAULT));
        assert!(glob_match("!**/*.md", "c.txt", flags::DEFAULT));
    }

    #[test]
    fn question_mark() {
        assert!(glob_match("?", "a", flags::DEFAULT));
        assert!(!glob_match("?", "aa", flags::DEFAULT));
        assert!(!glob_match("?", "ab", flags::DEFAULT));
        assert!(!glob_match("?", "aaa", flags::DEFAULT));
        assert!(!glob_match("?", "abcdefg", flags::DEFAULT));

        assert!(!glob_match("??", "a", flags::DEFAULT));
        assert!(glob_match("??", "aa", flags::DEFAULT));
        assert!(glob_match("??", "ab", flags::DEFAULT));
        assert!(!glob_match("??", "aaa", flags::DEFAULT));
        assert!(!glob_match("??", "abcdefg", flags::DEFAULT));

        assert!(!glob_match("???", "a", flags::DEFAULT));
        assert!(!glob_match("???", "aa", flags::DEFAULT));
        assert!(!glob_match("???", "ab", flags::DEFAULT));
        assert!(glob_match("???", "aaa", flags::DEFAULT));
        assert!(!glob_match("???", "abcdefg", flags::DEFAULT));

        assert!(!glob_match("a?c", "aaa", flags::DEFAULT));
        assert!(glob_match("a?c", "aac", flags::DEFAULT));
        assert!(glob_match("a?c", "abc", flags::DEFAULT));
        assert!(!glob_match("ab?", "a", flags::DEFAULT));
        assert!(!glob_match("ab?", "aa", flags::DEFAULT));
        assert!(!glob_match("ab?", "ab", flags::DEFAULT));
        assert!(!glob_match("ab?", "ac", flags::DEFAULT));
        assert!(!glob_match("ab?", "abcd", flags::DEFAULT));
        assert!(!glob_match("ab?", "abbb", flags::DEFAULT));
        assert!(glob_match("a?b", "acb", flags::DEFAULT));

        assert!(!glob_match(
            "a/?/c/?/e.md",
            "a/bb/c/dd/e.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/??/c/??/e.md",
            "a/bb/c/dd/e.md",
            flags::DEFAULT
        ));
        assert!(!glob_match("a/??/c.md", "a/bbb/c.md", flags::DEFAULT));
        assert!(glob_match("a/?/c.md", "a/b/c.md", flags::DEFAULT));
        assert!(glob_match("a/?/c/?/e.md", "a/b/c/d/e.md", flags::DEFAULT));
        assert!(!glob_match(
            "a/?/c/???/e.md",
            "a/b/c/d/e.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/?/c/???/e.md",
            "a/b/c/zzz/e.md",
            flags::DEFAULT
        ));
        assert!(!glob_match("a/?/c.md", "a/bb/c.md", flags::DEFAULT));
        assert!(glob_match("a/??/c.md", "a/bb/c.md", flags::DEFAULT));
        assert!(glob_match("a/???/c.md", "a/bbb/c.md", flags::DEFAULT));
        assert!(glob_match("a/????/c.md", "a/bbbb/c.md", flags::DEFAULT));
    }

    #[test]
    fn braces() {
        assert!(glob_match("{a,b,c}", "a", flags::DEFAULT));
        assert!(glob_match("{a,b,c}", "b", flags::DEFAULT));
        assert!(glob_match("{a,b,c}", "c", flags::DEFAULT));
        assert!(!glob_match("{a,b,c}", "aa", flags::DEFAULT));
        assert!(!glob_match("{a,b,c}", "bb", flags::DEFAULT));
        assert!(!glob_match("{a,b,c}", "cc", flags::DEFAULT));

        assert!(glob_match("a/{a,b}", "a/a", flags::DEFAULT));
        assert!(glob_match("a/{a,b}", "a/b", flags::DEFAULT));
        assert!(!glob_match("a/{a,b}", "a/c", flags::DEFAULT));
        assert!(!glob_match("a/{a,b}", "b/b", flags::DEFAULT));
        assert!(!glob_match("a/{a,b,c}", "b/b", flags::DEFAULT));
        assert!(glob_match("a/{a,b,c}", "a/c", flags::DEFAULT));
        assert!(glob_match("a{b,bc}.txt", "abc.txt", flags::DEFAULT));

        assert!(glob_match("foo[{a,b}]baz", "foo{baz", flags::DEFAULT));

        assert!(!glob_match("a{,b}.txt", "abc.txt", flags::DEFAULT));
        assert!(!glob_match("a{a,b,}.txt", "abc.txt", flags::DEFAULT));
        assert!(!glob_match("a{b,}.txt", "abc.txt", flags::DEFAULT));
        assert!(glob_match("a{,b}.txt", "a.txt", flags::DEFAULT));
        assert!(glob_match("a{b,}.txt", "a.txt", flags::DEFAULT));
        assert!(glob_match("a{a,b,}.txt", "aa.txt", flags::DEFAULT));
        assert!(glob_match("a{a,b,}.txt", "aa.txt", flags::DEFAULT));
        assert!(glob_match("a{,b}.txt", "ab.txt", flags::DEFAULT));
        assert!(glob_match("a{b,}.txt", "ab.txt", flags::DEFAULT));

        // assert!(glob_match("{a/,}a/**", "a", flags::DEFAULT));
        assert!(glob_match("a{a,b/}*.txt", "aa.txt", flags::DEFAULT));
        assert!(glob_match("a{a,b/}*.txt", "ab/.txt", flags::DEFAULT));
        assert!(glob_match("a{a,b/}*.txt", "ab/a.txt", flags::DEFAULT));
        // assert!(glob_match("{a/,}a/**", "a/", flags::DEFAULT));
        assert!(glob_match("{a/,}a/**", "a/a/", flags::DEFAULT));
        // assert!(glob_match("{a/,}a/**", "a/a", flags::DEFAULT));
        assert!(glob_match("{a/,}a/**", "a/a/a", flags::DEFAULT));
        assert!(glob_match("{a/,}a/**", "a/a/", flags::DEFAULT));
        assert!(glob_match("{a/,}a/**", "a/a/a/", flags::DEFAULT));
        assert!(glob_match("{a/,}b/**", "a/b/a/", flags::DEFAULT));
        assert!(glob_match("{a/,}b/**", "b/a/", flags::DEFAULT));
        assert!(glob_match("a{,/}*.txt", "a.txt", flags::DEFAULT));
        assert!(glob_match("a{,/}*.txt", "ab.txt", flags::DEFAULT));
        assert!(glob_match("a{,/}*.txt", "a/b.txt", flags::DEFAULT));
        assert!(glob_match("a{,/}*.txt", "a/ab.txt", flags::DEFAULT));

        assert!(glob_match(
            "a{,.*{foo,db},\\(bar\\)}.txt",
            "a.txt",
            flags::DEFAULT
        ));
        assert!(!glob_match(
            "a{,.*{foo,db},\\(bar\\)}.txt",
            "adb.txt",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a{,.*{foo,db},\\(bar\\)}.txt",
            "a.db.txt",
            flags::DEFAULT
        ));

        assert!(glob_match(
            "a{,*.{foo,db},\\(bar\\)}.txt",
            "a.txt",
            flags::DEFAULT
        ));
        assert!(!glob_match(
            "a{,*.{foo,db},\\(bar\\)}.txt",
            "adb.txt",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a{,*.{foo,db},\\(bar\\)}.txt",
            "a.db.txt",
            flags::DEFAULT
        ));

        // assert!(glob_match("a{,.*{foo,db},\\(bar\\)}", "a", flags::DEFAULT));
        assert!(!glob_match(
            "a{,.*{foo,db},\\(bar\\)}",
            "adb",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a{,.*{foo,db},\\(bar\\)}",
            "a.db",
            flags::DEFAULT
        ));

        // assert!(glob_match("a{,*.{foo,db},\\(bar\\)}", "a", flags::DEFAULT));
        assert!(!glob_match(
            "a{,*.{foo,db},\\(bar\\)}",
            "adb",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a{,*.{foo,db},\\(bar\\)}",
            "a.db",
            flags::DEFAULT
        ));

        assert!(!glob_match("{,.*{foo,db},\\(bar\\)}", "a", flags::DEFAULT));
        assert!(!glob_match(
            "{,.*{foo,db},\\(bar\\)}",
            "adb",
            flags::DEFAULT
        ));
        assert!(!glob_match(
            "{,.*{foo,db},\\(bar\\)}",
            "a.db",
            flags::DEFAULT
        ));
        assert!(glob_match("{,.*{foo,db},\\(bar\\)}", ".db", flags::DEFAULT));

        assert!(!glob_match("{,*.{foo,db},\\(bar\\)}", "a", flags::DEFAULT));
        assert!(glob_match("{*,*.{foo,db},\\(bar\\)}", "a", flags::DEFAULT));
        assert!(!glob_match(
            "{,*.{foo,db},\\(bar\\)}",
            "adb",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "{,*.{foo,db},\\(bar\\)}",
            "a.db",
            flags::DEFAULT
        ));

        assert!(!glob_match(
            "a/b/**/c{d,e}/**/xyz.md",
            "a/b/c/xyz.md",
            flags::DEFAULT
        ));
        assert!(!glob_match(
            "a/b/**/c{d,e}/**/xyz.md",
            "a/b/d/xyz.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/b/**/c{d,e}/**/xyz.md",
            "a/b/cd/xyz.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/b/**/{c,d,e}/**/xyz.md",
            "a/b/c/xyz.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/b/**/{c,d,e}/**/xyz.md",
            "a/b/d/xyz.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/b/**/{c,d,e}/**/xyz.md",
            "a/b/e/xyz.md",
            flags::DEFAULT
        ));

        assert!(glob_match("*{a,b}*", "xax", flags::DEFAULT));
        assert!(glob_match("*{a,b}*", "xxax", flags::DEFAULT));
        assert!(glob_match("*{a,b}*", "xbx", flags::DEFAULT));

        assert!(glob_match("*{*a,b}", "xba", flags::DEFAULT));
        assert!(glob_match("*{*a,b}", "xb", flags::DEFAULT));

        assert!(!glob_match("*??", "a", flags::DEFAULT));
        assert!(!glob_match("*???", "aa", flags::DEFAULT));
        assert!(glob_match("*???", "aaa", flags::DEFAULT));
        assert!(!glob_match("*****??", "a", flags::DEFAULT));
        assert!(!glob_match("*****???", "aa", flags::DEFAULT));
        assert!(glob_match("*****???", "aaa", flags::DEFAULT));

        assert!(!glob_match("a*?c", "aaa", flags::DEFAULT));
        assert!(glob_match("a*?c", "aac", flags::DEFAULT));
        assert!(glob_match("a*?c", "abc", flags::DEFAULT));

        assert!(glob_match("a**?c", "abc", flags::DEFAULT));
        assert!(!glob_match("a**?c", "abb", flags::DEFAULT));
        assert!(glob_match("a**?c", "acc", flags::DEFAULT));
        assert!(glob_match("a*****?c", "abc", flags::DEFAULT));

        assert!(glob_match("*****?", "a", flags::DEFAULT));
        assert!(glob_match("*****?", "aa", flags::DEFAULT));
        assert!(glob_match("*****?", "abc", flags::DEFAULT));
        assert!(glob_match("*****?", "zzz", flags::DEFAULT));
        assert!(glob_match("*****?", "bbb", flags::DEFAULT));
        assert!(glob_match("*****?", "aaaa", flags::DEFAULT));

        assert!(!glob_match("*****??", "a", flags::DEFAULT));
        assert!(glob_match("*****??", "aa", flags::DEFAULT));
        assert!(glob_match("*****??", "abc", flags::DEFAULT));
        assert!(glob_match("*****??", "zzz", flags::DEFAULT));
        assert!(glob_match("*****??", "bbb", flags::DEFAULT));
        assert!(glob_match("*****??", "aaaa", flags::DEFAULT));

        assert!(!glob_match("?*****??", "a", flags::DEFAULT));
        assert!(!glob_match("?*****??", "aa", flags::DEFAULT));
        assert!(glob_match("?*****??", "abc", flags::DEFAULT));
        assert!(glob_match("?*****??", "zzz", flags::DEFAULT));
        assert!(glob_match("?*****??", "bbb", flags::DEFAULT));
        assert!(glob_match("?*****??", "aaaa", flags::DEFAULT));

        assert!(glob_match("?*****?c", "abc", flags::DEFAULT));
        assert!(!glob_match("?*****?c", "abb", flags::DEFAULT));
        assert!(!glob_match("?*****?c", "zzz", flags::DEFAULT));

        assert!(glob_match("?***?****c", "abc", flags::DEFAULT));
        assert!(!glob_match("?***?****c", "bbb", flags::DEFAULT));
        assert!(!glob_match("?***?****c", "zzz", flags::DEFAULT));

        assert!(glob_match("?***?****?", "abc", flags::DEFAULT));
        assert!(glob_match("?***?****?", "bbb", flags::DEFAULT));
        assert!(glob_match("?***?****?", "zzz", flags::DEFAULT));

        assert!(glob_match("?***?****", "abc", flags::DEFAULT));
        assert!(glob_match("*******c", "abc", flags::DEFAULT));
        assert!(glob_match("*******?", "abc", flags::DEFAULT));
        assert!(glob_match("a*cd**?**??k", "abcdecdhjk", flags::DEFAULT));
        assert!(glob_match("a**?**cd**?**??k", "abcdecdhjk", flags::DEFAULT));
        assert!(glob_match(
            "a**?**cd**?**??k***",
            "abcdecdhjk",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a**?**cd**?**??***k",
            "abcdecdhjk",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a**?**cd**?**??***k**",
            "abcdecdhjk",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a****c**?**??*****",
            "abcdecdhjk",
            flags::DEFAULT
        ));

        assert!(!glob_match(
            "a/?/c/?/*/e.md",
            "a/b/c/d/e.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/?/c/?/*/e.md",
            "a/b/c/d/e/e.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/?/c/?/*/e.md",
            "a/b/c/d/efghijk/e.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/?/**/e.md",
            "a/b/c/d/efghijk/e.md",
            flags::DEFAULT
        ));
        assert!(!glob_match("a/?/e.md", "a/bb/e.md", flags::DEFAULT));
        assert!(glob_match("a/??/e.md", "a/bb/e.md", flags::DEFAULT));
        assert!(!glob_match("a/?/**/e.md", "a/bb/e.md", flags::DEFAULT));
        assert!(glob_match("a/?/**/e.md", "a/b/ccc/e.md", flags::DEFAULT));
        assert!(glob_match(
            "a/*/?/**/e.md",
            "a/b/c/d/efghijk/e.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/*/?/**/e.md",
            "a/b/c/d/efgh.ijk/e.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/*/?/**/e.md",
            "a/b.bb/c/d/efgh.ijk/e.md",
            flags::DEFAULT
        ));
        assert!(glob_match(
            "a/*/?/**/e.md",
            "a/bbb/c/d/efgh.ijk/e.md",
            flags::DEFAULT
        ));

        assert!(glob_match("a/*/ab??.md", "a/bbb/abcd.md", flags::DEFAULT));
        assert!(glob_match("a/bbb/ab??.md", "a/bbb/abcd.md", flags::DEFAULT));
        assert!(glob_match("a/bbb/ab???md", "a/bbb/abcd.md", flags::DEFAULT));
    }

    #[test]
    fn captures() {
        fn test_captures<'a>(glob: &str, path: &'a str) -> Option<Vec<&'a str>> {
            glob_match_with_captures(glob, path)
                .map(|v| v.into_iter().map(|capture| &path[capture]).collect())
        }

        assert_eq!(test_captures("a/b", "a/b"), Some(vec![]));
        assert_eq!(test_captures("a/*/c", "a/bx/c"), Some(vec!["bx"]));
        assert_eq!(test_captures("a/*/c", "a/test/c"), Some(vec!["test"]));
        assert_eq!(
            test_captures("a/*/c/*/e", "a/b/c/d/e"),
            Some(vec!["b", "d"])
        );
        assert_eq!(
            test_captures("a/*/c/*/e", "a/b/c/d/e"),
            Some(vec!["b", "d"])
        );
        assert_eq!(test_captures("a/{b,x}/c", "a/b/c"), Some(vec!["b"]));
        assert_eq!(test_captures("a/{b,x}/c", "a/x/c"), Some(vec!["x"]));
        assert_eq!(test_captures("a/?/c", "a/b/c"), Some(vec!["b"]));
        assert_eq!(test_captures("a/*?x/c", "a/yybx/c"), Some(vec!["yy", "b"]));
        assert_eq!(
            test_captures("a/*[a-z]x/c", "a/yybx/c"),
            Some(vec!["yy", "b"])
        );
        assert_eq!(
            test_captures("a/{b*c,c}y", "a/bdcy"),
            Some(vec!["bdc", "d"])
        );
        assert_eq!(test_captures("a/{b*,c}y", "a/bdy"), Some(vec!["bd", "d"]));
        assert_eq!(test_captures("a/{b*c,c}", "a/bdc"), Some(vec!["bdc", "d"]));
        assert_eq!(test_captures("a/{b*,c}", "a/bd"), Some(vec!["bd", "d"]));
        assert_eq!(test_captures("a/{b*,c}", "a/c"), Some(vec!["c", ""]));
        assert_eq!(
            test_captures("a/{b{c,d},c}y", "a/bdy"),
            Some(vec!["bd", "d"])
        );
        assert_eq!(
            test_captures("a/{b*,c*}y", "a/bdy"),
            Some(vec!["bd", "d", ""])
        );
        assert_eq!(
            test_captures("a/{b*,c*}y", "a/cdy"),
            Some(vec!["cd", "", "d"])
        );
        assert_eq!(test_captures("a/{b,c}", "a/b"), Some(vec!["b"]));
        assert_eq!(test_captures("a/{b,c}", "a/c"), Some(vec!["c"]));
        assert_eq!(test_captures("a/{b,c[}]*}", "a/b"), Some(vec!["b", "", ""]));
        assert_eq!(
            test_captures("a/{b,c[}]*}", "a/c}xx"),
            Some(vec!["c}xx", "}", "xx"])
        );

        // assert\.deepEqual\(([!])?capture\('(.*?)', ['"](.*?)['"]\), (.*)?\);
        // assert_eq!(test_captures("$2", "$3"), Some(vec!$4));

        assert_eq!(test_captures("test/*", "test/foo"), Some(vec!["foo"]));
        assert_eq!(
            test_captures("test/*/bar", "test/foo/bar"),
            Some(vec!["foo"])
        );
        assert_eq!(
            test_captures("test/*/bar/*", "test/foo/bar/baz"),
            Some(vec!["foo", "baz"])
        );
        assert_eq!(test_captures("test/*.js", "test/foo.js"), Some(vec!["foo"]));
        assert_eq!(
            test_captures("test/*-controller.js", "test/foo-controller.js"),
            Some(vec!["foo"])
        );

        assert_eq!(
            test_captures("test/**/*.js", "test/a.js"),
            Some(vec!["", "a"])
        );
        assert_eq!(
            test_captures("test/**/*.js", "test/dir/a.js"),
            Some(vec!["dir", "a"])
        );
        assert_eq!(
            test_captures("test/**/*.js", "test/dir/test/a.js"),
            Some(vec!["dir/test", "a"])
        );
        assert_eq!(
            test_captures("**/*.js", "test/dir/a.js"),
            Some(vec!["test/dir", "a"])
        );
        assert_eq!(
            test_captures("**/**/**/**/a", "foo/bar/baz/a"),
            Some(vec!["foo/bar/baz"])
        );
        assert_eq!(
            test_captures("a/{b/**/y,c/**/d}", "a/b/y"),
            Some(vec!["b/y", "", ""])
        );
        assert_eq!(
            test_captures("a/{b/**/y,c/**/d}", "a/b/x/x/y"),
            Some(vec!["b/x/x/y", "x/x", ""])
        );
        assert_eq!(
            test_captures("a/{b/**/y,c/**/d}", "a/c/x/x/d"),
            Some(vec!["c/x/x/d", "", "x/x"])
        );
        assert_eq!(
            test_captures("a/{b/**/**/y,c/**/**/d}", "a/b/x/x/x/x/x/y"),
            Some(vec!["b/x/x/x/x/x/y", "x/x/x/x/x", ""])
        );
        assert_eq!(
            test_captures("a/{b/**/**/y,c/**/**/d}", "a/c/x/x/x/x/x/d"),
            Some(vec!["c/x/x/x/x/x/d", "", "x/x/x/x/x"])
        );
        assert_eq!(
            test_captures(
                "some/**/{a,b,c}/**/needle.txt",
                "some/path/a/to/the/needle.txt"
            ),
            Some(vec!["path", "a", "to/the"])
        );
    }

    #[test]
    fn fuzz_tests() {
        // https://github.com/devongovett/glob-match/issues/1
        let s = "{*{??*{??**,Uz*zz}w**{*{**a,z***b*[!}w??*azzzzzzzz*!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!z[za,z&zz}w**z*z*}";
        assert!(!glob_match(s, s, flags::DEFAULT));
        let s = "**** *{*{??*{??***\u{5} *{*{??*{??***\u{5},\0U\0}]*****\u{1},\0***\0,\0\0}w****,\0U\0}]*****\u{1},\0***\0,\0\0}w*****\u{1}***{}*.*\0\0*\0";
        assert!(!glob_match(s, s, flags::DEFAULT));
    }
}
