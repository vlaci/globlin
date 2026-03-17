---
icon: lucide/book-open
---

<!--
SPDX-FileCopyrightText: 2026 László Vaskó <opensource@accounts.vlaci.email>

SPDX-License-Identifier: EUPL-1.2
-->

# Guide

## Installation

--8<-- "snippets/installation.md"

## Usage

!!! note "Case sensitivity"
    Unlike Python's [`fnmatch.fnmatch`][fnmatch], which is case-insensitive
    on case-insensitive filesystems (macOS, Windows), globlin always performs
    **case-sensitive** matching - equivalent to
    [`fnmatch.fnmatchcase`][fnmatchcase]. For case-insensitive matching,
    normalize both the pattern and value with [`os.path.normcase()`][normcase]
    before matching.

[fnmatch]: https://docs.python.org/3/library/fnmatch.html#fnmatch.fnmatch
[fnmatchcase]: https://docs.python.org/3/library/fnmatch.html#fnmatch.fnmatchcase
[normcase]: https://docs.python.org/3/library/os.path.html#os.path.normcase

### Builder API { data-version="unreleased" }

The primary API is the [`Glob`][globlin.Glob] class. Create one with [`Glob.default()`][globlin.Glob.default] for
POSIX fnmatch-like behavior (bracket expansion and escape sequences enabled):


```python
from globlin import Glob

glob = Glob.default()
```

Use [`.match(pattern, value)`][globlin.Glob.match] to test whether a value matches a glob pattern:

```python
glob.match("*.py", "foo.py")       # ✅
glob.match("*.py", "foo.txt")      # ❌
glob.match("test_?", "test_a")     # ✅
glob.match("[abc]", "b")           # ✅
```

Enable additional features by chaining builder methods:

```python
# Enable globstar (implies path separator handling)
glob = Glob.default().globstar()
glob.match("src/**/*.py", "src/a/b/foo.py")  # ✅

# Enable brace expansion
glob = Glob.default().brace_expansion()
glob.match("{src,lib}/*.py", "src/foo.py")   # ✅

# Combine features
glob = Glob.default().globstar().brace_expansion().negate()
```

Every feature has a `no_` counterpart to disable it:

```python
# Disable escape sequences
glob = Glob.default().no_escape()
glob.match(r"\*", r"\*")  # ✅ (backslash is literal)
```

Use [`Glob.empty()`][globlin.Glob.empty] to start with all features off - only `*` and `?`
wildcards work:

```python
glob = Glob.empty()
glob.match("*.py", "foo.py")   # ✅
glob.match("[abc]", "b")       # ❌ (brackets are literal)
```

### Flags based API { data-version="v0.2" }


!!! danger "Deprecated"
    The [`fnmatch`][globlin.fnmatch] function and [`Flag`][globlin.Flag] enum will be
    removed in 1.0. See [Migrating from v0.2](migration.md) for how to update
    your code.

```python
from globlin import fnmatch

fnmatch("*.py", "foo.py")  # ✅
```

Pass [`Flag`][globlin.Flag] values to `fnmatch()` to enable features:

```python
from globlin import fnmatch, Flag

# Enable globstar
fnmatch("src/**/*.py", "src/a/b/foo.py", Flag.GLOB_STAR)       # ✅

# Enable brace expansion
fnmatch("{src,lib}/*.py", "src/foo.py", Flag.BRACE_EXPANSION)  # ✅

# Combine features
fnmatch("!{a,b}", "c", Flag.NEGATE, Flag.BRACE_EXPANSION)      # ✅
```

Pass [`Flags`][globlin.Flags] to [`Glob.from_flags()`][globlin.Glob.from_flags]: *unreleased*{ .version-badge }

```python
from globlin import Glob, Flags

glob = Glob.from_flags(Flags.GLOB_STAR | Flags.PATH_SEPARATOR | Flags.ESCAPE)
```

See the [API reference](api-reference.md) for all available flags.

## Pattern features

### Path separator handling

With path separator handling, `*` and `?` stop at `/`.
The pattern `*.py` matches `foo.py` but not `dir/foo.py`.

```python
glob = Glob.default().path_separator()
```

Note: [`.globstar()`][globlin.Glob.globstar] automatically enables path separator handling.

```python
# Without path separator (default)
glob = Glob.default()
glob.match("*.py", "dir/foo.py")     # ✅ (* matches anything)

# With path separator
glob = Glob.default().path_separator()
glob.match("*.py", "foo.py")         # ✅
glob.match("*.py", "dir/foo.py")     # ❌ (* stops at /)
glob.match("*/*.py", "dir/foo.py")   # ✅
```

### Globstar (`**`)

The `**` pattern matches zero or more path segments, including nested
directories.

```python
glob = Glob.default().globstar()
```

!!! note "Path Separator handling"
    Calling [`.globstar()`][globlin.Glob.globstar] automatically enables [`.path_separator()`][globlin.Glob.path_separator], since
    globstar is only meaningful when `/` is treated as a path separator.

```python
glob = Glob.default().globstar()

# Match files at any depth
glob.match("src/**/*.py", "src/foo.py")           # ✅
glob.match("src/**/*.py", "src/a/b/c/foo.py")     # ✅

# ** matches zero segments too
glob.match("**/*.py", "foo.py")                   # ✅

# Single * does not cross /
glob.match("src/*/*.py", "src/a/b/foo.py")        # ❌
```

`**` matches any number of path components (sequences of characters
separated by `/`). A single `*` matches any character except `/`.

### Bracket expansion (`[...]`)

Bracket expressions match a single character from a set or range.
`Glob.default()` enables bracket expansion.

```python
glob = Glob.default()

# Character set
glob.match("[abc]", "a")     # ✅
glob.match("[abc]", "d")     # ❌

# Character range
glob.match("[a-z]", "m")     # ✅
glob.match("[a-z]", "M")     # ❌

# Negated set
glob.match("[!abc]", "d")    # ✅
glob.match("[!abc]", "a")    # ❌

# Combined with wildcards
glob.match("file[0-9].txt", "file3.txt")    # ✅
glob.match("file[0-9].txt", "file10.txt")   # ❌
```

Without bracket expansion, brackets match literally:

```python
glob = Glob.default().no_bracket_expansion()
glob.match("[abc]", "a")       # ❌
glob.match("[abc]", "[abc]")   # ✅
```

### Brace expansion (`{...}`)

Brace expressions match any of several comma-separated alternatives.

```python
glob = Glob.default().brace_expansion()

# Simple alternatives
glob.match("{foo,bar}", "foo")         # ✅
glob.match("{foo,bar}", "baz")         # ❌

# In paths
glob.match("{src,lib}/*.py", "src/foo.py")   # ✅
glob.match("{src,lib}/*.py", "lib/bar.py")   # ✅
glob.match("{src,lib}/*.py", "test/baz.py")  # ❌

# Nested braces (up to 10 levels)
glob.match("{a,{b,c}}", "c")           # ✅
```

Braces nest up to 10 levels deep. The matcher tries each alternative in
order and picks the first match.

### Negation (`!`)

A leading `!` inverts the match: the pattern matches when the value does
*not* match the rest of the pattern.

```python
glob = Glob.default().negate()

glob.match("!*.py", "foo.txt")   # ✅  (does not match *.py)
glob.match("!*.py", "foo.py")    # ❌ (matches *.py, so negated)
```

### Escape sequences (`\`)

A backslash `\` before a special character removes its special meaning,
letting you match literal `*`, `?`, `[`, etc.
`Glob.default()` enables escape sequences.

```python
glob = Glob.default()

# Match literal *
glob.match(r"\*", "*")       # ✅
glob.match(r"\*", "foo")     # ❌

# Match literal ?
glob.match(r"\?", "?")       # ✅
glob.match(r"\?", "a")       # ❌

# Match literal brackets
glob.match(r"\[abc\]", "[abc]")   # ✅
```

Without escape handling, backslash matches literally:

```python
glob = Glob.default().no_escape()
glob.match(r"\*", r"\foo")   # ✅ (\ is literal, * is wildcard)
glob.match(r"\*", "foo")     # ❌ (no leading \)
```
