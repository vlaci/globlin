<!-- SPDX-FileCopyrightText: 2025 2025 László Vaskó <opensource@accounts.vlaci.email>

SPDX-License-Identifier: EUPL-1.2 -->

# globlin

This package provides a faster and more featureful `fnmatch`
implementation over the one built into Python's standard library.

The implementation is based on
[`glob-match`](https://crates.io/crates/glob-match) library.

## Supported patterns

All pattern characters besides `*` and `?` can be enabled or
disabled. When not specified, all special characters are enabled with
their standard behavior. When any `Flag`s are passed, only the
explicitly passed `Flag`s are enabled.

### `?` - Single character wildcard

Matches any single character except `/`.

**Example:** `fo?` matches `foo` but not `foobar`.

**Flags:**
- `NO_PATH` - `/` is matched as well

### `*` - Multi-character wildcard

Matches zero or more characters, except path separators (e.g. `/`).

**Flags:**
- `NO_PATH` - `/` is matched as well

### `**` - Globstar

Matches zero or more characters, including path separators. Must match
a complete path segment.

**Examples:** `foo/**/bar` or `foo/**` but not `foo**`

**Flags:**
- `GLOB_STAR` - enable (default)
- `NO_PATH` - `/` is matched as well, `foo**` will match `foo/bar/`

### `[..]` - Bracket expansion

Matches one of the characters between the brackets. `[ab]` matches
exactly one `a` or `b`. Ranges are also allowed, i.e. `[a-z]` matches
any lowercase characters of the English alphabet.

The matching behavior can be inverted, for example `[!ab]` or `[^ab]`
matches any character except `a` and `b`.

**Flags:**
- `BRACKET_EXPANSION` - enable (default)

### `{.,.}` - Brace expansion

Matches one of the patterns contained in the braces.

**Examples:** `{foo?,foo*bar}` matches `foot`, `foobar` and `footbar`. Braces can be
nested up to 10 levels.

**Flags:**
- `BRACE_EXPANSION` - enable (default)

### `!` - Negation

Negates the following expression.

**Example:** `!foo` matches anything except `foo`.

**Flags:**
- `NEGATE` - enable (default)

### `\` - Escape character

Escapes special meaning of the following character.

**Example:** `\*` matches the literal `*`.

**Flags:**
- `ESCAPE` - enable (default)


## API

```python
def fnmatch(pattern: str, value: str, *flags: Flag) -> bool: ...

class Flag:
    EMPTY: Flag = ...
    GLOB_STAR: Flag = ...
    BRACKET_EXPANSION: Flag = ...
    BRACE_EXPANSION: Flag = ...
    NEGATE: Flag = ...
    ESCAPE: Flag = ...
    NO_PATH: Flag = ...
```
