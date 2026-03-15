<!-- SPDX-FileCopyrightText: 2025 László Vaskó <opensource@accounts.vlaci.email>

SPDX-License-Identifier: EUPL-1.2 -->

# globlin

A fast, Rust-backed glob pattern matching library for Python. Drop-in
alternative to the standard library's `fnmatch` with additional features
like globstar, brace expansion, and negation.

## Quick start

```python
from globlin import Glob

# POSIX fnmatch-like defaults (bracket expansion + escape)
glob = Glob.default()
glob.match("foo*", "foobar")      # True
glob.match("[abc]", "b")           # True
glob.match(r"\*", "*")             # True

# Opt in to path-aware matching
glob = Glob.default().globstar()
glob.match("src/**/test_*.py", "src/a/b/test_foo.py")  # True
glob.match("src/*/test_*.py", "src/a/b/test_foo.py")   # False

# Brace expansion
glob = Glob.default().brace_expansion()
glob.match("{src,lib}/*.py", "src/foo.py")  # True
```

## Installation

```
pip install globlin
```

<details>
<summary>Supported patterns</summary>

| Pattern | Description | Builder method |
|---------|-------------|----------------|
| `?` | Match any single character | enabled by default |
| `*` | Match zero or more characters | enabled by default |
| `[ab]`, `[a-z]` | Bracket expansion | `.bracket_expansion()` (default) |
| `\*` | Escape special characters | `.escape()` (default) |
| `**` | Match across path separators | `.globstar()` |
| `{a,b}` | Brace expansion | `.brace_expansion()` |
| `!pat` | Negation | `.negate()` |
| `/` as separator | `*` and `?` don't match `/` | `.path_separator()` |

`Glob.default()` enables bracket expansion and escape sequences, matching
POSIX `fnmatch(3)` behavior. All other features are opt-in via builder
methods. Calling `.globstar()` implies `.path_separator()`.

Each feature can be disabled with its `no_` counterpart (e.g.
`.no_bracket_expansion()`).

</details>

## Migrating from the old API

The `Flag` enum and `fnmatch()` function are deprecated. Replace with
`Glob`:

```python
# Before
from globlin import Flag, fnmatch
fnmatch("src/**/*.py", path, Flag.GLOB_STAR)

# After
from globlin import Glob
glob = Glob.default().globstar()
glob.match("src/**/*.py", path)
```

## License

[EUPL-1.2](LICENSES/EUPL-1.2.txt). Based on [`glob-match`](https://crates.io/crates/glob-match) (MIT).
