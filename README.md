<!--
SPDX-FileCopyrightText: 2025 2025 László Vaskó <opensource@vlaci.email.com>

SPDX-License-Identifier: EUPL-1.2
-->

# globlin

**NOTE**: The project is renamed to [`globlin`](https://pypi.org/project/globlin). This package is no longer updated.

This package provides a faster and more featureful `fnmatch` implementation over the one built into Python's standard library. 

The implementation is provided by the [`glob-match`](https://crates.io/crates/glob-match) library.

## Globbing syntax


| Syntax  | Meaning                                                                                                                                                                                             |
|---------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `?`     | Matches any single character.                                                                                                                                                                       |
| `*`     | Matches zero or more characters, except for path separators (e.g. `/`).                                                                                                                             |
| `**`    | Matches zero or more characters, including path separators. Must match a complete path segment (i.e. followed by a `/` or the end of the pattern).                                                  |
| `[ab]`  | Matches one of the characters contained in the brackets. Character ranges, e.g. `[a-z]` are also supported. Use `[!ab]` or `[^ab]` to match any character _except_ those contained in the brackets. |
| `{a,b}` | Matches one of the patterns contained in the braces. Any of the wildcard characters can be used in the sub-patterns. Braces may be nested up to 10 levels deep.                                     |
| `!`     | When at the start of the glob, this negates the result. Multiple `!` characters negate the glob multiple times.                                                                                     |
| `\`     | A backslash character may be used to escape any of the above special characters.                                                                                                                    |

## API

```python
def fnmatch(pattern: str, value: str) -> bool: ...
```
