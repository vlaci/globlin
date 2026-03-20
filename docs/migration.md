---
icon: lucide/arrow-right-left
---

<!--
SPDX-FileCopyrightText: 2026 László Vaskó <opensource@accounts.vlaci.email>

SPDX-License-Identifier: EUPL-1.2
-->

# Migration Guide

## Migrating from v0.2

The [`fnmatch()`][globlin.fnmatch] function and [`Flag`][globlin.Flag] enum are deprecated and will be
removed in 1.0. The new `Glob` builder API replaces it with a composable,
reusable interface.

### Basic matching

The simplest calls translate directly - `fnmatch(pat, val)` becomes
`Glob.default().match(pat, val)`:

```python
# Before
from globlin import fnmatch

fnmatch("*.py", "foo.py")

# After
from globlin import Glob

glob = Glob.default()
glob.match("*.py", "foo.py")
```

### Modifying matching behavior

Use the `Glob` builder instance instead of passing `Flag` values
to every call:

```python
# Before
from globlin import fnmatch, Flag

fnmatch("src/**/*.py", "src/a/b/foo.py", Flag.GLOB_STAR)
fnmatch("{src,lib}/*.py", "src/foo.py", Flag.BRACE_EXPANSION)

# After
from globlin import Glob

glob = Glob.default().globstar().brace_expansion()
glob.match("src/**/*.py", "src/a/b/foo.py")
glob.match("{src,lib}/*.py", "src/foo.py")
```

### Combining multiple flags

Chain builder methods to replace multiple `Flag` arguments:

```python
# Before
from globlin import fnmatch, Flag

fnmatch("!{a,b}", "c", Flag.NEGATE, Flag.BRACE_EXPANSION)

# After
from globlin import Glob

glob = Glob.default().negate().brace_expansion()
glob.match("!{a,b}", "c")
```

### Using raw flag values

If you composed flags as integers, use
[`Glob.from_flags()`][globlin.Glob.from_flags] with the new
[`Flags`][globlin.Flags] constants:

```python
# Before
from globlin import fnmatch, Flag

fnmatch("src/**/*.py", "src/foo.py", Flag.GLOB_STAR, Flag.ESCAPE)

# After
from globlin import Glob, Flags

glob = Glob.from_flags(Flags.GLOB_STAR | Flags.PATH_SEPARATOR | Flags.ESCAPE)
glob.match("src/**/*.py", "src/foo.py")
```

### Flag name mapping

| `Flag` (v0.2) | Builder method | `Flags` constant |
|---|---|---|
| `Flag.GLOB_STAR` | `.globstar()` | `Flags.GLOB_STAR` |
| `Flag.BRACKET_EXPANSION` | `.bracket_expansion()` | `Flags.BRACKET_EXPANSION` |
| `Flag.BRACE_EXPANSION` | `.brace_expansion()` | `Flags.BRACE_EXPANSION` |
| `Flag.NEGATE` | `.negate()` | `Flags.NEGATE` |
| `Flag.ESCAPE` | `.escape()` | `Flags.ESCAPE` |
| `Flag.PATH_SEPARATOR` | `.path_separator()` | `Flags.PATH_SEPARATOR` |

!!! tip "Reuse `Glob` instances"
    A `Glob` instance captures its configuration once, so you need not pass
    flags per call as `fnmatch()` required. Create one at module level and
    reuse it for all matching calls.
