---
icon: lucide/house
---

<!--
SPDX-FileCopyrightText: 2026 László Vaskó <opensource@accounts.vlaci.email>

SPDX-License-Identifier: EUPL-1.2
-->

# globlin

!!! warning "Unreleased"
    This documentation covers the upcoming v0.3 API. For the current stable
    release (v0.2), see the "v0.2 usage" sections and the
    [API reference](api-reference.md#globlin.globlin.fnmatch).

A fast glob pattern matching library for Python. Replaces the standard
library's [`fnmatch`][fnmatch] with a configurable matcher that supports
globstar, brace expansion, and negation.

[fnmatch]: https://docs.python.org/3/library/fnmatch.html#fnmatch.fnmatch

## Features

- **Fast**: Rust powers the core matching engine (BTW)
- **Configurable**: Builder pattern enables exactly the features you need
- **POSIX-compatible defaults**: `Glob.default()` matches `fnmatch(3)` behavior
- **Rich pattern syntax**: Globstar (`**`), bracket expansion (`[a-z]`), brace expansion (`{a,b}`), negation (`!pat`), escape sequences (`\*`), and path separator handling

## Quick start

--8<-- "snippets/installation.md"

Use the `Glob` class:

=== "Current <span class="version-badge">unreleased</span>"
    ```python
    from globlin import Glob
    
    # POSIX fnmatch-like defaults (bracket expansion + escape)
    glob = Glob.default()
    glob.match("foo*", "foobar")      # ✅
    glob.match("[abc]", "b")          # ✅
    
    # Opt in to path-aware matching
    glob = Glob.default().globstar()
    glob.match("src/**/test_*.py", "src/a/b/test_foo.py")  # ✅
    
    # Brace expansion
    glob = Glob.default().brace_expansion()
    glob.match("{src,lib}/*.py", "src/foo.py")  # ✅
    ```

=== "0.2"
    ```python
    from globlin import fnmatch, Flag

    fnmatch("foo*", "foobar")                              # ✅
    fnmatch("src/**/test_*.py", "src/a/b/test_foo.py",
            Flag.GLOB_STAR)                                # ✅
    fnmatch("{src,lib}/*.py", "src/foo.py",
            Flag.BRACE_EXPANSION)                          # ✅
    ```

See the [Guide](guide.md) for more examples and every pattern feature.

## Performance

Rust drives the matching engine, which Python calls through PyO3 with
minimal overhead. The core algorithm follows
[Russ Cox's research on glob matching][glob-research], using byte-by-byte
matching with backtracking.

[glob-research]: https://research.swtch.com/glob
