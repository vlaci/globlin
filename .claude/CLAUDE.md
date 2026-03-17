<!--
SPDX-FileCopyrightText: 2025 László Vaskó <opensource@accounts.vlaci.email>

SPDX-License-Identifier: EUPL-1.2
-->

# Globlin

A Rust glob pattern matching library with Python bindings (via PyO3/maturin). Provides a faster, more featureful `fnmatch` alternative to Python's standard library. The core algorithm is based on <https://research.swtch.com/glob> using byte-by-byte matching with backtracking.

- Repository: <https://github.com/vlaci/globlin>
- License: EUPL-1.2 (primary), MIT (original glob-match code). REUSE-compliant, SPDX headers on all files.

## Workspace Structure

```
crates/
  globlin/          # Core Rust library (zero runtime deps)
    src/lib.rs      # Single-file implementation (~2600 lines, all logic + tests)
    benches/        # criterion (fnmatch.rs) and divan (glob_match.rs) benchmarks
  python_binding/   # PyO3 cdylib wrapping globlin for Python
python/globlin/     # Python package (type stubs, __init__.py, py.typed)
tests/              # Python pytest suite
fuzz/               # cargo-fuzz targets
```

**Key:** `default-members = ["crates/globlin"]` — bare `cargo` commands only build/test the core crate, not the Python binding.

## Architecture

The entire matching engine lives in `crates/globlin/src/lib.rs`:

- **Entry point:** `glob_match(glob, path, flags) -> bool` converts `&str` to `&[u8]` and delegates to `glob_match_internal`
- **State machine:** `State` struct tracks positions in glob/path plus backtrack points (`Wildcard` for `*`, `Wildcard` for `**`)
- **Wildcard struct** uses `u32` instead of `usize` (measured 10% perf improvement)
- **BraceStack:** Inline stack (max 10 levels) for nested `{a,b}` expansion — no heap allocation
- **Feature flags:** `flags` module defines a `u8` bitfield. `DEFAULT` enables POSIX fnmatch-like features (`BRACKET_EXPANSION | ESCAPE`). `ALL` enables all features (bits 0-5). The `flag_set!` macro checks individual bits.

Python bindings (`crates/python_binding/src/lib.rs`) provide:
- `Glob` — primary API. `Glob.default()` starts with POSIX fnmatch-like defaults (bracket expansion + escape). Builder methods (e.g. `.globstar()`, `.no_escape()`) clone and return a new `Glob`. `.match(pattern, value)` performs matching.
- `flags` submodule — low-level `u8` constants for bitwise composition, used via `Glob.from_flags()`.
- Deprecated `Flag` enum and `fnmatch` function — backward-compatible, emit `DeprecationWarning`.

## Key Design Details

- **ABI3**: built with `pyo3/abi3-py39` for broad Python compatibility from a single wheel.
- **maturin-import-hook**: auto-rebuilds the Rust extension on Python import during development — no manual `maturin develop` needed.
- **Google-style docstrings** in Python, `pyright` strict mode, `ruff` with extensive rule set.

## Flag System

Flags are a `u8` bitfield in `globlin::flags`. `DEFAULT` includes only POSIX fnmatch-like features (`BRACKET_EXPANSION | ESCAPE`). `ALL` includes all flags (bits 0-5). The primary Python API is the `Glob` class; the raw bitfield is exposed via `globlin.flags` for advanced use.

| Flag | Bit | Controls |
|---|---|---|
| `GLOB_STAR` | 0 | `**` globstar matching (requires `PATH_SEPARATOR`) |
| `BRACKET_EXPANSION` | 1 | `[abc]` / `[a-z]` ranges |
| `BRACE_EXPANSION` | 2 | `{a,b,c}` alternatives |
| `NEGATE` | 3 | `!pattern` negation |
| `ESCAPE` | 4 | `\` escape sequences |
| `PATH_SEPARATOR` | 5 | Treat `/` as path separator (`*` and `?` do not match `/`) |

## Build Commands

| Command | Purpose |
|---------|---------|
| `cargo build` | Build core crate only (default-members) |
| `cargo build --workspace` | Build all crates |
| `cargo test` | Run Rust tests (core crate only) |
| `cargo test -p globlin` | Run only globlin tests |
| `cargo clippy --all-targets` | Lint Rust |
| `cargo fmt` | Format Rust |
| `cargo bench` | Run benchmarks (criterion + divan) |
| `pytest` | Run all Python tests |
| `pytest tests/test_fnmatch.py::test_matching_patterns` | Run a single test |
| `maturin develop` | Build Python extension (usually not needed — import hook handles it) |
| `ruff check .` | Lint Python |
| `ruff format .` | Format Python |
| `pyright` | Type-check Python (strict mode) |
| `prek run --all-files` | Run all pre-commit checks |

## Testing Conventions

- **Rust tests** are inline in `lib.rs` under `#[cfg(test)] mod tests`. They cover pattern matching, bracket/brace expansion, globstar, negation, escapes, captures, and fuzz-discovered edge cases.
- **Python tests** in `tests/` (`test_fnmatch.py`, `test_glob.py`, `test_flags.py`) use `pytest.mark.parametrize` extensively, testing both matching and non-matching cases for each flag/feature.

## Commit Conventions

- **Scoped prefix** for changes within a single area: `scope: lowercase message` — e.g. `ci: export pytest coverage data`, `glob: add configuration flags`
- **No prefix** for cross-cutting or top-level changes
- Lowercase message after the colon
- Scopes used: `glob` (core crate), `ci` (GitHub Actions / CI)

## Workflow

<!--REUSE-IgnoreStart-->
- All files must have SPDX license headers (REUSE-compliant)
- REUSE copyright line: `SPDX-FileCopyrightText: <year> László Vaskó <opensource@accounts.vlaci.email>`
- REUSE license line: `SPDX-License-Identifier: EUPL-1.2`
<!--REUSE-IgnoreEnd-->
- **Before starting any task**, run the full test suite (`cargo test` and `pytest`). If any pre-existing tests are failing, fix them first and commit the fix as a separate commit before proceeding with the actual task.
- Run `cargo check`, `cargo test`, `pytest`, and `cargo clippy` before claiming work is done.
- Run `prek run --all-files` to verify pre-commit hooks pass.
- Review diffs before committing. Check for: coding convention violations, trivial/unnecessary comments, clippy warnings, unused code.
- Present the commit message for user review before committing.
- Add references (dependencies, techniques, APIs) as markdown footer links in commit messages (e.g. `[Crane]: https://crane.dev/`).
- No intermediate commits during implementation unless the user requests them.
- Keep `CLAUDE.md` up to date: when adding modules, dependencies, or changing architecture, update the relevant files in the same commit.
