<!-- SPDX-FileCopyrightText: 2025 László Vaskó <opensource@vlaci.email.com>

SPDX-License-Identifier: EUPL-1.2 -->

# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**globlin** is a Rust glob pattern matching library with Python bindings (via PyO3/maturin). It provides a faster, more featureful `fnmatch` alternative to Python's standard library. The core algorithm is based on [research.swtch.com/glob](https://research.swtch.com/glob) using byte-by-byte matching with backtracking.

License: EUPL-1.2 (REUSE/SPDX compliant — all files need license headers).

## Build & Test Commands

```bash
# Rust
cargo build                              # Build (default-members = globlin only)
cargo build --workspace                  # Build all crates
cargo test                               # Run Rust tests
cargo test -p globlin                    # Run only globlin tests
cargo clippy --all-targets               # Lint
cargo bench                              # Run benchmarks (criterion + divan)

# Python
maturin develop                          # Build and install Python extension in venv
pytest                                   # Run Python tests

# Nix (if available)
nix flake check                          # Full CI: tests, coverage, pre-commit
nix develop                              # Enter dev shell with all tools
```

## Workspace Structure

```
crates/
  globlin/          # Core Rust library (zero runtime deps)
    src/lib.rs      # Single-file implementation (~2600 lines, all logic + tests)
    benches/        # criterion (fnmatch.rs) and divan (glob_match.rs) benchmarks
  python_binding/   # PyO3 cdylib wrapping globlin for Python
python/globlin/     # Python package (type stubs, __init__.py, py.typed)
tests/              # Python pytest suite
```

**Key:** `default-members = ["crates/globlin"]` — bare `cargo` commands only build/test the core crate, not the Python binding.

## Architecture

The entire matching engine lives in `crates/globlin/src/lib.rs`:

- **Entry point:** `glob_match(glob, path, flags) -> bool` converts `&str` to `&[u8]` and delegates to `glob_match_internal`
- **State machine:** `State` struct tracks positions in glob/path plus backtrack points (`Wildcard` for `*`, `Wildcard` for `**`)
- **Wildcard struct** uses `u32` instead of `usize` (measured 10% perf improvement)
- **BraceStack:** Inline stack (max 10 levels) for nested `{a,b}` expansion — no heap allocation
- **Feature flags:** `flags` module defines a `u8` bitfield. `DEFAULT` enables all features. Passing any explicit flag disables all others. The `flag_set!`/`flag_unset!` macros do the checking.

Python bindings (`crates/python_binding/src/lib.rs`) are thin: a `#[pyfunction] fnmatch` that converts Python `Flag` enum values into the Rust `u8` bitfield, plus a `#[pyclass] Flag` enum.

## Flag System

Flags are a `u8` bitfield in `globlin::flags`. When the Python API receives no flags, it uses `DEFAULT` (all features on). When any flag is passed, only those flags are active.

| Flag | Bit | Controls |
|---|---|---|
| `GLOB_STAR` | 0 | `**` globstar matching |
| `BRACKET_EXPANSION` | 1 | `[abc]` / `[a-z]` ranges |
| `BRACE_EXPANSION` | 2 | `{a,b,c}` alternatives |
| `NEGATE` | 3 | `!pattern` negation |
| `ESCAPE` | 4 | `\` escape sequences |
| `NO_PATH` | 5 | Allow `*` and `?` to match `/` |

## Testing Conventions

- **Rust tests** are inline in `lib.rs` under `#[cfg(test)] mod tests`. They cover pattern matching, bracket/brace expansion, globstar, negation, escapes, captures, and fuzz-discovered edge cases.
- **Python tests** in `tests/test_fnmatch.py` use `pytest.mark.parametrize` extensively, testing both matching and non-matching cases for each flag.

## Commit Conventions

- **Scoped prefix** for changes within a single area: `scope: lowercase message` — e.g. `ci: export pytest coverage data`, `glob: add configuration flags`
- **No prefix** for cross-cutting or top-level changes — e.g. `Split out python binding to a separate crate`
- Lowercase message after the colon
- Scopes used: `glob` (core crate), `ci` (GitHub Actions / CI)

## Python Build Details

- Built with **maturin** (configured in `pyproject.toml`)
- ABI3 wheels targeting Python 3.9+ (`pyo3/abi3-py39`)
- Type stubs in `python/globlin/globlin.pyi`
- Linting: `ruff` (extensive rule set in pyproject.toml), `pyright` strict mode
- Docstring convention: Google style
