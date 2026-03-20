<!-- SPDX-FileCopyrightText: 2025 László Vaskó <opensource@accounts.vlaci.email>

SPDX-License-Identifier: EUPL-1.2 -->

# Changelog

All notable changes to this project are documented in this file.

## Unreleased

### Added

- `Glob` builder API — composable, immutable configuration replacing the
  deprecated `Flag` enum and `fnmatch()` function
- Documentation site (zensical)

## [0.2.1] — 2026-03-01

### Added

- Benchmarking infrastructure
- Workspace split: Python binding is now a separate crate (`crates/python_binding`)

### Fixed

- Infinite loop when globstar backtracks across brace alternatives
  (e.g. `{/**/0,*}` against `/1`)

## [0.2.0] — 2025-11-14

### Added

- Configuration flags to customize matching behavior:
  globstar, bracket expansion, brace expansion, negation, escape, and
  path separator handling
- Imported [glob-match] algorithm — byte-by-byte matching with backtracking
  based on [Russ Cox's research][glob-research]

## [0.1.1-globlin] — 2025-11-14

### Changed

- Renamed project from `better-fnmatch` to `globlin`

## [0.1.1] — 2025-11-14

### Changed

- Added PyPI deprecation warning directing users to the renamed package

## [0.1.0] — 2025-11-13

Initial release as `better-fnmatch`.

[Unreleased]: https://github.com/vlaci/globlin/compare/v0.2.1...HEAD
[0.2.1]: https://github.com/vlaci/globlin/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/vlaci/globlin/compare/v0.1.1-globlin...v0.2.0
[0.1.1-globlin]: https://github.com/vlaci/globlin/compare/v0.1.1...v0.1.1-globlin
[0.1.1]: https://github.com/vlaci/globlin/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/vlaci/globlin/releases/tag/v0.1.0
[glob-match]: https://crates.io/crates/glob-match
[glob-research]: https://research.swtch.com/glob
