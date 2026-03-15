---
name: verify
description: Run full verification suite (check, test, clippy, pre-commit)
---
<!--
SPDX-FileCopyrightText: 2025 László Vaskó <opensource@accounts.vlaci.email>

SPDX-License-Identifier: EUPL-1.2
-->

Run all verification checks sequentially. Stop at first failure:

1. `cargo check`
2. `cargo test`
3. `cargo clippy -- -D warnings`
4. `pytest`
5. `prek run --all-files`

Report results concisely. If any step fails, show the error and suggest a fix.
