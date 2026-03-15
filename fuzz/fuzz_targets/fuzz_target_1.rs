// SPDX-FileCopyrightText: 2025 László Vaskó <opensource@vlaci.email>
// SPDX-License-Identifier: EUPL-1.2

#![no_main]

use libfuzzer_sys::{fuzz_target, Corpus};

#[derive(Clone, Debug, arbitrary::Arbitrary)]
struct GlobInput {
    glob: String,
    path: String,
}

fuzz_target!(|data: GlobInput| -> Corpus {
    let _ = globlin::glob_match(&data.glob, &data.path, globlin::flags::ALL);
    Corpus::Keep
});
