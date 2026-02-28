// SPDX-FileCopyrightText: 2025 László Vaskó <opensource@vlaci.email>
// SPDX-License-Identifier: EUPL-1.2

fn main() {
    globlin::glob_match(
        "{/**/0,*", // foo
        "/1",
        globlin::flags::DEFAULT,
    );
}
