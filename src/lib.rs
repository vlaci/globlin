// SPDX-FileCopyrightText: 2025 László Vaskó <opensource@vlaci.email.com>
//
// SPDX-License-Identifier: EUPL-1.2

#[pyo3::pymodule]
mod globlin {
    use glob_match::glob_match;
    use pyo3::prelude::*;
    #[pyfunction]
    fn fnmatch(pattern: &str, value: &str) -> PyResult<bool> {
        Ok(glob_match(pattern, value))
    }

    #[cfg(test)]
    mod test {
        use super::*;

        #[test]
        fn test_python_api() {
            Python::initialize();

            Python::attach(|_py| {
                assert!(fnmatch("foo*", "foobar").unwrap());
            })
        }
    }
}
