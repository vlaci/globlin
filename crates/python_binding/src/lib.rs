// SPDX-FileCopyrightText: 2025 László Vaskó <opensource@accounts.vlaci.email>
//
// SPDX-License-Identifier: EUPL-1.2
#[pyo3::pymodule]
mod globlin {
    use pyo3::prelude::*;
    use pyo3::types::PyTuple;

    #[pyfunction]
    #[pyo3(signature = (pattern, value, *flags))]
    fn fnmatch(pattern: &str, value: &str, flags: &Bound<'_, PyTuple>) -> PyResult<bool> {
        let mut glob_flags = if flags.is_empty() {
            ::globlin::flags::DEFAULT
        } else {
            ::globlin::flags::EMPTY
        };
        for flag in flags.iter() {
            let flag = flag.extract::<Flag>()?;
            match flag {
                Flag::EMPTY => glob_flags |= ::globlin::flags::EMPTY,
                Flag::GLOB_STAR => glob_flags |= ::globlin::flags::GLOB_STAR,
                Flag::BRACKET_EXPANSION => glob_flags |= ::globlin::flags::BRACKET_EXPANSION,
                Flag::BRACE_EXPANSION => glob_flags |= ::globlin::flags::BRACE_EXPANSION,
                Flag::NEGATE => glob_flags |= ::globlin::flags::NEGATE,
                Flag::ESCAPE => glob_flags |= ::globlin::flags::ESCAPE,
                Flag::NO_PATH => glob_flags |= ::globlin::flags::NO_PATH,
            }
        }
        Ok(::globlin::glob_match(pattern, value, glob_flags))
    }

    #[allow(non_camel_case_types)]
    #[allow(clippy::upper_case_acronyms)]
    #[pyclass(eq, from_py_object)]
    #[derive(Clone, PartialEq)]
    enum Flag {
        EMPTY,
        GLOB_STAR,
        BRACKET_EXPANSION,
        BRACE_EXPANSION,
        NEGATE,
        ESCAPE,
        NO_PATH,
    }

    #[cfg(test)]
    mod test {
        use super::*;

        #[test]
        fn test_python_api() {
            Python::initialize();

            Python::attach(|py| {
                assert!(fnmatch("foo*", "foobar", &PyTuple::empty(py)).unwrap());
            })
        }
    }
}
