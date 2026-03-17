// SPDX-FileCopyrightText: 2025 László Vaskó <opensource@accounts.vlaci.email>
//
// SPDX-License-Identifier: EUPL-1.2
#[pyo3::pymodule]
mod globlin {
    use pyo3::prelude::*;
    use pyo3::types::PyTuple;

    #[pymodule]
    mod _flags {
        use pyo3::prelude::*;

        #[pymodule_init]
        fn init(m: &Bound<'_, PyModule>) -> PyResult<()> {
            m.add("EMPTY", ::globlin::flags::EMPTY)?;
            m.add("GLOB_STAR", ::globlin::flags::GLOB_STAR)?;
            m.add("BRACKET_EXPANSION", ::globlin::flags::BRACKET_EXPANSION)?;
            m.add("BRACE_EXPANSION", ::globlin::flags::BRACE_EXPANSION)?;
            m.add("NEGATE", ::globlin::flags::NEGATE)?;
            m.add("ESCAPE", ::globlin::flags::ESCAPE)?;
            m.add("PATH_SEPARATOR", ::globlin::flags::PATH_SEPARATOR)?;
            m.add("ALL", ::globlin::flags::ALL)?;
            m.add("DEFAULT", ::globlin::flags::DEFAULT)?;
            Ok(())
        }
    }

    #[pyclass(skip_from_py_object)]
    #[derive(Clone)]
    struct Glob {
        flags: u8,
    }

    #[pymethods]
    impl Glob {
        #[staticmethod]
        fn default() -> Self {
            Glob {
                flags: ::globlin::flags::DEFAULT,
            }
        }

        #[staticmethod]
        fn empty() -> Self {
            Glob {
                flags: ::globlin::flags::EMPTY,
            }
        }

        #[staticmethod]
        fn from_flags(flags: i32) -> PyResult<Self> {
            let max_valid = (1u8 << 6) - 1;
            if flags < 0 || flags > max_valid as i32 {
                return Err(pyo3::exceptions::PyValueError::new_err(format!(
                    "invalid flags value: {flags}, must be 0-{max_valid}"
                )));
            }
            let flags = flags as u8;
            check_globstar_path_separator(flags)?;
            Ok(Glob { flags })
        }

        fn globstar(&self) -> Self {
            Glob {
                flags: self.flags | ::globlin::flags::GLOB_STAR | ::globlin::flags::PATH_SEPARATOR,
            }
        }

        fn no_globstar(&self) -> Self {
            Glob {
                flags: self.flags & !::globlin::flags::GLOB_STAR,
            }
        }

        fn bracket_expansion(&self) -> Self {
            Glob {
                flags: self.flags | ::globlin::flags::BRACKET_EXPANSION,
            }
        }

        fn no_bracket_expansion(&self) -> Self {
            Glob {
                flags: self.flags & !::globlin::flags::BRACKET_EXPANSION,
            }
        }

        fn brace_expansion(&self) -> Self {
            Glob {
                flags: self.flags | ::globlin::flags::BRACE_EXPANSION,
            }
        }

        fn no_brace_expansion(&self) -> Self {
            Glob {
                flags: self.flags & !::globlin::flags::BRACE_EXPANSION,
            }
        }

        fn negate(&self) -> Self {
            Glob {
                flags: self.flags | ::globlin::flags::NEGATE,
            }
        }

        fn no_negate(&self) -> Self {
            Glob {
                flags: self.flags & !::globlin::flags::NEGATE,
            }
        }

        fn escape(&self) -> Self {
            Glob {
                flags: self.flags | ::globlin::flags::ESCAPE,
            }
        }

        fn no_escape(&self) -> Self {
            Glob {
                flags: self.flags & !::globlin::flags::ESCAPE,
            }
        }

        fn path_separator(&self) -> Self {
            Glob {
                flags: self.flags | ::globlin::flags::PATH_SEPARATOR,
            }
        }

        fn no_path_separator(&self) -> PyResult<Self> {
            let flags = self.flags & !::globlin::flags::PATH_SEPARATOR;
            check_globstar_path_separator(flags)?;
            Ok(Glob { flags })
        }

        #[pyo3(name = "match", signature = (pattern, value))]
        fn match_(&self, pattern: &str, value: &str) -> bool {
            ::globlin::glob_match(pattern, value, self.flags)
        }

        fn __repr__(&self) -> String {
            let mut parts = Vec::new();
            if self.flags & ::globlin::flags::GLOB_STAR != 0 {
                parts.push("GLOB_STAR");
            }
            if self.flags & ::globlin::flags::BRACKET_EXPANSION != 0 {
                parts.push("BRACKET_EXPANSION");
            }
            if self.flags & ::globlin::flags::BRACE_EXPANSION != 0 {
                parts.push("BRACE_EXPANSION");
            }
            if self.flags & ::globlin::flags::NEGATE != 0 {
                parts.push("NEGATE");
            }
            if self.flags & ::globlin::flags::ESCAPE != 0 {
                parts.push("ESCAPE");
            }
            if self.flags & ::globlin::flags::PATH_SEPARATOR != 0 {
                parts.push("PATH_SEPARATOR");
            }
            if parts.is_empty() {
                "Glob(EMPTY)".to_string()
            } else {
                format!("Glob({})", parts.join(" | "))
            }
        }
    }

    fn check_globstar_path_separator(flags: u8) -> PyResult<()> {
        if flags & ::globlin::flags::GLOB_STAR != 0 && flags & ::globlin::flags::PATH_SEPARATOR == 0
        {
            return Err(pyo3::exceptions::PyValueError::new_err(
                "globstar is enabled without path separator; ** would behave like *",
            ));
        }
        Ok(())
    }

    #[pyfunction]
    #[pyo3(signature = (pattern, value, *flags))]
    fn fnmatch(
        py: Python<'_>,
        pattern: &str,
        value: &str,
        flags: &Bound<'_, PyTuple>,
    ) -> PyResult<bool> {
        let mut glob_flags = if flags.is_empty() {
            ::globlin::flags::ALL
        } else {
            PyErr::warn(
                py,
                &py.get_type::<pyo3::exceptions::PyDeprecationWarning>(),
                c"passing Flag arguments to fnmatch is deprecated, use Glob class instead.\n\
                See: https://vlaci.github.io/globlin/migration/#migrating-from-v02",
                1,
            )?;
            // Start with PATH_SEPARATOR set to preserve old behavior where
            // path separators were respected by default (absence of NO_PATH
            // meant flag_unset!(flags, NO_PATH) = true).
            ::globlin::flags::PATH_SEPARATOR
        };
        for flag in flags.iter() {
            let flag = flag.extract::<Flag>()?;
            match flag {
                Flag::EMPTY => {}
                Flag::GLOB_STAR => glob_flags |= ::globlin::flags::GLOB_STAR,
                Flag::BRACKET_EXPANSION => glob_flags |= ::globlin::flags::BRACKET_EXPANSION,
                Flag::BRACE_EXPANSION => glob_flags |= ::globlin::flags::BRACE_EXPANSION,
                Flag::NEGATE => glob_flags |= ::globlin::flags::NEGATE,
                Flag::ESCAPE => glob_flags |= ::globlin::flags::ESCAPE,
                Flag::NO_PATH => glob_flags &= !::globlin::flags::PATH_SEPARATOR,
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
                assert!(fnmatch(py, "foo*", "foobar", &PyTuple::empty(py)).unwrap());
            })
        }

        #[test]
        fn test_glob_default() {
            assert_eq!(Glob::default().flags, ::globlin::flags::DEFAULT);
        }

        #[test]
        fn test_glob_empty() {
            assert_eq!(Glob::empty().flags, ::globlin::flags::EMPTY);
        }

        #[test]
        fn test_glob_builder_methods() {
            let glob = Glob::empty().globstar();
            assert_eq!(
                glob.flags,
                ::globlin::flags::GLOB_STAR | ::globlin::flags::PATH_SEPARATOR
            );
            let glob = glob.no_globstar();
            assert_eq!(glob.flags, ::globlin::flags::PATH_SEPARATOR);

            let glob = Glob::empty().bracket_expansion();
            assert_eq!(glob.flags, ::globlin::flags::BRACKET_EXPANSION);
            let glob = glob.no_bracket_expansion();
            assert_eq!(glob.flags, 0);

            let glob = glob.brace_expansion();
            assert_eq!(glob.flags, ::globlin::flags::BRACE_EXPANSION);
            let glob = glob.no_brace_expansion();
            assert_eq!(glob.flags, 0);

            let glob = glob.negate();
            assert_eq!(glob.flags, ::globlin::flags::NEGATE);
            let glob = glob.no_negate();
            assert_eq!(glob.flags, 0);

            let glob = glob.escape();
            assert_eq!(glob.flags, ::globlin::flags::ESCAPE);
            let glob = glob.no_escape();
            assert_eq!(glob.flags, 0);

            let glob = glob.path_separator();
            assert_eq!(glob.flags, ::globlin::flags::PATH_SEPARATOR);
            let glob = glob.no_path_separator().unwrap();
            assert_eq!(glob.flags, 0);
        }

        #[test]
        fn test_glob_from_flags() {
            let glob = Glob::from_flags(
                (::globlin::flags::GLOB_STAR | ::globlin::flags::PATH_SEPARATOR) as i32,
            )
            .unwrap();
            assert_eq!(
                glob.flags,
                ::globlin::flags::GLOB_STAR | ::globlin::flags::PATH_SEPARATOR
            );
        }

        #[test]
        fn test_glob_from_flags_invalid() {
            assert!(Glob::from_flags(128).is_err());
        }

        #[test]
        fn test_glob_match() {
            let glob = Glob::default();
            assert!(glob.match_("foo*", "foobar"));
            assert!(!glob.match_("foo*", "barfoo"));
        }
    }
}
