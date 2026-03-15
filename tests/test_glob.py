# SPDX-FileCopyrightText: 2026 László Vaskó <opensource@accounts.vlaci.email>
#
# SPDX-License-Identifier: EUPL-1.2

import pytest

from globlin import Flags, Glob


def test_default_returns_glob():
    glob = Glob.default()
    assert isinstance(glob, Glob)


def test_default_matches_posix_fnmatch():
    glob = Glob.default()
    assert glob.match("[ab]", "a")  # bracket expansion
    assert glob.match(r"\*", "*")  # escape
    # POSIX fnmatch defaults: wildcards match /
    assert glob.match("a*b", "a/c/b")
    # Extensions not enabled by default
    assert glob.match("{a,b}", "{a,b}")  # no brace expansion (literal)
    assert glob.match("!a", "!a")  # no negate (literal)


def test_empty_disables_all_features():
    glob = Glob.empty()
    assert glob.match("[ab]", "[ab]")  # no bracket expansion
    assert glob.match("{a,b}", "{a,b}")  # no brace expansion
    assert glob.match("a*b", "a/c/b")  # wildcards match /


def test_enable_globstar():
    glob = Glob.default().globstar()
    assert glob.match("a/**/b", "a/x/y/b")
    assert not glob.match("a/*/b", "a/x/y/b")  # single * doesn't cross /


def test_enable_path_separator():
    glob = Glob.default().path_separator()
    assert not glob.match("a*b", "a/c/b")  # * does not match /
    assert not glob.match("a?b", "a/b")  # ? does not match /


def test_disable_path_separator():
    glob = Glob.default().path_separator().no_path_separator()
    assert glob.match("a*b", "a/c/b")  # * matches / again


def test_empty_enable_one():
    glob = Glob.empty().globstar()
    assert glob.match("a/**/b", "a/x/b")
    assert not glob.match("a/*/b", "a/x/y/b")  # globstar implies path_separator


def test_chaining_returns_new_glob():
    base = Glob.default()
    modified = base.no_escape()
    # base should be unaffected
    assert Glob.default().match(r"\*", "*")
    assert not modified.match(r"\*", "*")


@pytest.mark.parametrize(
    "pattern,value,flags",
    [
        pytest.param("a/**/b", "a/path/b", Flags.PATH_SEPARATOR, id="no-globstar"),
        pytest.param(
            "a/**/b",
            "a/long/path/to/b",
            Flags.PATH_SEPARATOR | Flags.GLOB_STAR,
            id="globstar",
        ),
        pytest.param("[ab]", "[ab]", Flags.EMPTY, id="no-bracket-expansion"),
        pytest.param("[ab]", "a", Flags.BRACKET_EXPANSION, id="bracket-expansion"),
        pytest.param(
            "[a-z]", "c", Flags.BRACKET_EXPANSION, id="bracket-expansion-range"
        ),
        pytest.param("[a-z]", "[a-z]", Flags.EMPTY, id="no-bracket-expansion-range"),
        pytest.param("{a,b?c}", "{a,bzc}", Flags.EMPTY, id="no-brace-expansion"),
        pytest.param("{a,b?c}", "bzc", Flags.BRACE_EXPANSION, id="brace-expansion"),
        pytest.param("!a", "!a", Flags.EMPTY, id="no-negate"),
        pytest.param("!a", "c", Flags.NEGATE, id="negate"),
        pytest.param(r"\*", r"\path", Flags.EMPTY, id="no-escape"),
        pytest.param(r"\*", "*", Flags.ESCAPE, id="escape"),
        pytest.param(
            "a/*/path", "a/very/long/path", Flags.DEFAULT, id="no-path-separator"
        ),
        pytest.param(
            "a?path", "a/path", Flags.DEFAULT, id="no-path-separator-question-mark"
        ),
    ],
)
def test_matching_pattern_from_flags(pattern: str, value: str, flags: int):
    glob = Glob.from_flags(flags)
    assert glob.match(pattern, value)


@pytest.mark.parametrize(
    "pattern,value,flags",
    [
        pytest.param("a/**/b", "a/long/path/b", Flags.PATH_SEPARATOR, id="no-globstar"),
        pytest.param(
            "a/l**o/b",
            "a/long/path/to/b",
            Flags.PATH_SEPARATOR | Flags.GLOB_STAR,
            id="globstar",
        ),
        pytest.param(r"[ab]", "a", Flags.EMPTY, id="no-bracket-expansion"),
        pytest.param(r"[ab]", "[ab]", Flags.BRACKET_EXPANSION, id="bracket-expansion"),
        pytest.param("{a,b?c}", "a", Flags.EMPTY, id="no-brace-expansion"),
        pytest.param("{a,b?c}", "{a,bzc}", Flags.BRACE_EXPANSION, id="brace-expansion"),
        pytest.param("!a", "c", Flags.EMPTY, id="no-negate"),
        pytest.param("!a", "a", Flags.NEGATE, id="negate"),
        pytest.param(r"\*", "*", Flags.EMPTY, id="no-escape"),
        pytest.param(r"\*", "path", Flags.ESCAPE, id="escape"),
        pytest.param(
            "a/*/path",
            "a/very/long/path",
            Flags.PATH_SEPARATOR,
            id="path-separator",
        ),
        pytest.param(
            "a?path", "a/path", Flags.PATH_SEPARATOR, id="path-separator-question-mark"
        ),
    ],
)
def test_not_matching_pattern_from_flags(pattern: str, value: str, flags: int):
    glob = Glob.from_flags(flags)
    assert not glob.match(pattern, value)


def test_error_on_globstar_no_path_separator():
    with pytest.raises(ValueError, match="globstar is enabled without path separator"):
        Glob.default().globstar().no_path_separator()

    with pytest.raises(ValueError, match="globstar is enabled without path separator"):
        Glob.from_flags(Flags.GLOB_STAR)


def test_from_flags_invalid():
    with pytest.raises(ValueError, match="invalid flags value"):
        Glob.from_flags(128)


def test_from_flags_negative():
    with pytest.raises(ValueError, match="invalid flags value"):
        Glob.from_flags(-1)


def test_repr():
    r = repr(Glob.default())
    assert "BRACKET_EXPANSION" in r
    assert "ESCAPE" in r
    assert "Glob(" in r


def test_repr_empty():
    assert repr(Glob.empty()) == "Glob(EMPTY)"
