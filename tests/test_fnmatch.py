# pyright: reportDeprecated=false
# SPDX-FileCopyrightText: 2025 László Vaskó <opensource@accounts.vlaci.email>
#
# SPDX-License-Identifier: EUPL-1.2

import warnings

import pytest

from globlin import Flag, fnmatch


@pytest.mark.parametrize(
    "pattern,value",
    [
        ("*", "*"),
        (r"\*", "*"),
        (r"\\\*", r"\*"),
        ("?", "?"),
        (r"\?", "?"),
        (r"\\\?", r"\?"),
        ("foo*", "foobar"),
        ("foo?", "foob"),
    ],
)
def test_matching_patterns(pattern: str, value: str):
    assert fnmatch(pattern, value)


@pytest.mark.parametrize(
    "pattern,value",
    [
        (r"\*", r"\*"),
        (r"\?", r"\?"),
        ("foo*", "barfoo"),
        ("foo?", "fooba"),
    ],
)
def test_not_matching_patterns(pattern: str, value: str):
    assert not fnmatch(pattern, value)


@pytest.mark.parametrize(
    "pattern,value,flag",
    [
        pytest.param("a/**/b", "a/path/b", Flag.EMPTY, id="no-globstar"),
        pytest.param("a/**/b", "a/long/path/to/b", Flag.GLOB_STAR, id="globstar"),
        pytest.param("[ab]", "[ab]", Flag.EMPTY, id="no-bracket-expansion"),
        pytest.param("[ab]", "a", Flag.BRACKET_EXPANSION, id="bracket-expansion"),
        pytest.param(
            "[a-z]", "c", Flag.BRACKET_EXPANSION, id="bracket-expansion-range"
        ),
        pytest.param("[a-z]", "[a-z]", Flag.EMPTY, id="no-bracket-expansion-range"),
        pytest.param("{a,b?c}", "{a,bzc}", Flag.EMPTY, id="no-brace-expansion"),
        pytest.param("{a,b?c}", "bzc", Flag.BRACE_EXPANSION, id="brace-expansion"),
        pytest.param("!a", "!a", Flag.EMPTY, id="no-negate"),
        pytest.param("!a", "c", Flag.NEGATE, id="negate"),
        pytest.param(r"\*", r"\path", Flag.EMPTY, id="no-escape"),
        pytest.param(r"\*", "*", Flag.ESCAPE, id="escape"),
        pytest.param(
            "a/*/path", "a/very/long/path", Flag.NO_PATH, id="no-path-asterisk"
        ),
        pytest.param("a?path", "a/path", Flag.NO_PATH, id="no-path-question-mark"),
    ],
)
def test_matching_pattern_with_flags(pattern: str, value: str, flag: Flag):
    assert fnmatch(pattern, value, flag)


@pytest.mark.parametrize(
    "pattern,value,flag",
    [
        pytest.param("a/**/b", "a/long/path/b", Flag.EMPTY, id="no-globstar"),
        pytest.param("a/l**o/b", "a/long/path/to/b", Flag.GLOB_STAR, id="globstar"),
        pytest.param(r"[ab]", "a", Flag.EMPTY, id="no-bracket-expansion"),
        pytest.param(r"[ab]", "[ab]", Flag.BRACKET_EXPANSION, id="bracket-expansion"),
        pytest.param("{a,b?c}", "a", Flag.EMPTY, id="no-brace-expansion"),
        pytest.param("{a,b?c}", "{a,bzc}", Flag.BRACE_EXPANSION, id="brace-expansion"),
        pytest.param("!a", "c", Flag.EMPTY, id="no-negate"),
        pytest.param("!a", "a", Flag.NEGATE, id="negate"),
        pytest.param(r"\*", "*", Flag.EMPTY, id="no-escape"),
        pytest.param(r"\*", "path", Flag.ESCAPE, id="escape"),
        pytest.param("a/*/path", "a/very/long/path", Flag.EMPTY, id="path-asterisk"),
        pytest.param("a?path", "a/path", Flag.EMPTY, id="path-question-mark"),
    ],
)
def test_not_matching_pattern_with_flags(pattern: str, value: str, flag: Flag):
    assert not fnmatch(pattern, value, flag)


def test_invalid_flags():
    with pytest.raises(TypeError):
        fnmatch("foo", "bar", "not a flag")  # type: ignore


def test_old_fnmatch_with_flags_warns():
    with pytest.deprecated_call():
        fnmatch("foo*", "foobar", Flag.GLOB_STAR)


def test_old_fnmatch_no_flags_no_warning():
    warnings.simplefilter("error")
    fnmatch("foo*", "foobar")
