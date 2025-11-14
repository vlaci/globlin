# SPDX-FileCopyrightText: 2025 László Vaskó <opensource@vlaci.email.com>
#
# SPDX-License-Identifier: EUPL-1.2

import pytest

import globlin


@pytest.mark.parametrize(
    "pattern,value,match",
    [
        ("*", "*", True),
        (r"\*", "*", True),
        (r"\*", r"\*", False),
        (r"\\\*", r"\*", True),
        ("?", "?", True),
        (r"\?", "?", True),
        (r"\?", r"\?", False),
        (r"\\\?", r"\?", True),
        ("foo*", "foobar", True),
        ("foo*", "barfoo", False),
        ("foo?", "foob", True),
        ("foo?", "fooba", False),
    ],
)
def test_globlin(pattern: str, value: str, match: bool):
    assert globlin.fnmatch(pattern, value) is match
