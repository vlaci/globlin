# SPDX-FileCopyrightText: 2026 László Vaskó <opensource@accounts.vlaci.email>
#
# SPDX-License-Identifier: EUPL-1.2

from globlin import Flags, Glob


def test_constants_are_powers_of_two():
    assert Flags.GLOB_STAR == 1 << 0
    assert Flags.BRACKET_EXPANSION == 1 << 1
    assert Flags.BRACE_EXPANSION == 1 << 2
    assert Flags.NEGATE == 1 << 3
    assert Flags.ESCAPE == 1 << 4
    assert Flags.PATH_SEPARATOR == 1 << 5


def test_all_includes_all():
    assert Flags.ALL == (1 << 6) - 1


def test_default_is_posix_fnmatch():
    assert Flags.DEFAULT == Flags.BRACKET_EXPANSION | Flags.ESCAPE


def test_empty_is_zero():
    assert Flags.EMPTY == 0


def test_bitwise_composition():
    combined = Flags.GLOB_STAR | Flags.ESCAPE | Flags.PATH_SEPARATOR
    glob = Glob.from_flags(combined)
    assert glob.match("a/**/b", "a/x/b")
    assert glob.match(r"\*", "*")


def test_bitwise_removal():
    reduced = Flags.ALL & ~Flags.GLOB_STAR
    glob = Glob.from_flags(reduced)
    assert not glob.match("a/**/b", "a/x/y/b")
    assert glob.match("[ab]", "a")  # other features intact
