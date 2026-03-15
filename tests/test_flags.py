# SPDX-FileCopyrightText: 2026 László Vaskó <opensource@accounts.vlaci.email>
#
# SPDX-License-Identifier: EUPL-1.2

from globlin import Glob, flags


def test_constants_are_powers_of_two():
    assert flags.GLOB_STAR == 1 << 0
    assert flags.BRACKET_EXPANSION == 1 << 1
    assert flags.BRACE_EXPANSION == 1 << 2
    assert flags.NEGATE == 1 << 3
    assert flags.ESCAPE == 1 << 4
    assert flags.PATH_SEPARATOR == 1 << 5


def test_all_includes_all():
    assert flags.ALL == (1 << 6) - 1


def test_default_is_posix_fnmatch():
    assert flags.DEFAULT == flags.BRACKET_EXPANSION | flags.ESCAPE


def test_empty_is_zero():
    assert flags.EMPTY == 0


def test_bitwise_composition():
    combined = flags.GLOB_STAR | flags.ESCAPE | flags.PATH_SEPARATOR
    glob = Glob.from_flags(combined)
    assert glob.match("a/**/b", "a/x/b")
    assert glob.match(r"\*", "*")


def test_bitwise_removal():
    reduced = flags.ALL & ~flags.GLOB_STAR
    glob = Glob.from_flags(reduced)
    assert not glob.match("a/**/b", "a/x/y/b")
    assert glob.match("[ab]", "a")  # other features intact
