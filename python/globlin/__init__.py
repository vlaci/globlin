# type: ignore
"""Globlin: fast glob pattern matching."""

# SPDX-FileCopyrightText: 2025 László Vaskó <opensource@accounts.vlaci.email>
#
# SPDX-License-Identifier: EUPL-1.2

import enum

from .globlin import Flag as Flag
from .globlin import Glob as Glob
from .globlin import _flags
from .globlin import fnmatch as fnmatch


class Flags(enum.IntFlag):
    """Low-level flag constants for bitwise composition."""

    EMPTY = _flags.EMPTY
    GLOB_STAR = _flags.GLOB_STAR
    BRACKET_EXPANSION = _flags.BRACKET_EXPANSION
    BRACE_EXPANSION = _flags.BRACE_EXPANSION
    NEGATE = _flags.NEGATE
    ESCAPE = _flags.ESCAPE
    PATH_SEPARATOR = _flags.PATH_SEPARATOR
    ALL = _flags.ALL
    DEFAULT = _flags.DEFAULT
