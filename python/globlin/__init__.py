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
    """No features enabled.

    *New in version 0.3.*
    """

    GLOB_STAR = _flags.GLOB_STAR
    """Enable ``**`` globstar matching.

    *New in version 0.3.*
    """

    BRACKET_EXPANSION = _flags.BRACKET_EXPANSION
    """Enable ``[abc]`` / ``[a-z]`` bracket expansion.

    *New in version 0.3.*
    """

    BRACE_EXPANSION = _flags.BRACE_EXPANSION
    """Enable ``{a,b,c}`` brace expansion.

    *New in version 0.3.*
    """

    NEGATE = _flags.NEGATE
    """Enable ``!pattern`` negation.

    *New in version 0.3.*
    """

    ESCAPE = _flags.ESCAPE
    r"""Enable ``\`` escape sequences.

    *New in version 0.3.*
    """

    PATH_SEPARATOR = _flags.PATH_SEPARATOR
    r"""Treat ``/`` as path separator — ``*`` and ``?`` do not match ``/``.

    *New in version 0.3.*
    """

    ALL = _flags.ALL
    """All features enabled.

    *New in version 0.3.*
    """

    DEFAULT = _flags.DEFAULT
    """POSIX fnmatch-like defaults (``BRACKET_EXPANSION | ESCAPE``).

    *New in version 0.3.*
    """
