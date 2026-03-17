# pyright: reportDeprecated=false
# SPDX-FileCopyrightText: 2026 László Vaskó <opensource@accounts.vlaci.email>
#
# SPDX-License-Identifier: EUPL-1.2

import enum

from typing_extensions import Self, deprecated

class Glob:
    """Glob pattern matcher with configurable features.

    Use ``Glob.default()`` for POSIX fnmatch-like matching (bracket expansion
    and escape sequences enabled), or ``Glob.empty()`` for a minimal
    configuration. Chain builder methods to enable or disable features, then
    call ``match()`` to test patterns.

    Examples:
        >>> from globlin import Glob
        >>> glob = Glob.default()
        >>> glob.match("*.py", "foo.py")
        True
        >>> glob.match("*.py", "foo.txt")
        False

    *New in version 0.3.*
    """

    @classmethod
    def default(cls) -> Glob:
        r"""Create a glob with POSIX fnmatch-like defaults.

        Enables bracket expansion and escape sequences. Additional
        features like globstar can be added via builder methods.

        Examples:
            >>> glob = Glob.default()
            >>> glob.match("[abc]", "b")
            True
            >>> glob.match(r"\*", "*")
            True

        *New in version 0.3.*
        """

    @classmethod
    def empty(cls) -> Glob:
        """Create a glob with no features enabled.

        Only ``*`` and ``?`` wildcards work.

        Examples:
            >>> glob = Glob.empty()
            >>> glob.match("*.py", "foo.py")
            True
            >>> glob.match("[abc]", "b")
            False

        *New in version 0.3.*
        """

    @classmethod
    def from_flags(cls, flags: int) -> Glob:
        """Create a glob from raw bitflags.

        Args:
            flags: Bitwise combination of constants from ``Flags``.

        Raises:
            ValueError: If any bits outside the valid range are set.

        Examples:
            >>> from globlin import Flags
            >>> glob = Glob.from_flags(Flags.GLOB_STAR | Flags.PATH_SEPARATOR | Flags.ESCAPE)
            >>> glob.match("src/**/*.py", "src/a/b/foo.py")
            True

        *New in version 0.3.*
        """

    def globstar(self) -> Self:
        """Enable ``**`` globstar matching.

        Implies ``path_separator()`` since globstar is only meaningful when
        ``/`` is treated as a path separator.

        Examples:
            >>> glob = Glob.default().globstar()
            >>> glob.match("src/**/*.py", "src/a/b/foo.py")
            True
            >>> glob.match("src/**/*.py", "src/foo.py")
            True

        *New in version 0.3.*
        """

    def no_globstar(self) -> Self:
        """Disable ``**`` globstar matching.

        *New in version 0.3.*
        """

    def bracket_expansion(self) -> Self:
        """Enable ``[abc]`` / ``[a-z]`` bracket expansion.

        Examples:
            >>> glob = Glob.empty().bracket_expansion()
            >>> glob.match("[a-z]", "m")
            True
            >>> glob.match("[!abc]", "d")
            True

        *New in version 0.3.*
        """

    def no_bracket_expansion(self) -> Self:
        """Disable ``[abc]`` / ``[a-z]`` bracket expansion.

        Examples:
            >>> glob = Glob.default().no_bracket_expansion()
            >>> glob.match("[abc]", "[abc]")
            True

        *New in version 0.3.*
        """

    def brace_expansion(self) -> Self:
        """Enable ``{a,b,c}`` brace expansion.

        Examples:
            >>> glob = Glob.default().brace_expansion()
            >>> glob.match("{src,lib}/*.py", "src/foo.py")
            True
            >>> glob.match("{src,lib}/*.py", "test/foo.py")
            False

        *New in version 0.3.*
        """

    def no_brace_expansion(self) -> Self:
        """Disable ``{a,b,c}`` brace expansion.

        *New in version 0.3.*
        """

    def negate(self) -> Self:
        """Enable ``!pattern`` negation.

        Examples:
            >>> glob = Glob.default().negate()
            >>> glob.match("!*.py", "foo.txt")
            True
            >>> glob.match("!*.py", "foo.py")
            False

        *New in version 0.3.*
        """

    def no_negate(self) -> Self:
        """Disable ``!pattern`` negation.

        *New in version 0.3.*
        """

    def escape(self) -> Self:
        r"""Enable ``\`` escape sequences.

        Examples:
            >>> glob = Glob.empty().escape()
            >>> glob.match("\\*", "*")
            True
            >>> glob.match("\\*", "foo")
            False

        *New in version 0.3.*
        """

    def no_escape(self) -> Self:
        r"""Disable ``\`` escape sequences.

        Examples:
            >>> glob = Glob.default().no_escape()
            >>> glob.match("\\*", "\\foo")
            True

        *New in version 0.3.*
        """

    def path_separator(self) -> Self:
        """Enable path separator handling (``*`` and ``?`` do not match ``/``).

        Examples:
            >>> glob = Glob.default().path_separator()
            >>> glob.match("*.py", "foo.py")
            True
            >>> glob.match("*.py", "dir/foo.py")
            False

        *New in version 0.3.*
        """

    def no_path_separator(self) -> Self:
        """Disable path separator handling (``*`` and ``?`` match ``/``).

        *New in version 0.3.*
        """

    def match(self, pattern: str, value: str) -> bool:
        """Match a glob pattern against a value.

        Args:
            pattern: The glob pattern.
            value: The string to match against.

        Returns:
            True if the value matches the pattern.

        Examples:
            >>> glob = Glob.default()
            >>> glob.match("test_?", "test_a")
            True
            >>> glob.match("test_?", "test_ab")
            False

        *New in version 0.3.*
        """

class Flags(enum.IntFlag):
    """Low-level flag constants for bitwise composition.

    These map directly to the Rust ``u8`` bitfield. Use bitwise operators
    to combine them, then pass to ``Glob.from_flags()``.

    Examples:
        >>> from globlin import Glob, Flags
        >>> glob = Glob.from_flags(Flags.BRACKET_EXPANSION | Flags.ESCAPE)
        >>> glob.match("[a-z]", "m")
        True

    *New in version 0.3.*
    """

    EMPTY = ...
    """No features enabled.

    *New in version 0.3.*
    """

    GLOB_STAR = ...
    """Enable ``**`` globstar matching.

    *New in version 0.3.*
    """

    BRACKET_EXPANSION = ...
    """Enable ``[abc]`` / ``[a-z]`` bracket expansion.

    *New in version 0.3.*
    """

    BRACE_EXPANSION = ...
    """Enable ``{a,b,c}`` brace expansion.

    *New in version 0.3.*
    """

    NEGATE = ...
    """Enable ``!pattern`` negation.

    *New in version 0.3.*
    """

    ESCAPE = ...
    r"""Enable ``\`` escape sequences.

    *New in version 0.3.*
    """

    PATH_SEPARATOR = ...
    r"""Treat ``/`` as path separator — ``*`` and ``?`` do not match ``/``.

    *New in version 0.3.*
    """

    ALL = ...
    """All features enabled.

    *New in version 0.3.*
    """

    DEFAULT = ...
    """POSIX fnmatch-like defaults (``BRACKET_EXPANSION | ESCAPE``).

    *New in version 0.3.*
    """

@deprecated("Use Glob.default() instead")
def fnmatch(pattern: str, value: str, *flags: Flag) -> bool:
    """Match a glob pattern against a value."""
@deprecated("Use Glob instead")
class Flag:
    """Flag enum for fnmatch."""

    EMPTY: Flag
    """No features enabled."""
    GLOB_STAR: Flag
    """Enable ``**`` globstar matching."""
    BRACKET_EXPANSION: Flag
    """Enable ``[abc]`` / ``[a-z]`` bracket expansion."""
    BRACE_EXPANSION: Flag
    """Enable ``{a,b,c}`` brace expansion."""
    NEGATE: Flag
    """Enable ``!pattern`` negation."""
    ESCAPE: Flag
    r"""Enable ``\`` escape sequences."""
    NO_PATH: Flag
    """``*`` and ``?`` match ``/`` (disables path separator handling)."""
