# pyright: reportDeprecated=false
# SPDX-FileCopyrightText: 2026 László Vaskó <opensource@accounts.vlaci.email>
#
# SPDX-License-Identifier: EUPL-1.2

"""Contains a more performant and complete implementation of fnmatch."""

from typing_extensions import Self, deprecated

class Glob:
    """Glob pattern matcher with configurable features.

    Use ``Glob.default()`` for POSIX fnmatch-like matching (bracket expansion
    and escape sequences enabled), or ``Glob.empty()`` for a minimal
    configuration. Chain builder methods to enable or disable features, then
    call ``match()`` to test patterns.
    """

    @classmethod
    def default(cls) -> Glob:
        """Create a glob with POSIX fnmatch-like defaults.

        Enables bracket expansion and escape sequences. Additional
        features like globstar can be added via builder methods.
        """

    @classmethod
    def empty(cls) -> Glob:
        """Create a glob with no features enabled."""

    @classmethod
    def from_flags(cls, flags: int) -> Glob:
        """Create a glob from raw bitflags.

        Args:
            flags: Bitwise combination of constants from the ``flags`` module.

        Raises:
            ValueError: If any bits outside the valid range are set.
        """

    def globstar(self) -> Self:
        """Enable ``**`` globstar matching.

        Implies ``path_separator()`` since globstar is only meaningful when
        ``/`` is treated as a path separator.
        """

    def no_globstar(self) -> Self:
        """Disable ``**`` globstar matching."""

    def bracket_expansion(self) -> Self:
        """Enable ``[abc]`` / ``[a-z]`` bracket expansion."""

    def no_bracket_expansion(self) -> Self:
        """Disable ``[abc]`` / ``[a-z]`` bracket expansion."""

    def brace_expansion(self) -> Self:
        """Enable ``{a,b,c}`` brace expansion."""

    def no_brace_expansion(self) -> Self:
        """Disable ``{a,b,c}`` brace expansion."""

    def negate(self) -> Self:
        """Enable ``!pattern`` negation."""

    def no_negate(self) -> Self:
        """Disable ``!pattern`` negation."""

    def escape(self) -> Self:
        r"""Enable ``\`` escape sequences."""

    def no_escape(self) -> Self:
        r"""Disable ``\`` escape sequences."""

    def path_separator(self) -> Self:
        """Enable path separator handling (``*`` and ``?`` do not match ``/``)."""

    def no_path_separator(self) -> Self:
        """Disable path separator handling (``*`` and ``?`` match ``/``)."""

    def match(self, pattern: str, value: str) -> bool:
        """Match a glob pattern against a value.

        Args:
            pattern: The glob pattern.
            value: The string to match against.

        Returns:
            True if the value matches the pattern.
        """

class flags:  # noqa: N801
    """Low-level flag constants for bitwise composition.

    These map directly to the Rust ``u8`` bitfield. Use bitwise operators
    to combine them, then pass to ``Glob.from_flags()``.
    """

    EMPTY: int
    GLOB_STAR: int
    BRACKET_EXPANSION: int
    BRACE_EXPANSION: int
    NEGATE: int
    ESCAPE: int
    PATH_SEPARATOR: int
    ALL: int
    DEFAULT: int

@deprecated("Use Glob.default() instead")
def fnmatch(pattern: str, value: str, *flags: Flag) -> bool:
    """Match a glob pattern against a value.

    .. deprecated::
        Use ``Glob.default()`` instead.
    """
@deprecated("Use Glob instead")
class Flag:
    """Flag enum for fnmatch.

    .. deprecated::
        Use ``Glob`` builder methods or ``flags`` module constants instead.
    """

    EMPTY: Flag
    GLOB_STAR: Flag
    BRACKET_EXPANSION: Flag
    BRACE_EXPANSION: Flag
    NEGATE: Flag
    ESCAPE: Flag
    NO_PATH: Flag
