# SPDX-FileCopyrightText: 2026 László Vaskó <opensource@accounts.vlaci.email>  # noqa: D100
#
# SPDX-License-Identifier: EUPL-1.2

from sybil import Sybil
from sybil.parsers.markdown import PythonCodeBlockParser
from sybil.parsers.rest import DocTestParser

pytest_collect_file = Sybil(
    parsers=[DocTestParser(), PythonCodeBlockParser()],
    patterns=["*.pyi", "python/globlin/__init__.py", "docs/*.md"],
).pytest()
