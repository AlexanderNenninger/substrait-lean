"""What this sverify is: its installed version and the checker protocol it
speaks (#730: below the checker and the reports that record them).

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.
"""

from importlib.metadata import PackageNotFoundError, version

try:
    VERSION: str = version("sverify")
except PackageNotFoundError:  # a source tree without an install
    VERSION = "0+unknown"

#: The checker protocol this sverify speaks: `protocol` in `Main.lean`, bumped
#: with it whenever a mode's output changes shape.
PROTOCOL = 3

#: The plugin interface revision: what `ProfilePlugin` takes and what an engine
#: package imports from sverify. Bump it with any change to either; each engine
#: package checks it at import, since a build from main carries the release's
#: version and an `==` pin cannot tell the two apart (#1585).
PLUGIN_API = 3
