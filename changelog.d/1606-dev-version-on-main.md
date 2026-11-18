### Main carries a development version

A build from main is versioned `<next minor>.0.dev0` (now `0.9.0.dev0`), so it cannot be mistaken for the release on PyPI, and an `==` pin no longer matches across the two. `python/scripts/set_version.py` sets the nine places that carry the version; the release skill uses it for the bump and to reopen main after a release (#1606).
