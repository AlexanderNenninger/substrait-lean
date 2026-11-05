### Unproved plans no longer run silently (#655)

`Report.run`, `Node.refresh` and a group's `refresh` refuse a plan whose
report is not proved, with what was not proved in the user's terms:
`refused on duckdb: not verified: may fail: domain error: sum(x) (see
report.errors)` (`sverify.errors.RouteError`). `unverified=True` runs it
anyway and says so: an `UnverifiedRunWarning`, the route `"unverified"` in
`Report.routes` or `StageRefresh.route`, and `sverify.verified: false` in
the result's schema metadata. `route="auto"` is the default: every run
chooses how its proof reaches the engine (`sverify.routes.choose`), and
`route=None` is gone.
