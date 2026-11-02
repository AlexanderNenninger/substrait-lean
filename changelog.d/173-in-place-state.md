### Refreshes on DuckDB cost what changed

On DuckDB, a refresh no longer rebuilds a view's whole state. The merge plan
adds the change to the state rows it touches, and DuckDB replaces those rows
in place, in one transaction for every view: a refresh that changes ten rows
of a view of ten million costs about ten rows. Sinks write the sum of the
view's changes since the state they wrote. A view whose new contents a
recomputed view or `refresh(audit=True)` reads first is still merged in full
(#173).
