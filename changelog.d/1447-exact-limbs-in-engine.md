### Maintained double aggregates keep their exact state in the engine

A maintained `SUM`, `AVG`, `VAR`, `STDDEV`, `COVAR` or `CORR` of doubles keeps
its exact moments as integer limbs, rows of the group state that the engine
adds up with its own `SUM` (#1447). A batch no longer brings each changed row
to the driver: Python reads the limbs of the touched groups and rounds them
once, so the results are unchanged (D25, D30). The state takes about half the
bytes of the decimal strings it replaces. A group with `2⁴¹` values or more,
past what the limbs hold, raises.
