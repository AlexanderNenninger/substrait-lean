### Fixed: reports on a DATE beyond the year 9999

A transformation with a DATE column whose range passes Python's limits, such
as `CAST(ts AS DATE)` of a TIMESTAMP, raised `OverflowError` while describing
its facts. Bounds outside the years 1 to 9999 now go without saying: the
column is "any date" (#435).
