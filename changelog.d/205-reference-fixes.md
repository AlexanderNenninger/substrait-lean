### Fixed: aggregates of double constants, casts between dates and timestamps

The reference computed two kinds of plans wrongly (#201). An aggregate of a
double constant read the constant as an integer: `SUM(CAST('inf' AS
DOUBLE))` is now `inf`, and `avg(42) OVER ()` is `42.0` (#205). A cast
between a date and a timestamp kept the number of days or microseconds: a
date now becomes midnight of that day, and a timestamp rounds down to its
day, before 1970 too. A comparison of a date with a timestamp without a cast
is refused (#206).
