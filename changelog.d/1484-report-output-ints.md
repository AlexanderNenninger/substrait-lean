### `Report.output` states the run's integer widths

`report.output` now types an integer column as the run returns it: `int64` for a computed integer (`i8 + i8`, `abs(i8)`, `-i16`, `year(ts)`, `length(s)`), the declared width for a column passed through, and `timestamp(6)` for a timestamp. It said Ibis's widths before (`int8` for `i8 + i8`), which the run did not return. Code that read a computed column's width from `report.output` sees `int64`. The contract report's `outputKinds` carries an integer's `bits`. An explicit cast gives today's width in both; writing the width it names is #1772.
