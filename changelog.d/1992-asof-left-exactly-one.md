### `sv.asof_join(how="left")` keeps every left row, proved

Sverify now proves that a left as-of join has one output row per left row:
every result the reference allows has as many rows as the left table
(`AsofSite.left_exactly_one`,
[#1992](https://github.com/AlexanderNenninger/substrait-lean/issues/1992)).
The checker's as-of sites report whether a plan has the shape the theorem is
about (`left_exact`).
