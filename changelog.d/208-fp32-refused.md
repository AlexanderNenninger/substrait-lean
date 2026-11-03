### Arithmetic on `FLOAT` (fp32) is refused

The reference computed `FLOAT` arithmetic in doubles, so `2e38::FLOAT / 0.1`
gave `2e39` where every engine gives `inf`. Arithmetic on `FLOAT`s and casts
to `FLOAT` are refused until binary32 is modelled (#208, #417). Reading a
`FLOAT` column, comparing it and widening it to `DOUBLE` are exact and keep
working; cast to `DOUBLE` first to compute with it.
