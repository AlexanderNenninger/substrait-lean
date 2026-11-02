### Decimals in reports keep their scale

`verify`'s "known about the output" showed a decimal column's bound as its
internal unscaled integer: TPC-H Q6's `revenue` read "an integer ≥ 450000".
It now reads "a decimal(38, 4) ≥ 45.0000", with the column's type (#250).
