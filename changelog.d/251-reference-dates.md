### Dates: the reference's own range

Date arithmetic is now checked against the reference's dates, the SQL
standard's 0001-01-01 to 9999-12-31, instead of the (much wider) range
DataFusion computes. Adding days or months that leaves them raises "outside
the reference's dates" on every engine, and `verify` reports it. With
constant operands, such as TPC-H Q6's `DATE '1994-01-01' + INTERVAL 1 YEAR`,
the written SQL no longer carries a range check at all (#251).
