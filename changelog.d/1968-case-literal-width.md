### A CASE of constants has its declared width

A column computed by a `CASE` whose branches are integer constants now has the
width their declared type gives, as a literal column does since
[#1934](https://github.com/AlexanderNenninger/substrait-lean/issues/1934):
`CASE WHEN x > 0 THEN 100 ELSE 0 END` of `BIGINT` literals is a 64-bit column, and
`e * e` of it is no longer reported as an 8-bit overflow. A `CASE` of `TINYINT`
constants stays 8 bits ([#1968](https://github.com/AlexanderNenninger/substrait-lean/issues/1968)).
