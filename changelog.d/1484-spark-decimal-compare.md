### Spark refuses a decimal comparison it would round

Spark compares decimals of different scales in a common type and, where that type passes 38 digits, rounds the operand of the higher scale: `CAST(2 AS DECIMAL(38,0)) = CAST(1.5 AS DECIMAL(38,10))` is true on Spark. The Spark writer now refuses such a comparison, and `GREATEST` or `LEAST` of such a pair (the common type has `max(p₁ - s₁, p₂ - s₂) + max(s₁, s₂)` digits), naming the two types; a pair that fits 38 digits is written as before and is exact (`spark-decimal-compare-scale`, #1484).
