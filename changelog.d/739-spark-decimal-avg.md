### Spark runs an AVG of decimals

A plan with an `AVG` of a `DECIMAL` (or Ibis's decimal division by an integer) now runs on Spark, where it was refused. Sverify writes the exact quotient at the reference's scale, rounded half away from zero; Spark's own `/` rounds once at a scale of its own first (spark-decimal-arith). A result past 12 decimal places, past 32 integer digits, or of 38 digits with more than 6 decimal places stays refused, with a cast to fewer digits as the way out ([#739](https://github.com/AlexanderNenninger/substrait-lean/issues/739)).
