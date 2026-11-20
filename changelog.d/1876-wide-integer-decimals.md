### An integer cast to a wide DECIMAL is read as a decimal (corrected rule)

Sverify used to read an integer's cast to `DECIMAL(p, 0)` with 19 or more digits as the integer itself, a rule from before decimals were modelled. Arithmetic after such a cast was then checked and written at 64 bits, where the plan computes it at `p` digits: `CAST(i AS DECIMAL(38, 0)) * j` was reported as `may fail: overflow` and refused ([#1876](https://github.com/AlexanderNenninger/substrait-lean/issues/1876)). The cast is now read as the plan declares it, as any other cast to a decimal:

- arithmetic after the cast is checked at `p` digits, so such products and sums prove where they fit;
- the result column is `DECIMAL(p, 0)` where it was an integer;
- the public Snowflake writer, which computes no decimal as the reference does yet (#27), refuses such a plan where it wrote 64-bit integer arithmetic before.
- a decimal's truncation and rounding to an integer keep their operand's bounds, so more casts of a decimal back to an integer prove: `CAST(CAST(i AS DECIMAL(38, 0)) AS BIGINT)` proves with no precondition.
