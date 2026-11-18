### Guards that a constant decides are not written

A literal operand decides checks that the written SQL used to spell out: `x / 2.0`
no longer carries the division-by-zero, infinity-over-infinity and overflow
`CASE`s (2680 characters become 244), and `n // 10` drops the sign tests of the
floor division and the zero check that never held (1390 become 438). A check
stays where a constant can still make it fire (`x / 0.5` can overflow)
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).
