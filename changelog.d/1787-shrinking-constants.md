### No overflow assumed where a division or product shrinks its operand

Sverify proves that a double divided by a value of at least 1 in size, or multiplied by one of at most 1, can't overflow to `±inf` (`BinFn.shrinks_fin`). Two common examples are a percentage `x / 100.0` and a rate `x * 0.01`. The same holds when a contract's ranges bound the divisor or factor, as in `x / y` with `y >= 1`. Sverify no longer assumes an overflow there, so a checked run drops the assumed check before the plan and the check in the SQL it writes (#1787).
