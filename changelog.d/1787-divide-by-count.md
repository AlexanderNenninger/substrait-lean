### No overflow check on a division by a count

A double divided by an integer cast to a double, such as a rate `d1.cast("float64") / users` or a mean computed as a sum over a count, can't overflow to `±inf`. A zero divisor already raises division by zero, and any other divisor is at least 1 in size. Sverify proves this (`Expr.mayInfBin_sound`), so it no longer assumes such an overflow or checks for it in the SQL it writes (#1787).
