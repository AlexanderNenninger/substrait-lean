### No overflow assumed for a division by a decimal

A double divided by a decimal converted to a double, such as `price / CAST(quantity AS DOUBLE)` with a decimal quantity, no longer assumes an overflow to `±inf` where the dividend is bounded. A zero divisor raises division by zero first. Any other decimal at scale `s` is at least `10⁻ˢ` in size, so the quotient stays within the dividend's bound over that divisor (`decQuotFinite_sound`, #1787).
