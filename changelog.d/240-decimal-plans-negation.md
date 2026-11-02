### Plans with decimals and a negated double are written

A plan with DECIMAL arithmetic is written for the engines only if it reads
back as the same plan. Negating a double, or taking its `ABS`, broke that,
so such plans (TPC-DS q89, for one) stopped at "this decimal arithmetic
cannot be written for the engines yet". They are written now.
