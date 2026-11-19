### Decimal literals of up to 38 digits are written exactly

A decimal literal of more than 28 digits was rounded to 28 by Python's default `Decimal` context and then refused as "does not fit" its type. The scaling now runs in one context wide enough for 38 digits (`sverify._decimals.scaled`), so such a literal, a bound of `10**34 - 1` for example, verifies and compares exactly. Other places that shared the rounding (the Ibis producer's literal width, the shown bounds of a decimal) use it too.
