### A bound with only a lower end keeps it through double `+` and `*`

`amount >= 0` alone now proves `amount * 3 + 1 > 0`: a double's lower end bounds a sum with another lower end, and a product of non-negative ones, whatever the column is above it (`+∞` and NaN included), so the result is at least `1` where it was `any double` ([#1485](https://github.com/AlexanderNenninger/substrait-lean/issues/1485), item 7). A difference and a quotient by a range still give no lower end from one-sided operands.
