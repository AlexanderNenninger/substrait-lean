### Variance and standard deviation

`var()` and `std()` of doubles and integers, of a sample or a population
(`how="pop"`), are verified on every engine (#54). Each engine uses its own
algorithm for now, so results may differ in the last bits, and a contract
can rely only on the value being a non-negative double, or NULL: for no
values, and for a sample of one value. A NaN passes through; an infinite
value raises, since its deviation from the mean would be NaN. Variances over
windows are refused.
