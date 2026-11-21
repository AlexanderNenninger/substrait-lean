### A decimal average over a window stays within its inputs

`AVG` of a decimal column over a window now keeps the bounds of the values it averages, as a grouped `AVG` already did. A sum minus its average per partition, or a ratio that divides by that average, no longer reports an overflow or a division by zero that its inputs' bounds rule out ([#2015](https://github.com/AlexanderNenninger/substrait-lean/issues/2015)).
