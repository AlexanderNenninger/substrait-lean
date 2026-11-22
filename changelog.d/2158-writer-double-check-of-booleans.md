### Fixed

- The SQL writer no longer refuses `corr` and `cov` of booleans (`(t.G > 34.0).corr(t.G <= 34.0)`) after the checker accepted them: it read `abs` of a double built from an `IF` as an integer `abs`, as Lean's parser does not ([#2158](https://github.com/AlexanderNenninger/substrait-lean/issues/2158)).
