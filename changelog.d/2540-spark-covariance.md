### Spark runs covariance and correlation

Spark runs `cov` and `corr` (SQL `covar_samp`, `covar_pop`, `corr`) with its own Welford co-moment, within the bound sverify proves for it, and with the reference's NULL cases ([#2540](https://github.com/AlexanderNenninger/substrait-lean/issues/2540)).
