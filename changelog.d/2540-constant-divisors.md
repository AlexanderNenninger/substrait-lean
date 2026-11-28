### Smaller SQL for integer division by a constant

Integer `/` and `%` by a constant other than 0 are written without a zero check on Spark and Snowflake. The check repeated the dividend, so calendar arithmetic, which nests them, gave SQL that grew exponentially: a date from columns was 175 KB of Spark SQL and is now 43 KB ([#2540](https://github.com/AlexanderNenninger/substrait-lean/issues/2540)).
