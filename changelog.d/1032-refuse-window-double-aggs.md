### Fixes

- A window `SUM`, `AVG`, `VARIANCE` or `STDDEV` of doubles is refused on
  every engine. The plan's bound left window functions out, so such a plan
  ran with route class `exact` while the engine's value could differ from the
  reference's correctly rounded one ([#1032](https://github.com/AlexanderNenninger/substrait-lean/issues/1032)).
  The refusal names the issue; the windows return once the bound covers them.
