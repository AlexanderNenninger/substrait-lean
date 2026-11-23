### Kahan's sum and DuckDB's constant runs are proved within the sum bound

Sverify now proves the bound on an engine's double `SUM` for the last two
summation orders it took as given: Kahan's compensated sum (`COMPENSATED`,
Polars's grouped sums) and DuckDB's constant runs added as one product
(`SCALED_CONSTANT`). Both algorithms are written on the core's codes and
proved to meet `SumOrder` through the float-bounds bridge
(`KahanSums.sumOrder`, `FloatSumsK.sumOrder`,
[#1196](https://github.com/AlexanderNenninger/substrait-lean/issues/1196)).
What stays trusted is that the engine runs the algorithm its fact names.
