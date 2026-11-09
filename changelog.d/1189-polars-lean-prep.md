### Polars's Lean modules stand on the shared packages

Polars's Lean modules now import only the core, the analysis, engines-common
and each other ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
The lowering machinery (`Sverify.Engines.Lowering`) and what an engine's
model is sound for (`Sverify.Engines.Sound`) join engines-common,
`Profile.reference_faithful` joins the analysis (`Sverify.Analysis.ProfileImpl`),
and `Expr.floorDivOf`/`Expr.floorModOf` join the core. Polars's table and
`Engine` value get modules of their own (`PolarsTables`, `PolarsEngine`). No
theorem changed.
