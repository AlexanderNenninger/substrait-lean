### Routes name their evidence

- A route keeps the provenance the checker gives for its class: `route.theorems`
  for a proof, `route.facts`, `route.version` (the engine version the facts
  were probed at) and `route.issues` (the issues that track them) for a test. Its line names them:
  `shim (integer division rewritten to truncate); evidence proved by Rel.polars_sound, Polars.int_div_trunc`.
  The report's JSON carries the four fields
  ([#1166](https://github.com/AlexanderNenninger/substrait-lean/issues/1166)).
- `print(report)` shows an `evidence:` line per engine before any run, so a
  plan that rests on tested facts on an engine says so before it runs there.
- Evidence is `proved` only where every choice the class rests on is proved in
  Lean; a probe or a row without evidence counts as `tested`. Before, a plan
  whose rows were all probes read as proved.
- The engine versions come from the checker's profiles alone; the copy in
  `sverify.routes.PROFILES` is gone.
