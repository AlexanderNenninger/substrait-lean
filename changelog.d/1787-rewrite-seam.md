### Proved rewrites run on an engine, in Lean

Sverify's Lean model now states what an optimization must prove before an
engine may run it ([#1787](https://github.com/AlexanderNenninger/substrait-lean/issues/1787), step 1).
A rewrite that refines the plan, exactly or up to the order of rows, gives an
engine run that the reference allows for the plan as written
(`Engine.Sound.of_refines`). A contract verified on the plan as written holds
on that run, with every bound computed from the written plan
(`Engine.contract_sound_rewrite`). A refinement at one node carries up through
every operator but `FETCH` (`analysis/Sverify/Analysis/Refines.lean`), and
`Engine.runPlan` falls back to the written plan when the engine does not
translate the rewrite or the rewrite fails the side condition's check. Nothing
runs the optimized plan yet: item 2 of the epic adds the per-rule gate.
