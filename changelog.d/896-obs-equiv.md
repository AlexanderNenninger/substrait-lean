### Observations have a meaning in Lean

Equality up to an observation is now a Lean relation, `Relation.Equiv`
(`core/Sverify/Core/ObsEquiv.lean`), and `Relation.Equiv_mono` proves that a finer
observation's equality implies a coarser one's, the order `Observation.refines`
computes (D18, #896). `substrait-check --options` reports each component's
levels and their order, and a test checks the Python order against it.
