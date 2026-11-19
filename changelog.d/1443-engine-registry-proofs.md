### The checker's engines carry their soundness proofs

The list `substrait-check` is built over holds each engine's `Engine` value
with the proof that its run is sound (`EngineEntry`,
`engines/Sverify/Engines/Entry.lean`), so an entry whose theorem does not
state its engine's soundness no longer builds
([#1443](https://github.com/AlexanderNenninger/substrait-lean/issues/1443)).
`--realizability`'s `"theorem"` names that proof (`Engine.duckdb_sound`,
`Engine.polars_sound`, `Engine.spark_sound`), and a new `"side"` the side
condition it holds under (`Engine.NoRaiseSide`, `Engine.GuardFreeSide`). An engine package from outside
builds its checker over `builtinEntries ++ [its entry]`, copying
`SubstraitCheckExamples/DummyEngine.lean`; `EngineProfile.translationTheorem`
and `asReference` are gone, and a request under such an engine's profile is
pending like a built-in one's.
