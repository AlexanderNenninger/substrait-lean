### `semantics="portable"`, and lenses in the report's words

Breaking. The semantics every engine reaches is called `"portable"`:
`sv.verify(..., semantics="portable")` is the default, `Report.semantics`
and a route's `profile` say `"portable"`, and `sv.sql(..., semantics=...)`
takes `"duckdb"` or `"portable"`. `"reference"` is refused, with the list of
names `verify` takes. The reference profile keeps its name in the theory
(`Profile.reference`, `docs/core-semantics.md`). The SQL lift's profile
constant `sverify.sql_lift.REFERENCE` is `PORTABLE`.

Reports, Substrait manifests and sinks' contract records written before
1.0 say `"reference"`, and read as `"portable"`: a sink resumes, and its
plan's digest is unchanged ([docs/stability.md](docs/stability.md)).

Messages say "lenses" where they said "the observation": "no engine
meets the lenses' tolerance", "depends on floats, which the lenses ignore".
([#2081](https://github.com/AlexanderNenninger/substrait-lean/issues/2081),
[#1288](https://github.com/AlexanderNenninger/substrait-lean/issues/1288))
