# Substrait's profile

`Profile.substrait` states what Substrait's function YAMLs allow, their own
looseness, as a profile beside the reference and the engines' profiles
([docs/engine-profiles.md](../../docs/engine-profiles.md)). Plans verify under
it with `verify(semantics="substrait")`; the plugin is sverify's own
(`python/src/sverify/_builtin/substrait.py`), since there is no engine to run.

- `Sverify/Substrait/` and `lakefile.toml`: the Lake package
  `sverify-substrait`, on the core alone
  ([docs/proofs.md](../../docs/proofs.md)).
