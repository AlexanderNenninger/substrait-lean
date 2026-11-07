---
name: upstream-bug
description: Record a bug in SQLGlot, an engine, Ibis or Substrait's tooling (or a Substrait spec gap) as upstream/bugs/<id>.json in the PR with its workaround: id prefixes, fields, linking facts, and the checker. Use when a workaround is needed for someone else's bug, or behaviour the Substrait YAMLs leave unspecified. For drafting the upstream report itself, use upstream-report.
---

# Upstream bugs

When you find a bug in SQLGlot, an engine, Ibis or Substrait's tooling, add
a document `upstream/bugs/<id>.json` in the same PR as the workaround, in the
format of `upstream/bug.schema.json`: the version, a status, a minimal
reproduction, how sverify handles it, and what it was last checked against
(`checked`). The id is the project's prefix and the next free number (`SG-8`,
`DD-5`; `upstream/README.md` lists the prefixes); the file is named after it.
Link the files of the workaround (`files`) and the engine facts that record
it (`facts`). We file them upstream in batches, with the `upstream-report`
skill. Documented engine behaviour that only differs from the reference model
goes into the engine's characterization.

Behaviour the Substrait YAMLs leave unspecified, but that Substrait could
express (a missing option, option value or default), is a spec gap: add an
`ST-<n>` document with `kind: spec-gap` in the same PR that meets it, saying
how Substrait could express it and what each engine does (its facts).
`docs/core-semantics.md` lists the ones found so far.

`python -m sverify_dev.bugs` checks the documents and the lift's backlog
`python/tests/lift_backlog.json` (`tests/test_bugs.py` does too).
