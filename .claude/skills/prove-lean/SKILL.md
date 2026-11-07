---
name: prove-lean
description: Work on sverify's Lean model and proofs (SubstraitLean/): state and prove a theorem, add a shim with its soundness lemma, change an evaluator or analysis, or extend a profile. Covers finding existing lemmas, the no-weakening rule, Allowed vs equality, the axioms audit, building cheaply and with --wfail, generated modules, and docs/proofs.md. Use whenever a task edits .lean files.
---

# Working on the Lean proofs

## Before writing

1. Read the step's issue and `docs/proofs.md`, which maps each module to its
   theorems and assumptions. The design dossier (#936) has the order and
   decisions of the core refactor.
2. Search for an existing lemma before declaring one:
   `grep -rn "theorem .*<keyword>\|lemma .*<keyword>" SubstraitLean/`. Reuse it,
   or generalise it in its own module.
3. Check `Rel.Allowed` (`Allowed.lean`, `AllowedP.lean`). Where the reference
   leaves a choice open (tie order, float summation, row order), the theorem
   is membership in `Allowed`, not equality of results.

## While proving

- No `native_decide`, no `sorry`, `decide` only on small terms; prefer
  reflection or `simp` with specific lemmas.
- Don't weaken a statement to make it close. If it's false, write down the
  counterexample, name the side condition as a predicate on the plan, prove
  the theorem under it, and prove the predicate for the cases you cover.
  Say so in the PR, and on the issue whose later step discharges it.
- The reference (`Rel.eval`, `Rel.Allowed`) changes only with a decision
  recorded in `docs/core-semantics.md`.
- Shims: each comes with a soundness lemma against the reference (or its
  `Allowed` set), named after the engine and the shim, beside the profile's
  other shims (`PolarsShims.lean`, `SparkShims.lean`).

## Building

- Check capacity first (`uptime` ≤ 6 on the laptop). Build only the modules
  you touch while working: `lake build SubstraitLean.<Module>`.
- CI builds with warnings as errors: build with `lake build --wfail` before
  pushing. A heartbeat timeout means the proof is too expensive: restructure
  it rather than raising the limit.
- Full builds with the generated proofs (`lake -R -Kcheck_generated=true build`)
  go to homelab via `python/scripts/homelab_qa.sh`, one run at a time.
- Generated modules (`LoweringDuckDB/On`, `LiftDuckDB/Duckdb`, `Reference`)
  are regenerated with `poe regen-lowering` / `poe regen-lift`, never edited
  by hand. A changed constructor list usually needs both, plus the lowering
  golden (`tests/lowering/duckdb.expected`).

## Before the PR

- `#print axioms` of the changed theorems: the same as on main, or the PR
  says which axiom changed and why.
- A new module gets its line in `docs/proofs.md`, in its layer.
- The goldens pass (`tests/run.sh`), and the Python mirror still agrees
  (`substrait-check --functions` against `tests/test_functions.py`) when you
  touched function tables.
- The PR's Improvement section measures something before and after: build
  time, memory, proof size, the checker's time, or hypotheses and axioms
  removed (CLAUDE.md, "Every PR leaves its area faster or simpler").
