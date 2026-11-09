# Build performance

Every session waits on the Lean build, so its time and memory are measured
per module and guarded in CI. This page has the method, the budget and the
latest numbers.

## The method

Lake runs `lean` from the sysroot it finds through `LEAN_SYSROOT` (with
`LAKE_OVERRIDE_LEAN=true`). [`scripts/lean_timings.py`](../scripts/lean_timings.py)
`sysroot` makes a copy of the toolchain's sysroot, symbolic links, whose
`bin/lean` runs the real `lean` under `os.wait4`: each module's CPU time
(user and system), wall time and peak RSS, exact, one JSON line each in
`$LEAN_TIMINGS`. The build is the same build, with the same arguments and
outputs.

```bash
python3 scripts/lean_timings.py sysroot /tmp/lean-sysroot
LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT=/tmp/lean-sysroot LEAN_TIMINGS=t.jsonl lake build
python3 scripts/lean_timings.py report t.jsonl          # by time, by RSS, the critical path
python3 scripts/lean_timings.py check t.jsonl           # against the budget
python3 scripts/lean_timings.py replay t.jsonl --out isolated.jsonl
```

- Cold: a build from an empty `.lake`, Lake's parallelism on. Its numbers
  carry the other modules' contention.
- Isolated (warm): `replay` compiles each recorded module again, alone, its
  imports built and its outputs thrown away.
- The critical path is the longest import chain by time. No parallel build
  is shorter.
- Generated proofs off is a plain `lake build`; on is
  `lake -R -Kcheck_generated=true build` (`engines/Sverify/Engines/Generated.lean`).

To find what a slow module spends its time on, put
`set_option profiler true` (and `set_option profiler.threshold 200`) above
the slow declarations and build the one file:
`timeout 600 lake lean <file> -- -M 3072` (`lake env lean` resolves
`Sverify.Engines.*` in the core's build, with two packages under `Sverify/`).
A generated module's entries are proved only with `check_generated` on.

## The budget

[`scripts/lean-budget.json`](../scripts/lean-budget.json) holds a ceiling per
module, 1.5 times its measured CPU time and peak RSS, at least 30 s and
1.5 GB, and a default for modules it doesn't list. CI's `lean` job builds
through the timing sysroot and runs `check` on the modules it rebuilt: the
others came from the cache, unchanged with everything they import. A module
over its ceiling fails the job, named in the error. The job's summary has the
report, and the `lean-timings` artifact the records.

A module over its ceiling gets cheaper in the same PR, or its line goes up
there with the reason in the PR body. After a PR that makes modules cheaper,
`write-budget` from the CI artifact lowers the ceilings.

## Patterns that cost

- `simp` or `decide` unfolding a large constant. `canon`'s `2^2045`
  constants took `TransferSound` past 11 minutes; `rfl` lemmas about the
  constant, used in place of unfolding it, brought it back.
- `decide` on more than a small term (CLAUDE.md allows it on small terms
  only). Reflection through a `Bool` function and `rfl` is cheaper.
- `omega` or `simp_all` over a large context: `clear` what the goal doesn't
  need first, or name the hypotheses `simp` gets.
- Unfolding a large definition at every step. `pow2Chain_eval` unfolded
  `Profile.duckdb` at each induction step; rewriting with the lemma
  `Lowering.duck_eq` took its `simp` from 10.8 s to 0.05 s
  ([#1293](https://github.com/AlexanderNenninger/substrait-lean/pull/1293)).
- A case split over a wide inductive multiplies the cost of every tactic
  after it. `cases x <;> cases y` over `Value` made 25 goals before
  [#923](https://github.com/AlexanderNenninger/substrait-lean/issues/923) and 121 after, and `On.Doubles` went from 32 s to
  126 s. One `simp` unfolded the profiles, the issues and the functions at
  once on every goal; three goal-only stages first brought it to 84 s
  ([#1299](https://github.com/AlexanderNenninger/substrait-lean/pull/1299)).
- Wide imports: a module imported by many rebuilds them all on any change.
  `import Lean` alone makes a module's process about 2 GB.
- Large generated modules: their proofs are checked only when
  `check_generated` is on.

## The numbers

Measured on 2026-11-09 from main at `deec99a4`, the method above, on
homelab (Ryzen 5 3600X, 12 threads, `nice -n 10`); the CI column is a cold
checked build on a GitHub runner (`ubuntu-latest`, 4 vCPU) from `0e11885d`,
the commit before. A module built alone takes about the same CPU time on
both (`On.Doubles` 594 s on homelab, 587 s on the runner); in homelab's
parallel build two threads share each core, and CPU times run up to a
quarter higher. The ceilings take the highest of these.

### Whole builds

| build | homelab | CI runner |
|---|---:|---:|
| cold `lake build`, generated proofs off | 223 s, critical path 219 s, CPU 1031 s | |
| then `lake -R -Kcheck_generated=true build` (29 modules) | 249 s | |
| cold checked build | critical path 422 s, CPU 2311 s | 656 s, CPU 1850 s |
| `engines/` alone | 58 s | |
| no-op `lake build` | 1 s | |
| peak memory of the build (cgroup) | 3.1 GB unchecked, 2.8 GB rebuilding the checked modules | |

The cold build's time is its critical path, about one import chain long:
the core's floats, expressions and order, then `Contracts.Lattice` →
`Transfer` → `TransferSound` → `Refine` → `Facts` → `Safety` →
`Partition` → `Guards` → `Lowering` → `LoweringSearch` → the generated
modules → `Obligations` → `Engine`. More cores don't shorten it; a module
that starts earlier, or a cheaper one on the chain, does.

### The slowest modules

Cold, generated proofs on, homelab; the CI column is the same module's CPU
time on the runner.

| module | CPU s | wall s | RSS MB | CI CPU s |
|---|---:|---:|---:|---:|
| `SubstraitLean.LoweringDuckDB.On.Doubles` | 733 | 179 | 2550 | 587 |
| `SubstraitLean.LoweringDuckDB.On.Integers` | 145 | 83 | 1946 | 105 |
| `SubstraitLean.DuckDBSQL` | 133 | 33 | 930 | 100 |
| `SubstraitLean.LiftDuckDB.Duckdb.Arith` | 88 | 109 | 1981 | 69 |
| `SubstraitLean.LoweringDuckDB.On.Math` | 75 | 42 | 1926 | 53 |
| `SubstraitLean.LoweringDuckDB.On.Guards` | 64 | 28 | 2406 | 51 |
| `SubstraitLean.LoweringDuckDB.On.Native` | 51 | 11 | 1881 | 36 |
| `SubstraitLean.LiftDuckDB.Duckdb.Compare` | 49 | 70 | 1874 | 37 |
| `SubstraitLean.Safety` | 44 | 18 | 1219 | 46 |
| `SubstraitLean.LiftDuckDB.Duckdb.Math` | 43 | 61 | 1858 | 32 |
| `SubstraitLean.Contracts.TransferSound` | 41 | 16 | 1140 | 36 |
| `Sverify.Core.Kinds` | 40 | 26 | 1074 | 32 |

CPU time above wall time is Lean elaborating a module's theorems in
parallel. `On.Doubles` comes down to 181 s CPU with
[#1299](https://github.com/AlexanderNenninger/substrait-lean/pull/1299). Peak RSS falls
into two tiers: about 0.5 to 1.3 GB for a module whose imports stop short of
`import Lean`, and 1.6 to 2.6 GB for the generated modules and everything
that imports them, which load Lean's elaborator through `LoweringSearch` and
`LiftSearch` ([#1292](https://github.com/AlexanderNenninger/substrait-lean/issues/1292)).
