# The refresh protocol, in TLA+

`Refresh.tla` models how sverify refreshes one stored node, `node.write(sink)`,
when the processes that refresh it crash, restart, race each other and lose
acknowledgements. It is step 1 of [#933](https://github.com/AlexanderNenninger/substrait-lean/issues/933):
TLC checks it exhaustively at small scopes, and finds the interleavings the
chaos suite (`python/tests/chaos/`) can only sample. Step 2 states the same
transition system in Lean.

## What it models

One node with one source and one sink, as sverify 0.7 runs it:

| model | sverify |
|---|---|
| `Start`, `Stop` | a process builds the node; a deploy stops the processes of the old plan |
| `Refresh` | `Group.refresh`: `_continue_versions`, then `_Stage.build` on the first refresh of a process (resume from `sink._stored()`, or compute), later the source's change (`nodes.py`) |
| `Prepare` | `Sink._commit` up to the write: `contract()`, the pending write, the plan and digest checks, the skip, the change since `_written` (`io/_sink.py`) |
| `Land`, `Conflict` | the table format's conditional commit (`_TableSink.write`, `_check`, Delta's `Transaction(app_id, epoch)`, Iceberg's `_Guarded`), and `ConcurrentWriteError` |
| `LandLostAck`, `Fail` | a write that raises after or before its commit landed (`Sink._pending`) |
| `Crash`, `ZombieLands` | a process dies; a write it had sent may still land, late |
| `SourceChanges` | a new version of a durable source (`DeltaSource`, `IcebergSource`, a `Source` with `restore`), or a new snapshot of one that cannot restore (`from_frame`, `Source._resume_after`) |
| `ForeignWrite` | another application changes the sink's rows (`last_record(...).kept` turns false) |
| `Deploy` | a new plan (a new `Contract.plan`) |

The data is abstract. The node's rows are `St(plan, content)`, a function of
the plan and the source's content. A write that applies a change to a table
other than the one the change was computed from yields `corrupt`: for some
sinks and some changes the result happens to be right (Delta's MERGE sets the
changed rows to their new counts), for none in general (a row added and
removed again between the two states keeps its stale count; a custom `Sink`
applying `inserts` and `deletes` applies them twice).

Left out, for later steps: several sources (the epoch is their versions'
sum; here it is the one version), a source dropped and created again
(`table_ids`), quarantined and held batches, retention, maintenance commits,
nodes reading the stored node, and `group` refreshes. `Refresh` is one step
(the reads of `_continue_versions` and `_stored()` happen together).

## Properties

Invariants, numbered as in #933:

- `NoCorruption` (2, 4): a change is applied only to the state it was
  computed from.
- `RecordDescribesTable` (4, the refinement on the sink): when the app's
  commit is the last one, the table is the state its record names.
- `ReadIsHead` (3): when a change commits, the commit `contract()` read is
  still the app's last one.
- `Monotone` (1, 5): under one plan, versions never go down and no state is
  committed twice in a row (a repair after a foreign write may write the same
  state again).
- `NoNeedlessRewrite` (#889): a new process does not rewrite in full a state
  it could resume from.
- `NoRewriteUnchanged` (#889): a refresh whose source content is what the
  sink records commits nothing.

Liveness, under weak fairness for every process step and strong fairness for
stopping a process of an old plan: `Converges`, once the source and the
deploys stop, the sink ends up with the deployed plan's state of the source.

Witnesses (`witness-*` configs) are invariants that must fail: a zombie's
write lands, a process writes on after a lost acknowledgement, a change is
merged, a writer replaces a state of its own plan. They show that the fixed
model reaches the states the properties are about.

## Findings

The `today-*` configs model the protocol of sverify 0.7.0, before the fixes
(every `Fix*` switch off); their names date from then. Each finding below is
the shortest trace TLC found there; `trace.py` prints it. All five are fixed
since: #963 by #980, #964 by #982, #965 and #889 by #986, #966 by #987. The
fixed protocol, the one sverify runs, is the model with every `Fix*` switch
on.

Four ways the protocol before the fixes put the sink in a state it did not
record, and the verdict on #889. The traces are in `traces/`; each line is one step,
`P1(c2)` the rows of plan 1 on source content 2, `corrupt` a change applied
to another state.

1. A change lands on a commit the writer did not compute it from (#963).
   `Sink._commit` wrote the change since `_written` whenever the record had
   the same plan and a lower epoch, without checking the record was the one
   it wrote. One writer is enough: a restart resumes, the crashed process's
   write lands late, and the restart's change lands on it
   (`today-zombie-resume`); two live writers do the same
   (`today-two-writers`). Reproduced on Delta tables: the sink keeps a row
   the source deleted.
2. The conditional commit compared the value of the app's epoch (#964).
   A deploy replaced the table at the same epoch, and a write prepared
   against the old plan's commit passed the check (`today-aba`). A foreign
   commit between the read and the commit passed it too.
3. Versions of a source that cannot restore collided across processes
   (#965). Two processes starting from the same record numbered different
   contents with the same version; the sink skipped one as committed, then
   wrote a change on the other (`today-collision`), or stayed behind the
   source for good (`today-collision-stale`).
4. Rows another application changed were written over or kept (#966):
   `stored()` noticed them, the write path did not (`today-foreign`,
   `today-foreign-stale`).
5. #889 was allowed by safety and broke the documented promise: a new
   process rewrote in full a state it could resume from
   (`today-889-needless`), with the source unchanged too
   (`today-889-unchanged`). With a durable source neither happens
   (`today-durable-889` passes).

Also seen, and left as is: two live processes of two plans (a rolling
deploy) replace each other's state on every refresh until the old one
stops. The states are right; the log grows by one full copy per refresh
meanwhile.

## The fixes

Each `Fix*` constant switches on one change, the one sverify made for its
finding; the `fixed-*` configs turn on all of them and every property holds
there.

- `FixLast`: `Sink._commit` writes the change since `_written` only when the
  sink's record is the one this process wrote, skipped to or resumed from
  (its contract); otherwise it replaces the table.
- `FixCas`: the commit is conditional on the table version `contract()` read
  (Delta: commit from that `DeltaTable` with no retries, so any commit in
  between fails it; Iceberg: assert the snapshot id it read). Before the
  fix it was conditional on the value of the app's epoch, which another
  commit can repeat.
- `FixDigest`: a source that cannot restore records a digest of its content
  in the contract; an equal or higher recorded version with another digest is
  another state, so the process numbers its version above it and replaces;
  the pending-write check compares the digest too.
- `FixResume` (#889): such a source restores at the recorded version when its
  first read has the recorded digest, and a new process that computed the
  node writes the change against the stored table, read back.
- `FixForeign`: when a commit that changes rows follows the sink's last one,
  the next write replaces the table.

## Results

TLC 2.19 (`tla2tools.jar` v1.7.4), 4 workers, on homelab (12 cores), on
2026-11-06. Distinct states and seconds per config; every config found what
it expects.

| config | expects | distinct states | seconds |
|---|---|---:|---:|
| `fixed-two-writers` | pass | 2,121,735 | 80 |
| `fixed-two-writers-snapshot` | pass | 555,705 | 22 |
| `fixed-one-writer` | pass | 122,893 | 4 |
| `fixed-one-writer-snapshot` | pass | 157,039 | 4 |
| `fixed-liveness` | pass | 36,188 | 4 |
| `fixed-liveness-snapshot` | pass | 42,460 | 5 |
| `today-durable-889` | pass | 1,022 | 1 |
| `today-zombie-resume` | `NoCorruption` fails | 377 | 1 |
| `today-two-writers` | `NoCorruption` fails | 750 | 1 |
| `today-aba` | `ReadIsHead` fails | 1,490 | 1 |
| `today-collision` | `NoCorruption` fails | 765 | 1 |
| `today-collision-stale` | `Converges` fails | 566 | 1 |
| `today-foreign` | `NoCorruption` fails | 32 | 1 |
| `today-foreign-stale` | `Converges` fails | 8 | 1 |
| `today-889-needless` | `NoNeedlessRewrite` fails | 120 | 1 |
| `today-889-unchanged` | `NoRewriteUnchanged` fails | 33 | 0 |
| `witness-*` (4) | each fails | 123 to 2,811 | 1 |

The whole set takes about two minutes. The scopes: `fixed-two-writers` has
two writer slots, two plans, two source changes, one crash, one lost
acknowledgement and logs up to 6 commits; `fixed-one-writer` one slot, two
plans, two changes, two crashes, one lost acknowledgement and one foreign
writer; the snapshot variant of the two-writer config has one change.

The `deep-*` configs, on homelab with `DEEP=1`, pass as well:

| config | scope | distinct states | seconds |
|---|---|---:|---:|
| `deep-two-writers-snapshot` | two writers, two changes, a source that cannot restore | 6,486,822 | 267 |
| `deep-fixed-durable` | two writers and a foreign writer, a durable source | 12,280,414 | 404 |
| `deep-fixed-snapshot` | two writers and a foreign writer, a source that cannot restore | 38,352,684 | 1,571 |

What the reductions save, on `fixed-two-writers` (the same verdict in each):

| fingerprint | distinct states | seconds |
|---|---:|---:|
| `SlotSymmetry`, the whole log | 9,067,636 | 393 |
| `LogView`, no symmetry | 2,614,966 | 181 |
| `LogView` and `SlotSymmetry` | 2,121,735 | 115 |

These three ran with 3 workers while other jobs shared the box; `LogView`
alone takes `fixed-one-writer` from 173,357 to 122,893 states.

## Running TLC

TLC needs Java 11 or later and `tla2tools.jar` (v1.7.4):

```bash
mkdir -p ~/.local/share/tlaplus
curl -fsSL -o ~/.local/share/tlaplus/tla2tools.jar https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar
```

Then, from the repository root:

```bash
bash models/refresh/check.sh
```

```bash
TLC_OUT=/tmp/tlc bash models/refresh/check.sh today-zombie-resume && python3 models/refresh/trace.py /tmp/tlc/today-zombie-resume.out
```

`check.sh` runs every config in `configs/` except the `deep-*` ones (add
`DEEP=1`, or name them) and fails unless each finds what its first line
expects. `TLC_WORKERS` (2) and `TLC_HEAP` (2g) set TLC's threads and heap.
CI runs it in the `refresh-model` job when `models/` changes.

The safety configs fingerprint states by `LogView`: the log only grows, and
the next steps and the properties read only its length, the app's last
commit, the last commit and whether each property over the log still holds.
Liveness configs run without a view, which TLC does not support for them.
