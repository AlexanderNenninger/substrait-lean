# The refresh protocol: what the model found, and what is proved

A stored node refreshes while processes crash, restart, race each other and
lose acknowledgements. Sverify specified that protocol twice: as a TLA+ model
that TLC checked at small scopes (#933, step 1), and as a transition system in
Lean that proves its properties for every scope.
[`Refresh.lean`](../analysis/Sverify/Analysis/Refresh.lean) states it for a
durable source, and
[`RefreshSnapshot.lean`](../analysis/Sverify/Analysis/RefreshSnapshot.lean)
for a source that cannot restore (`from_frame`, #988). The TLA+ model is gone
since the Lean proofs cover everything it checked, apart from the fairness
half of convergence below; it is in the repository's history at `70599e49e`
(`models/refresh/`), with its traces.

## What the model found

Four ways the protocol of sverify 0.7 put the sink in a state it did not
record, and a verdict on #889. All are fixed.

1. A change landed on a commit the writer did not compute it from (#963).
   `Sink._commit` wrote the change since `_written` whenever the record had the
   same plan and a lower epoch, without checking the record was the one it
   wrote. One writer was enough: a restart resumes, the crashed process's
   write lands late, and the restart's change lands on it. Two live writers did
   the same. The sink kept a row the source had deleted.
2. The conditional commit compared the value of the app's epoch (#964). A
   deploy replaced the table at the same epoch, and a write prepared against
   the old plan's commit passed the check. A foreign commit between the read
   and the commit passed it too. The commit is now conditional on the table
   version `contract()` read.
3. Versions of a source that cannot restore collided across processes (#965).
   Two processes starting from the same record numbered different contents
   with the same version; the sink skipped one as committed, then wrote a
   change on the other, or stayed behind the source for good. The contract
   records a digest of the contents now, and a record of other contents at a
   version not below the writer's makes the writer number above it.
4. Rows another application changed were written over or kept (#966):
   `stored()` noticed them and the write path did not. The next write replaces
   the table.
5. #889 was allowed by safety and broke the documented promise: a new process
   rewrote in full a state it could resume from, also with the source
   unchanged. A durable source never did. A source that cannot restore now
   restores at the recorded version when its first read has the recorded
   digest.

Two live processes of two plans, in a rolling deploy, replace each other's
state on every refresh until the old one stops. The states are right and the
log grows by one full copy per refresh meanwhile.

## What is proved

Each property holds of every reachable state, for any number of writers,
crashes, late writes of crashed processes, lost acknowledgements, foreign
commits and deploys. They are listed with their theorems in
[proofs.md](proofs.md).

- No change is applied to a table it was not computed from, and the sink's
  record names its table.
- A change lands only on the newest commit of the node, computed against its
  table.
- Adjacent commits of one plan are of later versions (durable) or of other
  contents (source that cannot restore): no state is committed twice in a
  row.
- A restarted process resumes from the record and never rewrites it in full
  (#889).
- Every table and record an observer sees, with crashes, zombies and lost
  acknowledgements, is one a failure-free run reaches.
- Once the environment is quiet, the processes' own steps reach the deployed
  plan's state of the source and keep it.

`python/tests/test_refresh_next.py` and
`python/tests/test_refresh_snapshot_next.py` run each case of the models'
decision function against `Sink._commit`, so the two cannot drift.

## The one limit

The TLA+ model also checked `Converges` under weak fairness: if the processes
keep taking their steps, the sink ends up with the deployed plan's state of the
source. Lean proves what the steps do once taken. That the processes take them is an assumption.
The chaos suite ([`python/tests/chaos/`](../python/tests/chaos/)) exercises that
half by killing and restarting writers and checking that the sink converges.
