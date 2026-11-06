------------------------------ MODULE Refresh ------------------------------
(***************************************************************************)
(* The refresh protocol of one stored node: `node.write(sink)` refreshed   *)
(* by processes that crash, restart, race and lose acknowledgements (#933).*)
(*                                                                         *)
(* It follows the Python of sverify 0.7:                                   *)
(*   - `nodes.py`: `Group.refresh` (`_continue_versions`, then `_refresh`  *)
(*     with `_Stage.build`, which resumes from `sink._stored()`);          *)
(*   - `incremental.py`: `IncrementalView` (`_mismatch`, `resumed`);       *)
(*   - `io/_sink.py`: `Sink._commit` (the pending write, the plan and      *)
(*     table checks, the skip, the change since `_written`) and            *)
(*     `_TableSink.write` (the commit is conditional on the epoch of       *)
(*     `app_id` that `contract()` read, #517 #534);                        *)
(*   - `io/_source.py`: `Source._resume_after` (a source that cannot       *)
(*     `restore` numbers its versions above the recorded one);             *)
(*   - `io/delta.py`, `io/iceberg.py`: the contract in each commit, the    *)
(*     epoch read back, `stored()` only when no commit changed rows after  *)
(*     the sink's last one (`last_record(...).kept`).                      *)
(*                                                                         *)
(* Data is abstract. The node's rows are a function of its plan and of the *)
(* source's content: St(p, c). A write that applies a change to a table    *)
(* other than the one the change was computed from yields Corrupt (it may  *)
(* be right for some sinks and some changes; it is right for none in       *)
(* general). Foreign is a table another application changed.              *)
(*                                                                         *)
(* The Fix* constants switch on the fixes the README proposes; with all of *)
(* them FALSE the model is today's protocol.                               *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Slots,        \* writer slots: processes refreshing the node (model values)
    NumPlans,     \* plans deployed one after another: 1..NumPlans
    MaxChanges,   \* changes of the source's content
    MaxCrashes,   \* process crashes (each may leave a zombie write)
    MaxLostAcks,  \* writes that raise: committed or not, the writer cannot tell
    MaxForeign,   \* row-changing commits by another application
    MaxLog,       \* bound on the sink's log: LogBound checks one writer
                  \* stays below it; LogConstraint cuts two writers off at it
    Durable,      \* TRUE: the source's versions last across processes
                  \* (DeltaSource, IcebergSource, a Source with `restore`);
                  \* FALSE: they restart with the process (from_frame, #889)
    FixLast,      \* write a change only on top of the record this process
                  \* wrote, skipped to or resumed from (else the whole table)
    FixCas,       \* the commit is conditional on the table's version that
                  \* `contract()` read (no commit of any writer in between),
                  \* not on the value of the app's epoch
    FixDigest,    \* a source that cannot restore records a digest of its
                  \* content; an equal epoch with another digest is another
                  \* state
    FixResume,    \* #889: such a source restores at the recorded version
                  \* when its read has the recorded digest, and a new
                  \* process writes the change against the stored table
    FixForeign    \* a row-changing commit by another application after the
                  \* sink's last one makes the next write replace the table

VARIABLES
    src,       \* the source: [c: content, ver: version (durable sources)]
    log,       \* the sink's commits, oldest first
    tbl,       \* the sink's table
    w,         \* the writer slots
    zombies,   \* writes of crashed processes still in flight
    deployed,  \* the plan new processes start with
    n          \* how many of the bounded events happened

vars == <<src, log, tbl, w, zombies, deployed, n>>

-----------------------------------------------------------------------------
(* Table states. *)
St(p, c) == [k |-> "rows", plan |-> p, c |-> c]
Foreign  == [k |-> "foreign", plan |-> 0, c |-> 0]
Corrupt  == [k |-> "corrupt", plan |-> 0, c |-> 0]
Nothing  == [k |-> "none", plan |-> 0, c |-> 0]  \* no table / `_written = None`

TableStates ==
    {St(p, c) : p \in 1..NumPlans, c \in 0..MaxChanges} \cup {Foreign, Corrupt, Nothing}

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

(* The sink's record. *)
AppIdxs == {i \in 1..Len(log) : log[i].app}
AppIdx  == IF AppIdxs = {} THEN 0 ELSE Max(AppIdxs)  \* the app's last commit
Has     == AppIdx > 0
Rec     == log[AppIdx]                                \* only where Has
AppEpoch == IF Has THEN Rec.ver ELSE -1               \* `_epoch_of`: -1 for none
\* `last_record(...).kept`: no commit after the app's last one changed rows.
Kept    == Has /\ AppIdx = Len(log)

PrevApp(j) ==
    LET I == {i \in 1..(j - 1) : log[i].app} IN IF I = {} THEN 0 ELSE Max(I)

(* What a contract records that a writer compares: `Contract.plan`, the  *)
(* source version (`sources`, the epoch with one source) and the digest. *)
NoKey == [plan |-> 0, ver |-> -1, dig |-> -1]
Key(r) == [plan |-> r.plan, ver |-> r.ver, dig |-> r.dig]

(* The digest a contract records for the source's content: only with the *)
(* fixes, and only for a source that cannot restore (a durable source's  *)
(* version determines its content).                                      *)
Dig(c) == IF ~Durable /\ (FixDigest \/ FixResume) THEN c ELSE 0

NoPend == [on |-> FALSE, plan |-> 0, ver |-> -1, dig |-> 0, view |-> Nothing]
NoOut  == [plan |-> 0, ver |-> -1, c |-> 0, dig |-> 0, mode |-> "none",
           view |-> Nothing, written |-> Nothing, read |-> -1, base |-> 0, head |-> 0,
           needless |-> FALSE, by |-> "none"]

(* A process's memory: lost when it crashes. Fields only some fixes or   *)
(* properties read are kept constant otherwise, so that they do not split *)
(* states (`last` without FixLast).                                       *)
Down == [st |-> "down", plan |-> 0, first |-> TRUE, ver |-> 0, c |-> 0,
         view |-> Nothing, written |-> Nothing, last |-> NoKey, pend |-> NoPend,
         resumable |-> 0, out |-> NoOut]

Last(k) == IF FixLast THEN k ELSE NoKey

-----------------------------------------------------------------------------
Init ==
    /\ src = [c |-> 0, ver |-> 0]
    /\ log = <<>>
    /\ tbl = Nothing
    /\ w = [s \in Slots |-> Down]
    /\ zombies = {}
    /\ deployed = 1
    /\ n = [changes |-> 0, crashes |-> 0, lost |-> 0, foreign |-> 0, zombies |-> 0]

(* A process starts, with the plan deployed now. *)
Start(s) ==
    /\ w[s].st = "down"
    /\ w' = [w EXCEPT ![s] = [Down EXCEPT !.st = "idle", !.plan = deployed]]
    /\ UNCHANGED <<src, log, tbl, zombies, deployed, n>>

(* A process whose plan is no longer deployed is stopped between refreshes *)
(* (a deploy restarts the jobs).                                           *)
Stop(s) ==
    /\ w[s].st = "idle"
    /\ w[s].plan # deployed
    /\ w' = [w EXCEPT ![s] = Down]
    /\ UNCHANGED <<src, log, tbl, zombies, deployed, n>>

(* `refresh()` up to the write: read the source; on the first refresh of a *)
(* process, `_continue_versions` and `_Stage.build` (resume from what the  *)
(* sink stored, or compute); later, apply the source's change to the view. *)
Refresh(s) ==
    LET me == w[s]
        first == me.first
        \* `Source._resume_after` with `restore`: the FixResume source restores
        \* when its first read has the digest the sink recorded.
        restored == ~Durable /\ FixResume /\ first /\ Has /\ Rec.dig = src.c
        ver == IF Durable THEN src.ver
               ELSE IF first THEN (IF restored THEN Rec.ver
                                   ELSE (IF Has THEN Rec.ver ELSE 0) + 1)
               ELSE IF src.c # me.c THEN me.ver + 1 ELSE me.ver
        \* `_Stage.build`: `stored()` (the last commit is the sink's), the
        \* stored versions not above the pipeline's, `_mismatch` (same plan),
        \* and the source can give the stored version (a source that cannot
        \* restore keeps only the versions of this process).
        same == Has /\ Kept /\ Rec.plan = me.plan
        resume == same /\ Rec.ver <= ver /\ (Durable \/ Rec.ver = ver)
        \* Resumed: the table read back, then the source's change since the
        \* stored version; right only if the table is the recorded state.
        view == IF ~first
                  THEN (IF me.view.k = "rows" THEN St(me.plan, src.c) ELSE me.view)
                ELSE IF resume
                  THEN (IF tbl = St(me.plan, Rec.c) THEN St(me.plan, src.c) ELSE Corrupt)
                ELSE St(me.plan, src.c)
        \* FixResume: computed, the write is the change against the table.
        readBack == resume \/ (FixResume /\ same)
    IN
    /\ me.st = "idle"
    /\ w' = [w EXCEPT ![s] = [me EXCEPT
            !.st = "ready", !.first = FALSE, !.ver = ver, !.c = src.c, !.view = view,
            !.written = IF first THEN (IF readBack THEN tbl ELSE Nothing) ELSE me.written,
            !.last = IF first THEN Last(IF readBack THEN Key(Rec) ELSE NoKey) ELSE me.last,
            !.resumable = IF first /\ same THEN AppIdx ELSE 0]]
    /\ UNCHANGED <<src, log, tbl, zombies, deployed, n>>

(* `Sink._commit` up to the commit: read the sink's record (`contract()`), *)
(* then skip the state, or write the table or the change since `_written`. *)
Prepare(s) ==
    LET me == w[s]
        \* The last write raised after its commit landed: write on from it.
        \* (`(done.plan, done.epoch) == (pending.plan, pending.epoch)`; with
        \* FixDigest, and the digest.)
        hit == me.pend.on /\ Has /\ Rec.plan = me.pend.plan /\ Rec.ver = me.pend.ver
               /\ (FixDigest => Rec.dig = me.pend.dig)
        written0 == IF hit THEN me.pend.view ELSE me.written
        last0 == IF hit THEN Last(Key(Rec)) ELSE me.last
        other == Has /\ Rec.plan # me.plan               \* another plan's rows
        foreign == FixForeign /\ Has /\ ~Kept
        stale == FixLast /\ Has /\ Key(Rec) # last0
        \* FixDigest: the versions of a source that cannot restore are this
        \* process's; the digest says whether the sink holds this content.
        \* Another content at a version not below ours: number ours above it.
        clash == FixDigest /\ ~Durable /\ Has /\ ~other
                 /\ Rec.ver >= me.ver /\ Rec.dig # Dig(me.c)
        ver == IF clash THEN Rec.ver + 1 ELSE me.ver
        written == IF other \/ foreign \/ stale \/ clash THEN Nothing ELSE written0
        \* The sink has this very state: the same version, or with FixDigest
        \* the same content whatever the version.
        same == Has /\ ~other /\ ~foreign
                /\ IF FixDigest /\ ~Durable THEN Rec.dig = Dig(me.c) ELSE Rec.ver = me.ver
        \* `done.epoch >= contract.epoch`: the sink has this state, or a later one.
        skip == same \/ (Has /\ ~other /\ ~foreign /\ ~clash /\ Rec.ver >= ver)
        here == same
        mode == IF written = Nothing THEN "replace" ELSE "merge"
        out == [plan |-> me.plan, ver |-> ver, c |-> me.c, dig |-> Dig(me.c),
                mode |-> mode, view |-> me.view, written |-> written,
                read |-> AppEpoch, base |-> AppIdx, head |-> Len(log),
                \* #889: a new process rewrites in full the state it could
                \* have resumed from.
                needless |-> mode = "replace" /\ me.resumable # 0
                             /\ me.resumable = AppIdx /\ Kept,
                by |-> s]
    IN
    /\ me.st = "ready"
    /\ IF skip
         THEN w' = [w EXCEPT ![s] = [me EXCEPT
                !.st = "idle", !.pend = NoPend, !.resumable = 0,
                !.ver = IF here THEN Rec.ver ELSE me.ver,
                !.written = IF here THEN me.view ELSE Nothing,
                !.last = Last(IF here THEN Key(Rec) ELSE NoKey)]]
         ELSE w' = [w EXCEPT ![s] = [me EXCEPT
                !.st = "writing", !.out = out, !.written = written, !.last = last0,
                !.resumable = 0, !.ver = ver,
                !.pend = [on |-> TRUE, plan |-> me.plan, ver |-> ver, dig |-> Dig(me.c),
                          view |-> me.view]]]
    /\ UNCHANGED <<src, log, tbl, zombies, deployed, n>>

(* The table format's conditional commit: today, while the app's epoch is  *)
(* the one `contract()` read; with FixCas, while the table is at the       *)
(* version it read.                                                         *)
CasOK(o) == IF FixCas THEN Len(log) = o.head ELSE AppEpoch = o.read

NewTbl(o) ==
    IF o.mode = "replace" THEN o.view
    ELSE IF tbl = o.written THEN o.view ELSE Corrupt

Entry(o) == [app |-> TRUE, plan |-> o.plan, ver |-> o.ver, c |-> o.c, dig |-> o.dig,
             mode |-> o.mode, base |-> o.base, needless |-> o.needless, by |-> o.by]

ForeignEntry == [app |-> FALSE, plan |-> 0, ver |-> -1, c |-> 0, dig |-> 0,
                 mode |-> "foreign", base |-> 0, needless |-> FALSE, by |-> "other"]

Commit(o) ==
    /\ CasOK(o)
    /\ log' = Append(log, Entry(o))
    /\ tbl' = NewTbl(o)

(* The write commits and returns. *)
Land(s) ==
    /\ w[s].st = "writing"
    /\ Commit(w[s].out)
    /\ w' = [w EXCEPT ![s] = [@ EXCEPT !.st = "idle", !.written = w[s].out.view,
                                       !.last = Last(Key(w[s].out)), !.pend = NoPend,
                                       !.out = NoOut]]
    /\ UNCHANGED <<src, zombies, deployed, n>>

(* The write commits, then raises (the acknowledgement is lost): the       *)
(* process keeps `_pending`.                                                *)
LandLostAck(s) ==
    /\ w[s].st = "writing"
    /\ n.lost < MaxLostAcks
    /\ Commit(w[s].out)
    /\ w' = [w EXCEPT ![s] = [@ EXCEPT !.st = "idle", !.out = NoOut]]
    /\ n' = [n EXCEPT !.lost = @ + 1]
    /\ UNCHANGED <<src, zombies, deployed>>

(* The write raises without committing. *)
Fail(s) ==
    /\ w[s].st = "writing"
    /\ n.lost < MaxLostAcks
    /\ w' = [w EXCEPT ![s] = [@ EXCEPT !.st = "idle", !.out = NoOut]]
    /\ n' = [n EXCEPT !.lost = @ + 1]
    /\ UNCHANGED <<src, log, tbl, zombies, deployed>>

(* `ConcurrentWriteError`: another writer committed first. *)
Conflict(s) ==
    /\ w[s].st = "writing"
    /\ ~CasOK(w[s].out)
    /\ w' = [w EXCEPT ![s] = [@ EXCEPT !.st = "idle", !.pend = NoPend, !.written = Nothing,
                                       !.out = NoOut]]
    /\ UNCHANGED <<src, log, tbl, zombies, deployed, n>>

(* A process dies; a write it had sent may still land. *)
Crash(s) ==
    /\ w[s].st # "down"
    /\ n.crashes < MaxCrashes
    /\ zombies' = IF w[s].st = "writing" THEN zombies \cup {w[s].out} ELSE zombies
    /\ w' = [w EXCEPT ![s] = Down]
    /\ n' = [n EXCEPT !.crashes = @ + 1]
    /\ UNCHANGED <<src, log, tbl, deployed>>

(* A dead process's write lands late (a zombie). *)
ZombieLands(o) ==
    /\ Commit(o)
    /\ zombies' = zombies \ {o}
    /\ n' = [n EXCEPT !.zombies = @ + 1]
    /\ UNCHANGED <<src, w, deployed>>

(* The source's content changes: a new version of a durable source; a new  *)
(* snapshot for a source that cannot restore.                              *)
SourceChanges ==
    /\ n.changes < MaxChanges
    /\ src' = [c |-> src.c + 1, ver |-> IF Durable THEN src.ver + 1 ELSE 0]
    /\ n' = [n EXCEPT !.changes = @ + 1]
    /\ UNCHANGED <<log, tbl, w, zombies, deployed>>

(* Another application changes the sink's rows. *)
ForeignWrite ==
    /\ n.foreign < MaxForeign
    /\ Has
    /\ log' = Append(log, ForeignEntry)
    /\ tbl' = Foreign
    /\ n' = [n EXCEPT !.foreign = @ + 1]
    /\ UNCHANGED <<src, w, zombies, deployed>>

(* A new plan is deployed; running processes keep theirs until stopped. *)
Deploy ==
    /\ deployed < NumPlans
    /\ deployed' = deployed + 1
    /\ UNCHANGED <<src, log, tbl, w, zombies, n>>

Writer(s) ==
    \/ Start(s) \/ Stop(s) \/ Refresh(s) \/ Prepare(s)
    \/ Land(s) \/ LandLostAck(s) \/ Fail(s) \/ Conflict(s) \/ Crash(s)

Next ==
    \/ \E s \in Slots : Writer(s)
    \/ \E o \in zombies : ZombieLands(o)
    \/ SourceChanges \/ ForeignWrite \/ Deploy

(* Processes run their refreshes (a process of an old plan is stopped    *)
(* between two of them: strong fairness, as it is idle only now and then); *)
(* crashes, zombies, lost acknowledgements, *)
(* source changes, foreign writes and deploys may or may not happen.        *)
Fairness ==
    \A s \in Slots :
        /\ WF_vars(Start(s)) /\ SF_vars(Stop(s)) /\ WF_vars(Refresh(s))
        /\ WF_vars(Prepare(s)) /\ WF_vars(Land(s) \/ Conflict(s))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties. The numbers are those of #933.                              *)

TypeOK ==
    /\ tbl \in TableStates
    /\ \A s \in Slots : w[s].st \in {"down", "idle", "ready", "writing"}
    /\ deployed \in 1..NumPlans

(* 2, 4. A change is applied only to the state it was computed from. *)
NoCorruption == tbl # Corrupt

(* 4. The refinement, on the sink: when the app's commit is the last one,  *)
(* the table is the state of the plan and the source content it records.   *)
RecordDescribesTable == Kept => tbl = St(Rec.plan, Rec.c)

(* 3. A stale record cannot commit: when a change commits, the commit    *)
(* `contract()` read is still the app's last (no other commit of the app *)
(* passed the compare-and-swap in between).                              *)
ReadIsHead ==
    \A j \in 1..Len(log) :
        log[j].app /\ log[j].mode = "merge" => log[j].base = PrevApp(j)

(* 1, 5. Versions never go down under one plan, and no state is committed *)
(* twice: consecutive commits of a plan are of distinct source states.    *)
(* A commit right after another application's rows may write the same     *)
(* state again: it repairs the table.                                     *)
Monotone ==
    \A j \in 2..Len(log) :
        LET i == j - 1 IN
        log[j].app /\ log[i].app /\ log[i].plan = log[j].plan =>
            /\ log[j].ver >= log[i].ver
            /\ <<log[j].ver, log[j].c>> # <<log[i].ver, log[i].c>>

(* #889. A new process does not rewrite in full a state it could resume. *)
NoNeedlessRewrite == \A j \in 1..Len(log) : ~log[j].needless

(* #889. A refresh whose source content is what the sink records commits *)
(* nothing ("a read that changes nothing is no new version").            *)
NoRewriteUnchanged ==
    \A j \in 2..Len(log) :
        LET i == j - 1 IN
        log[j].app /\ log[i].app /\ log[i].plan = log[j].plan => log[j].c # log[i].c

(* Liveness: once the source and the deploys stop, the sink ends up with   *)
(* the deployed plan's state of the source, and keeps it.                  *)
Converges == <>[](tbl = St(deployed, src.c))

-----------------------------------------------------------------------------
(* Witnesses: invariants that must FAIL, so that the model reaches the     *)
(* states it is about and no property above holds vacuously.               *)
NoZombieLanded == n.zombies = 0
NoLostAckResumed == ~(\E s \in Slots : w[s].pend.on /\ w[s].st = "ready")
NoMerge == \A j \in 1..Len(log) : log[j].mode # "merge"
NoConflictReplace ==
    \A j \in 1..Len(log) : ~(log[j].app /\ log[j].mode = "replace" /\ PrevApp(j) > 0
                             /\ log[PrevApp(j)].plan = log[j].plan)

(* With one writer the log stays below MaxLog by itself. Two live          *)
(* processes of two plans (a rolling deploy) replace each other's state on *)
(* every refresh until the old one stops, so with two writers the runs     *)
(* explore the logs up to MaxLog commits (a state constraint).             *)
LogBound == Len(log) < MaxLog
LogConstraint == Len(log) <= MaxLog

-----------------------------------------------------------------------------
(* What TLC fingerprints in the safety runs (VIEW in their configs). The    *)
(* log only grows, and what the next steps and the properties read of it is *)
(* its length, the app's last commit, the last commit, and whether each     *)
(* property over the log still holds (it stays false once false): two      *)
(* histories that agree on these have the same futures and the same verdict.*)
(* Not for liveness runs, which TLC checks without a view.                  *)
Strip(e) == [e EXCEPT !.by = "-"]
LogView ==
    <<src, tbl, w, zombies, deployed, n, Len(log), AppIdx,
      IF Has THEN Strip(Rec) ELSE ForeignEntry,
      IF log = <<>> THEN ForeignEntry ELSE Strip(log[Len(log)]),
      ReadIsHead, Monotone, NoNeedlessRewrite, NoRewriteUnchanged>>

(* Symmetry of the writer slots, for the safety runs. *)
SlotSymmetry == Permutations(Slots)
=============================================================================
