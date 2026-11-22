/-
The refresh protocol of one stored node as a transition system (#933, step 2).

`models/refresh/Refresh.tla` explores the protocol with TLC at small scopes;
this module states the protocol sverify runs since #963, #964 and #966 (the
model's `FixLast`, `FixCas` and `FixForeign`) for a durable source, and proves
its safety for every scope: any number of writers, crashes, zombie writes,
lost acknowledgements, foreign commits and deploys.

The data is abstract, as in the TLA+ model: the node's rows are `Tbl.rows p v`,
a function of the plan `p` and of the source's version `v` (a durable source's
version names its contents). A change written on a table it was not computed
from yields `Tbl.corrupt`.

What it models of `python/src/sverify`:

* `World.refresh`: `Group.refresh` up to the write (`_Stage.build` resumes from
  the sink's record on a process's first refresh, when no other commit
  followed it and the plan is the same).
* `next`: `Sink._commit`'s decision: skip, replace, or write the change on
  the record this process wrote, skipped to or resumed from (`_synced`, #963),
  never on rows another application changed (`_foreign`, #966).
* `World.commit` under `log.length = o.head`: the table format's conditional
  commit on the version `contract()` read (#964).
* Crashes leave the write in flight (`zombies`), which may land later; a write
  that raises keeps `_pending`.

What it assumes, and so what the theorems do not cover:

* A durable source. Its version names its contents and only grows, and its
  table is not dropped and created again: `World.src` is one counter, and
  `Tbl.rows p v` is the state of plan `p` at version `v`. A source that cannot
  restore (`from_frame`), whose versions count one process's reads (#965),
  and a source recreated with lower versions (`table_ids`, #516, #1025) are
  outside the model; the TLA+ model checks the first at small scopes.
* `Sink._commit` decides as `next` does. `python/tests/test_refresh_next.py`
  checks it case by case.
-/

namespace Substrait
namespace Refresh

/-- The sink's table. -/
inductive Tbl where
  | none
  | rows (plan ver : Nat)
  | foreign
  | corrupt
  deriving DecidableEq, Repr

/-- What a commit's contract says of its state: the plan and the source's
version. -/
structure Key where
  plan : Nat
  ver : Nat
  deriving DecidableEq, Repr

/-- The rows a key names. -/
def Key.tbl (k : Key) : Tbl := .rows k.plan k.ver

/-- A commit of the sink's log: the node's (`app`), or another application's. -/
structure Commit where
  app : Bool
  key : Key
  deriving DecidableEq, Repr

inductive Mode where
  | replace
  | merge
  deriving DecidableEq, Repr

/-- A write in flight: its key, whether it replaces the rows or applies a
change computed against `base`, and the log length `contract()` read. -/
structure Out where
  key : Key
  mode : Mode
  base : Tbl
  head : Nat
  deriving DecidableEq, Repr

inductive Phase where
  | down
  | idle
  | ready
  | writing (o : Out)
  deriving DecidableEq, Repr

/-- A process refreshing the node: its plan, its view's version, the record
of the state it wrote, skipped to or resumed from (`_written` with
`_synced`), and a write that raised (`_pending`). -/
structure Writer where
  phase : Phase := .down
  plan : Nat := 0
  first : Bool := true
  ver : Nat := 0
  written : Option Key := none
  pend : Option Key := none
  /-- Ghost: the record the process's first refresh could resume from, until
  its first `prepare` (`needless` in the TLA+ model, #889). -/
  resumable : Option Key := none
  deriving DecidableEq, Repr

/-- The source's latest version, the sink's log (newest first) and table,
the writer slots, the writes of crashed processes still in flight, and the
plan new processes start with. -/
structure World where
  src : Nat := 0
  log : List Commit := []
  tbl : Tbl := .none
  ws : Nat → Writer := fun _ => {}
  zombies : List Out := []
  deployed : Nat := 0

def upd (f : Nat → Writer) (i : Nat) (w : Writer) : Nat → Writer :=
  fun j => if j = i then w else f j

/-- The record of the node's last commit (`contract()`). -/
def record (log : List Commit) : Option Key := (log.find? (·.app)).map (·.key)

/-- The node's last commit is the newest: no other application changed rows
since (`last_record(...).kept`). -/
def kept : List Commit → Bool
  | c :: _ => c.app
  | [] => false

inductive Decision where
  | skip (written : Option Key)
  | write (mode : Mode) (written : Option Key)
  deriving DecidableEq, Repr

/-- `Sink._commit`'s decision, from the sink's record and the writer's own
state alone. `python/tests/test_refresh_next.py` runs each of its cases
against `Sink._commit`: change both together. -/
def next (rec : Option Key) (kept : Bool) (w : Writer) : Decision :=
  -- The last write raised after its commit landed: write on from it.
  let w0 : Option Key := if w.pend.isSome && w.pend == rec then w.pend else w.written
  match rec with
  | none => .write .replace none
  | some r =>
    if r.plan != w.plan then .write .replace none -- another plan's rows
    else if !kept then .write .replace none -- another application's rows (#966)
    else if w.ver ≤ r.ver then .skip (if r.ver == w.ver then some r else none)
    else if w0 == some r then .write .merge (some r) -- on its own record (#963)
    else .write .replace none

/-- A write commits: the rows, or the change applied to the table. -/
def newTbl (o : Out) (t : Tbl) : Tbl :=
  match o.mode with
  | .replace => o.key.tbl
  | .merge => if t = o.base then o.key.tbl else .corrupt

namespace World

def start (s : World) (i : Nat) : World :=
  { s with ws := upd s.ws i { phase := .idle, plan := s.deployed } }

def stop (s : World) (i : Nat) : World :=
  { s with ws := upd s.ws i {} }

def refresh (s : World) (i : Nat) : World :=
  let w := s.ws i
  let resumed : Option Key :=
    match record s.log with
    | some r => if kept s.log && r.plan == w.plan && decide (r.ver ≤ s.src) then some r else none
    | none => none
  { s with ws := upd s.ws i { w with phase := .ready, first := false, ver := s.src,
                                     written := if w.first then resumed else w.written,
                                     resumable := if w.first then resumed else none } }

def prepare (s : World) (i : Nat) : World :=
  let w := s.ws i
  match next (record s.log) (kept s.log) w with
  | .skip wr =>
    { s with ws := upd s.ws i { w with phase := .idle, written := wr, pend := none,
                                       resumable := none } }
  | .write m wr =>
    let o : Out := ⟨⟨w.plan, w.ver⟩, m, (wr.map Key.tbl).getD .none, s.log.length⟩
    { s with ws := upd s.ws i { w with phase := .writing o, written := wr,
                                       pend := some ⟨w.plan, w.ver⟩, resumable := none } }

def commit (s : World) (o : Out) : World :=
  { s with log := ⟨true, o.key⟩ :: s.log, tbl := newTbl o s.tbl }

def crash (s : World) (i : Nat) : World :=
  { s with ws := upd s.ws i {},
           zombies := match (s.ws i).phase with
             | .writing o => o :: s.zombies
             | _ => s.zombies }

end World

/-- One step of the protocol or of its environment. -/
inductive Step : World → World → Prop where
  | start (s i) : (s.ws i).phase = .down → Step s (s.start i)
  | stop (s i) : (s.ws i).phase = .idle → (s.ws i).plan ≠ s.deployed → Step s (s.stop i)
  | refresh (s i) : (s.ws i).phase = .idle → Step s (s.refresh i)
  | prepare (s i) : (s.ws i).phase = .ready → Step s (s.prepare i)
  | land (s i o) : (s.ws i).phase = .writing o → s.log.length = o.head →
      Step s { s.commit o with
        ws := upd s.ws i { s.ws i with phase := .idle, written := some o.key, pend := none } }
  | landLostAck (s i o) : (s.ws i).phase = .writing o → s.log.length = o.head →
      Step s { s.commit o with ws := upd s.ws i { s.ws i with phase := .idle } }
  | fail (s i o) : (s.ws i).phase = .writing o →
      Step s { s with ws := upd s.ws i { s.ws i with phase := .idle } }
  | conflict (s i o) : (s.ws i).phase = .writing o → s.log.length ≠ o.head →
      Step s { s with ws := upd s.ws i { s.ws i with phase := .idle, written := none,
                                                     pend := none } }
  | crash (s i) : (s.ws i).phase ≠ .down → Step s (s.crash i)
  | zombieLands (s o) : o ∈ s.zombies → s.log.length = o.head →
      Step s { s.commit o with zombies := s.zombies.erase o }
  | sourceChanges (s) : Step s { s with src := s.src + 1 }
  | foreignWrite (s) : Step s { s with log := ⟨false, ⟨0, 0⟩⟩ :: s.log, tbl := .foreign }
  | deploy (s) : Step s { s with deployed := s.deployed + 1 }

inductive Reachable : World → Prop where
  | init : Reachable {}
  | step {s t} : Reachable s → Step s t → Reachable t

/-! ## The invariant -/

/-- The table is what the newest commit says: the node's rows, or another
application's. -/
def TblOK (s : World) : Prop :=
  match s.log with
  | [] => s.tbl = .none
  | c :: _ => if c.app then s.tbl = c.key.tbl else s.tbl = .foreign

/-- A write in flight: a writer's, or a crashed process's. -/
def Pending (s : World) (o : Out) : Prop :=
  (∃ i, (s.ws i).phase = .writing o) ∨ o ∈ s.zombies

/-- A write in flight read a log no longer than the current one, and while
the log is still the one it read, its change was computed against the table. -/
def OutOK (s : World) (o : Out) : Prop :=
  o.head ≤ s.log.length ∧ (o.mode = .merge → s.log.length = o.head → s.tbl = o.base)

def Inv (s : World) : Prop := TblOK s ∧ ∀ o, Pending s o → OutOK s o

theorem upd_same (f : Nat → Writer) (i : Nat) (w : Writer) : upd f i w i = w := by
  simp [upd]

theorem upd_other (f : Nat → Writer) {i j : Nat} (w : Writer) (h : j ≠ i) :
    upd f i w j = f j := by
  simp [upd, h]

/-- After an update of slot `i` to a writer that is not writing, a write in
flight was in flight before. -/
theorem pending_upd {s : World} {i : Nat} {w : Writer} {o : Out}
    (hw : ∀ o', w.phase ≠ .writing o') (h : Pending { s with ws := upd s.ws i w } o) :
    Pending s o := by
  rcases h with ⟨j, hj⟩ | hz
  · change (upd s.ws i w j).phase = _ at hj
    by_cases hji : j = i
    · subst hji; rw [upd_same] at hj; exact absurd hj (hw o)
    · exact Or.inl ⟨j, by rw [upd_other _ _ hji] at hj; exact hj⟩
  · exact Or.inr hz

/-- A step that keeps the log and the table, and starts no write. -/
theorem inv_of_keep {s t : World} (hs : Inv s) (hlog : t.log = s.log) (htbl : t.tbl = s.tbl)
    (hp : ∀ o, Pending t o → Pending s o) : Inv t := by
  refine ⟨?_, fun o ho => ?_⟩
  · have := hs.1; unfold TblOK at this ⊢; rw [hlog, htbl]; exact this
  · have := hs.2 o (hp o ho); unfold OutOK at this ⊢; rw [hlog, htbl]; exact this

/-- The record of a log whose newest commit is the node's is that commit's. -/
theorem record_of_kept {log : List Commit} (h : kept log = true) :
    ∃ c rest, log = c :: rest ∧ c.app = true ∧ record log = some c.key := by
  cases log with
  | nil => simp [kept] at h
  | cons c rest =>
    simp only [kept] at h
    exact ⟨c, rest, rfl, h, by simp [record, List.find?, h]⟩

/-- `next` writes a change only on the sink's record, and only when no other
application's commit followed it. -/
theorem next_merge {rec : Option Key} {k : Bool} {w : Writer} {wr : Option Key}
    (h : next rec k w = .write .merge wr) : ∃ r, rec = some r ∧ wr = some r ∧ k = true := by
  cases rec with
  | none => simp [next] at h
  | some r =>
    simp only [next] at h
    refine ⟨r, rfl, ?_⟩
    repeat' split at h
    all_goals simp_all

/-- A commit of `o` when the log is the one `o` read, and `o`'s change (if
it is one) was computed against the table: the invariant holds after it,
for every write in flight after it that was in flight before. -/
theorem inv_commit {s t : World} {o : Out} (hs : Inv s) (hpo : Pending s o)
    (hc : s.log.length = o.head) (hlog : t.log = ⟨true, o.key⟩ :: s.log)
    (htbl : t.tbl = newTbl o s.tbl) (hp : ∀ o', Pending t o' → Pending s o') : Inv t := by
  have ho := hs.2 o hpo
  refine ⟨?_, fun o' ho' => ?_⟩
  · unfold TblOK; rw [hlog, htbl]
    simp only [↓reduceIte]
    unfold newTbl
    cases hm : o.mode with
    | replace => rfl
    | merge => simp [ho.2 hm hc]
  · have h' := hs.2 o' (hp o' ho')
    unfold OutOK at h' ⊢
    rw [hlog]
    simp only [List.length_cons]
    refine ⟨Nat.le_succ_of_le h'.1, fun _ heq => ?_⟩
    have := h'.1
    omega

theorem inv_step {s t : World} (hs : Inv s) (h : Step s t) : Inv t := by
  cases h with
  | start i _ =>
    exact inv_of_keep hs rfl rfl fun o ho => pending_upd (by intro o' h; cases h) ho
  | stop i _ _ =>
    exact inv_of_keep hs rfl rfl fun o ho => pending_upd (by intro o' h; cases h) ho
  | refresh i _ =>
    exact inv_of_keep hs rfl rfl fun o ho => pending_upd (by intro o' h; cases h) ho
  | prepare i hr =>
    cases hnext : next (record s.log) (kept s.log) (s.ws i) with
    | skip wr =>
      simp only [World.prepare, hnext]
      exact inv_of_keep hs rfl rfl fun o ho => pending_upd (by intro o' h; cases h) ho
    | write m wr =>
      simp only [World.prepare, hnext]
      refine ⟨hs.1, fun o ho => ?_⟩
      rcases ho with ⟨j, hj⟩ | hz
      · dsimp only at hj
        by_cases hji : j = i
        · subst hji
          rw [upd_same] at hj
          simp only [Phase.writing.injEq] at hj
          subst hj
          refine ⟨Nat.le_refl _, fun hm _ => ?_⟩
          simp only at hm
          subst hm
          obtain ⟨r, hrec, hwr, hk⟩ := next_merge hnext
          obtain ⟨c, rest, hlog, happ, hrc⟩ := record_of_kept hk
          have ht := hs.1
          unfold TblOK at ht
          rw [hlog] at ht
          simp only [happ, ↓reduceIte] at ht
          rw [hrec] at hrc
          simp only [Option.some.injEq] at hrc
          subst hwr
          simp [ht, hrc]
        · rw [upd_other _ _ hji] at hj
          exact hs.2 o (Or.inl ⟨j, hj⟩)
      · exact hs.2 o (Or.inr hz)
  | land i o hw hc =>
    refine inv_commit hs (Or.inl ⟨i, hw⟩) hc rfl rfl fun o' ho' => ?_
    exact pending_upd (s := s.commit o) (by intro o' h; cases h) ho'
  | landLostAck i o hw hc =>
    refine inv_commit hs (Or.inl ⟨i, hw⟩) hc rfl rfl fun o' ho' => ?_
    have hw' : ∀ o'', ({ s.ws i with phase := .idle } : Writer).phase ≠ .writing o'' := by
      intro o'' h; cases h
    exact pending_upd (s := s.commit o) hw' ho'
  | fail i o _ =>
    exact inv_of_keep hs rfl rfl fun o' ho' => pending_upd (by intro o'' h; cases h) ho'
  | conflict i o _ _ =>
    exact inv_of_keep hs rfl rfl fun o' ho' => pending_upd (by intro o'' h; cases h) ho'
  | crash i _ =>
    apply inv_of_keep (t := s.crash i) hs rfl rfl
    intro o ho
    unfold World.crash at ho
    rcases ho with ⟨j, hj⟩ | hz
    · dsimp only at hj
      by_cases hji : j = i
      · subst hji; simp [upd_same] at hj
      · exact Or.inl ⟨j, by simpa [upd_other _ _ hji] using hj⟩
    · simp only at hz
      split at hz
      · next o' hph =>
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inl ⟨i, hph⟩
        · exact Or.inr hz
      · exact Or.inr hz
  | zombieLands o hz hc =>
    refine inv_commit hs (Or.inr hz) hc rfl rfl fun o' ho' => ?_
    rcases ho' with ⟨j, hj⟩ | hz'
    · exact Or.inl ⟨j, hj⟩
    · exact Or.inr (List.mem_of_mem_erase hz')
  | sourceChanges =>
    exact inv_of_keep hs rfl rfl fun o ho => ho
  | foreignWrite =>
    refine ⟨by simp [TblOK], fun o ho => ?_⟩
    have h' := hs.2 o ho
    unfold OutOK at h' ⊢
    simp only [List.length_cons]
    refine ⟨Nat.le_succ_of_le h'.1, fun _ heq => ?_⟩
    have := h'.1
    omega
  | deploy =>
    exact inv_of_keep hs rfl rfl fun o ho => ho

theorem inv_init : Inv ({} : World) :=
  ⟨rfl, fun o ho => by rcases ho with ⟨_, h⟩ | h <;> cases h⟩

theorem inv_reachable {s : World} (h : Reachable s) : Inv s := by
  induction h with
  | init => exact inv_init
  | step _ hst ih => exact inv_step ih hst

end Refresh

open Refresh

/-! ## Safety -/

/-- No reachable state has a change applied to a table it was not computed
from (#933, invariants 2 and 4). -/
theorem Refresh.no_corruption {s : World} (h : Reachable s) : s.tbl ≠ .corrupt := by
  have ht := (inv_reachable h).1
  unfold TblOK at ht
  split at ht
  · rw [ht]; simp
  · split at ht <;> rw [ht] <;> simp [Key.tbl]

/-- When the node's commit is the newest, the table is the state its record
names (#933, invariant 4: the sink's record describes the sink). -/
theorem Refresh.record_describes_table {s : World} (h : Reachable s) (hk : kept s.log = true) :
    ∃ r, record s.log = some r ∧ s.tbl = r.tbl := by
  obtain ⟨c, rest, hlog, happ, hrc⟩ := record_of_kept hk
  have ht := (inv_reachable h).1
  unfold TblOK at ht
  rw [hlog] at ht
  simp only [happ, ↓reduceIte] at ht
  exact ⟨c.key, hrc, ht⟩

/-! ## Witnesses

The safety theorems hold of every reachable state; these reachable states
show that the states they are about exist: a change merged on the writer's
own commit, and the write of a crashed process landing late. -/

/-- One writer writes the node at v0, the source changes, and the writer
merges the change: the table holds v1. -/
theorem Refresh.merge_reachable : ∃ s, Reachable s ∧ s.log.length = 2 ∧ s.tbl = .rows 0 1 := by
  have r1 : Reachable (({} : World).start 0) := .step .init (.start _ 0 rfl)
  have r2 := r1.step (.refresh _ 0 rfl)
  have r3 := r2.step (.prepare _ 0 rfl)
  have r4 := r3.step (.land _ 0 ⟨⟨0, 0⟩, .replace, .none, 0⟩ rfl rfl)
  have r5 := r4.step (.sourceChanges _)
  have r6 := r5.step (.refresh _ 0 rfl)
  have r7 := r6.step (.prepare _ 0 rfl)
  have r8 := r7.step (.land _ 0 ⟨⟨0, 1⟩, .merge, .rows 0 0, 1⟩ rfl rfl)
  exact ⟨_, r8, rfl, rfl⟩

/-- A writer crashes with its write in flight; the write lands afterwards,
while a new process of the same slot runs. -/
theorem Refresh.zombie_reachable : ∃ s, Reachable s ∧ s.log.length = 1 ∧ s.zombies = [] ∧
    (s.ws 0).phase = .idle := by
  have r1 : Reachable (({} : World).start 0) := .step .init (.start _ 0 rfl)
  have r2 := r1.step (.refresh _ 0 rfl)
  have r3 := r2.step (.prepare _ 0 rfl)
  have r4 := r3.step (.crash _ 0 (by decide))
  have r5 := r4.step (.start _ 0 rfl)
  have r6 := r5.step (.zombieLands _ ⟨⟨0, 0⟩, .replace, .none, 0⟩ (by exact .head _) rfl)
  exact ⟨_, r6, rfl, rfl, rfl⟩

/-- A writer's write landed and raised before it heard: its `pend` stays, and
the next refresh starts from it (`Sink._pending`, `NoLostAckResumed`'s witness
in the TLA+ model). -/
theorem Refresh.lost_ack_reachable : ∃ s, Reachable s ∧ ∃ i, (s.ws i).pend.isSome ∧
    (s.ws i).phase = .ready := by
  have r1 : Reachable (({} : World).start 0) := .step .init (.start _ 0 rfl)
  have r2 := r1.step (.refresh _ 0 rfl)
  have r3 := r2.step (.prepare _ 0 rfl)
  have r4 := r3.step (.landLostAck _ 0 ⟨⟨0, 0⟩, .replace, .none, 0⟩ rfl rfl)
  have r5 := r4.step (.refresh _ 0 rfl)
  exact ⟨_, r5, 0, rfl, rfl⟩

/-- A writer that lost the race to the node's own commit rewrites the table
on top of it (`NoConflictReplace`'s witness): two processes of one plan read
the empty sink, one commits, the other conflicts, and after a source change
it replaces the first one's state. -/
theorem Refresh.conflict_replace_reachable : ∃ s o, Reachable s ∧ (∃ i, (s.ws i).phase = .writing o) ∧
    o.mode = .replace ∧ s.log.length = o.head ∧
    ∃ r, record s.log = some r ∧ r.plan = o.key.plan := by
  have a1 : Reachable (({} : World).start 0) := .step .init (.start _ 0 rfl)
  have a2 := a1.step (.start _ 1 rfl)
  have a3 := a2.step (.refresh _ 0 rfl)
  have a4 := a3.step (.refresh _ 1 rfl)
  have a5 := a4.step (.prepare _ 0 rfl)
  have a6 := a5.step (.prepare _ 1 rfl)
  have a7 := a6.step (.land _ 0 ⟨⟨0, 0⟩, .replace, .none, 0⟩ rfl rfl)
  have a8 := a7.step (.conflict _ 1 ⟨⟨0, 0⟩, .replace, .none, 0⟩ rfl (by decide))
  have a9 := a8.step (.sourceChanges _)
  have a10 := a9.step (.refresh _ 1 rfl)
  have a11 := a10.step (.prepare _ 1 rfl)
  exact ⟨_, ⟨⟨0, 1⟩, .replace, .none, 1⟩, a11, ⟨1, rfl⟩, rfl, rfl, ⟨0, 0⟩, rfl, rfl⟩

/-! ## What a write reads, and the order of the commits

`ReadIsHead` and `Monotone` of `models/refresh/Refresh.tla`, for every scope.
A write in flight remembers the log's length when it read the sink's record
(`Out.head`). While the log still has that length, it is the log the write
read: commits only add to it. So the write's change was computed from the
newest commit of the node, and its state is above that commit's. -/

namespace Refresh

/-- Two adjacent commits of the node under one plan: the later one is of a
later version of the source. A commit that follows another application's rows
may write the same state again (a repair), so only adjacent commits count. -/
def AdjOK : List Commit → Prop
  | c' :: c :: rest =>
      (c'.app = true → c.app = true → c.key.plan = c'.key.plan → c.key.ver < c'.key.ver) ∧
        AdjOK (c :: rest)
  | _ => True

/-- What a write in flight read, while the log is still the one it read: the
newest commit of the node under its plan is of an earlier version, and a
change was computed from that very commit's state. -/
def Reads (s : World) (o : Out) : Prop :=
  s.log.length = o.head →
    (∀ c rest, s.log = c :: rest → c.app = true → c.key.plan = o.key.plan →
        c.key.ver < o.key.ver) ∧
    (o.mode = .merge → kept s.log = true ∧ ∃ r, record s.log = some r ∧ o.base = r.tbl)

def Inv2 (s : World) : Prop := AdjOK s.log ∧ ∀ o, Pending s o → Reads s o

theorem record_cons {c : Commit} {rest : List Commit} (h : c.app = true) :
    record (c :: rest) = some c.key := by
  simp [record, List.find?, h]

theorem kept_cons {c : Commit} {rest : List Commit} (h : c.app = true) :
    kept (c :: rest) = true := by
  simp [kept, h]

/-- `next` writes under the record's plan only a later version. -/
theorem next_ver {r : Key} {w : Writer} {m : Mode} {wr : Option Key}
    (h : next (some r) true w = .write m wr) (hp : r.plan = w.plan) : r.ver < w.ver := by
  by_cases hv : w.ver ≤ r.ver
  · simp [next, hp, hv] at h
  · omega

theorem inv2_of_keep {s t : World} (hs : Inv2 s) (hlog : t.log = s.log)
    (hp : ∀ o, Pending t o → Pending s o) : Inv2 t := by
  refine ⟨by rw [hlog]; exact hs.1, fun o ho => ?_⟩
  have := hs.2 o (hp o ho)
  unfold Reads at this ⊢
  rw [hlog]
  exact this

/-- A commit of `o` on the log `o` read. -/
theorem inv2_of_commit {s t : World} {o : Out} (hi : Inv s) (hs : Inv2 s) (hpo : Pending s o)
    (hc : s.log.length = o.head) (hlog : t.log = ⟨true, o.key⟩ :: s.log)
    (hp : ∀ o', Pending t o' → Pending s o') : Inv2 t := by
  have hr := hs.2 o hpo hc
  refine ⟨?_, fun o' ho' => ?_⟩
  · rw [hlog]
    have h1 := hs.1
    cases hl : s.log with
    | nil => simp [AdjOK]
    | cons c rest =>
      rw [hl] at h1
      exact ⟨fun _ hca hpl => hr.1 c rest hl hca hpl, h1⟩
  · have hh := (hi.2 o' (hp o' ho')).1
    intro heq
    exfalso
    rw [hlog] at heq
    have heq' : s.log.length + 1 = o'.head := heq
    omega

theorem inv2_step {s t : World} (hi : Inv s) (hs : Inv2 s) (h : Step s t) : Inv2 t := by
  cases h with
  | start i _ =>
    exact inv2_of_keep hs rfl fun o ho => pending_upd (by intro o' h; cases h) ho
  | stop i _ _ =>
    exact inv2_of_keep hs rfl fun o ho => pending_upd (by intro o' h; cases h) ho
  | refresh i _ =>
    exact inv2_of_keep hs rfl fun o ho => pending_upd (by intro o' h; cases h) ho
  | prepare i hr =>
    cases hnext : next (record s.log) (kept s.log) (s.ws i) with
    | skip wr =>
      simp only [World.prepare, hnext]
      exact inv2_of_keep hs rfl fun o ho => pending_upd (by intro o' h; cases h) ho
    | write m wr =>
      simp only [World.prepare, hnext]
      refine ⟨hs.1, fun o ho => ?_⟩
      rcases ho with ⟨j, hj⟩ | hz
      · dsimp only at hj
        by_cases hji : j = i
        · subst hji
          rw [upd_same] at hj
          simp only [Phase.writing.injEq] at hj
          subst hj
          intro _
          refine ⟨fun c rest hl hca hpl => ?_, fun hm => ?_⟩
          · have hrec : record s.log = some c.key := by rw [hl]; exact record_cons hca
            have hk : kept s.log = true := by rw [hl]; exact kept_cons hca
            rw [hrec, hk] at hnext
            exact next_ver hnext hpl
          · simp only at hm
            subst hm
            obtain ⟨r, hrec, hwr, hk⟩ := next_merge hnext
            subst hwr
            exact ⟨hk, r, hrec, rfl⟩
        · rw [upd_other _ _ hji] at hj
          exact hs.2 o (Or.inl ⟨j, hj⟩)
      · exact hs.2 o (Or.inr hz)
  | land i o hw hc =>
    refine inv2_of_commit hi hs (Or.inl ⟨i, hw⟩) hc rfl fun o' ho' => ?_
    exact pending_upd (s := s.commit o) (by intro o' h; cases h) ho'
  | landLostAck i o hw hc =>
    refine inv2_of_commit hi hs (Or.inl ⟨i, hw⟩) hc rfl fun o' ho' => ?_
    have hw' : ∀ o'', ({ s.ws i with phase := .idle } : Writer).phase ≠ .writing o'' := by
      intro o'' h; cases h
    exact pending_upd (s := s.commit o) hw' ho'
  | fail i o _ =>
    exact inv2_of_keep hs rfl fun o' ho' => pending_upd (by intro o'' h; cases h) ho'
  | conflict i o _ _ =>
    exact inv2_of_keep hs rfl fun o' ho' => pending_upd (by intro o'' h; cases h) ho'
  | crash i _ =>
    apply inv2_of_keep (t := s.crash i) hs rfl
    intro o ho
    unfold World.crash at ho
    rcases ho with ⟨j, hj⟩ | hz
    · dsimp only at hj
      by_cases hji : j = i
      · subst hji; simp [upd_same] at hj
      · exact Or.inl ⟨j, by simpa [upd_other _ _ hji] using hj⟩
    · simp only at hz
      split at hz
      · next o' hph =>
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inl ⟨i, hph⟩
        · exact Or.inr hz
      · exact Or.inr hz
  | zombieLands o hz hc =>
    refine inv2_of_commit hi hs (Or.inr hz) hc rfl fun o' ho' => ?_
    rcases ho' with ⟨j, hj⟩ | hz'
    · exact Or.inl ⟨j, hj⟩
    · exact Or.inr (List.mem_of_mem_erase hz')
  | sourceChanges =>
    exact inv2_of_keep hs rfl fun o ho => ho
  | foreignWrite =>
    refine ⟨?_, fun o ho => ?_⟩
    · show AdjOK (⟨false, ⟨0, 0⟩⟩ :: s.log)
      have h1 := hs.1
      cases hl : s.log with
      | nil => simp [AdjOK]
      | cons c rest =>
        rw [hl] at h1
        exact ⟨fun h => absurd h (by simp), h1⟩
    · have h' := (hi.2 o ho).1
      intro heq
      exfalso
      have heq' : s.log.length + 1 = o.head := heq
      omega
  | deploy =>
    exact inv2_of_keep hs rfl fun o ho => ho

theorem inv2_reachable {s : World} (h : Reachable s) : Inv2 s := by
  induction h with
  | init => exact ⟨trivial, fun o ho => by rcases ho with ⟨_, h⟩ | h <;> cases h⟩
  | step hr hst ih => exact inv2_step (inv_reachable hr) ih hst

end Refresh

/-- A change that lands applies to the newest commit of the node: while the
log is still the one the write read, that commit is the sink's record, still
the newest, and the change was computed against its table (#933, invariant 3:
`ReadIsHead`). -/
theorem Refresh.read_is_head {s : World} {o : Out} (h : Reachable s) (hp : Pending s o)
    (hm : o.mode = .merge) (hc : s.log.length = o.head) :
    kept s.log = true ∧ ∃ r, record s.log = some r ∧ o.base = r.tbl :=
  ((inv2_reachable h).2 o hp hc).2 hm

/-- Under one plan, adjacent commits of the node are of strictly increasing
source versions: no state is committed twice in a row, and none goes back
(#933, invariants 1 and 5: `Monotone`, and #889's `NoRewriteUnchanged`, which
is the same fact: a state is a function of the plan and the version). -/
theorem Refresh.monotone {s : World} (h : Reachable s) : AdjOK s.log :=
  (inv2_reachable h).1

/-! ## #889: what a new process does with the sink's record -/

/-- A process whose view is the record's version commits nothing. -/
theorem Refresh.next_unchanged {r : Key} {w : Writer} (hp : r.plan = w.plan)
    (hv : w.ver = r.ver) : next (some r) true w = .skip (some r) := by
  simp [next, hp, hv]

/-- A process that holds the record as its own writes at most a change on it,
never the whole table again (#889's `NoNeedlessRewrite`). -/
theorem Refresh.next_resumes {r : Key} {w : Writer} (hp : r.plan = w.plan)
    (hv : r.ver ≤ w.ver) (hw : w.written = some r) (wr : Option Key) :
    next (some r) true w ≠ .write .replace wr := by
  intro h
  have hw0 : (if w.pend.isSome && w.pend == some r then w.pend else w.written) = some r := by
    split
    · next hc =>
      simp [Option.isSome_iff_exists] at hc
      exact hc.2
    · exact hw
  have hlt : ¬ w.ver ≤ r.ver ∨ w.ver = r.ver := by omega
  simp only [next, hw0] at h
  rcases hlt with hlt | heq
  · simp [hp, hlt] at h
  · simp [hp, heq] at h

/-- A process's first refresh resumes from the record when it is the node's
newest commit, under the process's plan, and not ahead of the source: what it
commits next is a change on it or nothing. -/
theorem Refresh.no_needless_rewrite (s : World) (i : Nat) (hf : (s.ws i).first = true)
    {r : Key} (hk : kept s.log = true) (hr : record s.log = some r)
    (hp : r.plan = (s.ws i).plan) (hv : r.ver ≤ s.src) (wr : Option Key) :
    next (record (s.refresh i).log) (kept (s.refresh i).log) ((s.refresh i).ws i) ≠
      .write .replace wr := by
  simp only [World.refresh, upd_same, hf, hr, hk, hp, hv, decide_true, Bool.and_self,
    ite_true, beq_self_eq_true]
  exact next_resumes
    (w := { s.ws i with phase := .ready, first := false, ver := s.src, written := some r,
                        resumable := some r })
    hp hv rfl wr

/-! ### #889 at any later prepare

`Refresh.no_needless_rewrite` says what a first refresh leads to. The TLA+
property is stronger: whenever a process prepares, if the record is still the
one its first refresh could resume from, it does not rewrite in full. Between
its first refresh and its prepare only the process's own steps change its
`written` and `ver`, and each leaves the phase `ready`. -/

namespace Refresh

/-- A process that is ready and could resume from `r` holds `r` as its own,
under its plan, not ahead of its view. -/
def ResOK (s : World) : Prop :=
  ∀ i r, (s.ws i).phase = .ready → (s.ws i).resumable = some r →
    (s.ws i).written = some r ∧ r.plan = (s.ws i).plan ∧ r.ver ≤ (s.ws i).ver

theorem resok_step {s t : World} (hs : ResOK s) (h : Step s t) : ResOK t := by
  -- A step that changes only other slots, or leaves slot `i` not ready.
  have other : ∀ (i : Nat) (w : Writer), (∀ r, w.phase = .ready → w.resumable = some r →
      w.written = some r ∧ r.plan = w.plan ∧ r.ver ≤ w.ver) →
      ∀ ws : Nat → Writer, ws = upd s.ws i w → ∀ j r, (ws j).phase = .ready →
        (ws j).resumable = some r →
        (ws j).written = some r ∧ r.plan = (ws j).plan ∧ r.ver ≤ (ws j).ver := by
    intro i w hw ws hws j r hph hr
    subst hws
    by_cases hji : j = i
    · subst hji; rw [upd_same] at hph hr ⊢; exact hw r hph hr
    · rw [upd_other _ _ hji] at hph hr ⊢; exact hs j r hph hr
  cases h with
  | start i _ => exact other i _ (fun r hp => by simp at hp) _ rfl
  | stop i _ _ => exact other i _ (fun r hp => by simp at hp) _ rfl
  | refresh i hi =>
    refine other i _ ?_ _ rfl
    intro r _ hr
    simp only at hr ⊢
    split at hr
    · next hf =>
      simp only [hf] at hr ⊢
      cases hrec : record s.log with
      | none => simp [hrec] at hr
      | some r' =>
        simp only [hrec] at hr ⊢
        split at hr
        · next hc =>
          simp only [Option.some.injEq] at hr
          subst hr
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
          simp_all
        · simp at hr
    · simp at hr
  | prepare i _ =>
    cases hnext : next (record s.log) (kept s.log) (s.ws i) with
    | skip wr =>
      simp only [World.prepare, hnext]
      exact other i _ (fun r hp => by simp at hp) _ rfl
    | write m wr =>
      simp only [World.prepare, hnext]
      exact other i _ (fun r hp => by simp at hp) _ rfl
  | land i o _ _ => exact other i _ (fun r hp => by simp at hp) _ rfl
  | landLostAck i o _ _ => exact other i _ (fun r hp => by simp at hp) _ rfl
  | fail i o _ => exact other i _ (fun r hp => by simp at hp) _ rfl
  | conflict i o _ _ => exact other i _ (fun r hp => by simp at hp) _ rfl
  | crash i _ => exact other i {} (fun r hp => by simp at hp) _ rfl
  | zombieLands o _ _ => exact hs
  | sourceChanges => exact hs
  | foreignWrite => exact hs
  | deploy => exact hs

theorem resok_reachable {s : World} (h : Reachable s) : ResOK s := by
  induction h with
  | init => intro i r hp; simp at hp
  | step _ hst ih => exact resok_step ih hst

end Refresh

/-- Whenever a process prepares, if the record is still the one its first
refresh could resume from and no other application wrote since, it does not
write the whole table again (#889: `NoNeedlessRewrite`). -/
theorem Refresh.no_needless_rewrite_reachable {s : World} (h : Reachable s) {i : Nat} {r : Key}
    (hph : (s.ws i).phase = .ready) (hres : (s.ws i).resumable = some r)
    (hrec : record s.log = some r) (hk : kept s.log = true) (wr : Option Key) :
    next (record s.log) (kept s.log) (s.ws i) ≠ .write .replace wr := by
  obtain ⟨hw, hp, hv⟩ := resok_reachable h i r hph hres
  rw [hrec, hk]
  exact next_resumes hp hv hw wr


/-! ## Observably a failure-free run

The failure-free system has one writer and no crash, zombie, lost
acknowledgement, failed write or race of writers. Other applications still
write to the sink, the source still changes and plans are still deployed. -/

/-- One step of the failure-free system. -/
inductive Step₀ : World → World → Prop where
  | start (s : World) : (s.ws 0).phase = .down → Step₀ s (s.start 0)
  | refresh (s : World) : (s.ws 0).phase = .idle → Step₀ s (s.refresh 0)
  | prepare (s : World) : (s.ws 0).phase = .ready → Step₀ s (s.prepare 0)
  | land (s : World) (o : Out) : (s.ws 0).phase = .writing o → s.log.length = o.head →
      Step₀ s { s.commit o with
        ws := upd s.ws 0 { s.ws 0 with phase := .idle, written := some o.key, pend := none } }
  | sourceChanges (s : World) : Step₀ s { s with src := s.src + 1 }
  | foreignWrite (s : World) : Step₀ s { s with log := ⟨false, ⟨0, 0⟩⟩ :: s.log, tbl := .foreign }
  | deploy (s : World) : Step₀ s { s with deployed := s.deployed + 1 }

inductive Reachable₀ : World → Prop where
  | init : Reachable₀ {}
  | step {s t} : Reachable₀ s → Step₀ s t → Reachable₀ t

theorem Step₀.step {s t : World} (h : Step₀ s t) : Step s t := by
  cases h with
  | start => exact .start _ 0 ‹_›
  | refresh => exact .refresh _ 0 ‹_›
  | prepare => exact .prepare _ 0 ‹_›
  | land o hw hc => exact .land _ 0 o hw hc
  | sourceChanges => exact .sourceChanges _
  | foreignWrite => exact .foreignWrite _
  | deploy => exact .deploy _

theorem record_foreign (k : Key) (log : List Commit) :
    record (⟨false, k⟩ :: log) = record log := by
  simp [record, List.find?]

/-- What an observer of the sink sees: its table and the node's record. -/
def obs (s : World) : Tbl × Option Key := (s.tbl, record s.log)

/-- A failure-free run commits the state `p`, `v`: the source at version `v`,
the plan `p` deployed. -/
theorem reach₀_committed (k : Key) :
    ∃ s, Reachable₀ s ∧ s.tbl = k.tbl ∧ record s.log = some k := by
  have e0 : ∀ m, Reachable₀ ({ src := m } : World) := by
    intro m
    induction m with
    | zero => exact .init
    | succ m ih => exact ih.step (.sourceChanges _)
  have e1 : ∀ n, Reachable₀ ({ src := k.ver, deployed := n } : World) := by
    intro n
    induction n with
    | zero => exact e0 k.ver
    | succ n ih => exact ih.step (.deploy _)
  have r1 := (e1 k.plan).step (.start _ rfl)
  have r2 := r1.step (.refresh _ rfl)
  have r3 := r2.step (.prepare _ rfl)
  have r4 := r3.step (.land _ ⟨k, .replace, .none, 0⟩ rfl rfl)
  exact ⟨_, r4, rfl, rfl⟩

/-- Every state of the sink an observer can see, in a run with crashes, zombies,
lost acknowledgements and racing writers, is one a failure-free run reaches.
It holds of the observation, the table and the node's record, and not of the
run's steps: a failure-free run reaches the state by another order of source
changes and deploys (#933: refinement). -/
theorem Refresh.observable {s : World} (h : Reachable s) :
    ∃ s₀, Reachable₀ s₀ ∧ obs s₀ = obs s := by
  have ht := (inv_reachable h).1
  unfold TblOK at ht
  cases hl : s.log with
  | nil =>
    rw [hl] at ht
    exact ⟨{}, .init, by simp [obs, hl, ht, record]⟩
  | cons c rest =>
    rw [hl] at ht
    by_cases hc : c.app = true
    · simp only [hc, ↓reduceIte] at ht
      obtain ⟨s₀, h₀, e₁, e₂⟩ := reach₀_committed c.key
      exact ⟨s₀, h₀, by simp [obs, hl, ht, e₁, e₂, record_cons hc]⟩
    · have hc' : c.app = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at ht
      cases hr : record s.log with
      | none =>
        refine ⟨_, Reachable₀.step .init (.foreignWrite _), ?_⟩
        show (Tbl.foreign, record (⟨false, ⟨0, 0⟩⟩ :: ([] : List Commit))) = (s.tbl, record s.log)
        rw [record_foreign, ht, hr]
        rfl
      | some k =>
        obtain ⟨s₀, h₀, e₁, e₂⟩ := reach₀_committed k
        refine ⟨_, h₀.step (.foreignWrite s₀), ?_⟩
        show (Tbl.foreign, record (⟨false, ⟨0, 0⟩⟩ :: s₀.log)) = (s.tbl, record s.log)
        rw [record_foreign, ht, hr, e₂]

/-! ## The quiet regime

Liveness (`Converges` in the TLA+ model) needs a fairness hypothesis on
infinite runs. What is proved here is its safety half, with no fairness: once
the environment is quiet, no source change, deploy, foreign commit, crash,
lost acknowledgement or late write of a crashed process, the processes' own
steps reach the deployed plan's state of the source, and keep it. -/

namespace Refresh

/-- A step of a process, as against a step of the environment. -/
inductive PStep : World → World → Prop where
  | start (s : World) (i : Nat) : (s.ws i).phase = .down → PStep s (s.start i)
  | stop (s : World) (i : Nat) : (s.ws i).phase = .idle → (s.ws i).plan ≠ s.deployed →
      PStep s (s.stop i)
  | refresh (s : World) (i : Nat) : (s.ws i).phase = .idle → PStep s (s.refresh i)
  | prepare (s : World) (i : Nat) : (s.ws i).phase = .ready → PStep s (s.prepare i)
  | land (s : World) (i : Nat) (o : Out) : (s.ws i).phase = .writing o →
      s.log.length = o.head →
      PStep s { s.commit o with
        ws := upd s.ws i { s.ws i with phase := .idle, written := some o.key, pend := none } }
  | conflict (s : World) (i : Nat) (o : Out) : (s.ws i).phase = .writing o →
      s.log.length ≠ o.head →
      PStep s { s with ws := upd s.ws i { s.ws i with phase := .idle, written := none,
                                                      pend := none } }

theorem PStep.step {s t : World} (h : PStep s t) : Step s t := by
  cases h with
  | start i h => exact .start _ i h
  | stop i h1 h2 => exact .stop _ i h1 h2
  | refresh i h => exact .refresh _ i h
  | prepare i h => exact .prepare _ i h
  | land i o h1 h2 => exact .land _ i o h1 h2
  | conflict i o h1 h2 => exact .conflict _ i o h1 h2

/-- A process step changes neither the source, the plan deployed nor the
writes in flight of crashed processes. -/
theorem PStep.env {s t : World} (h : PStep s t) :
    t.src = s.src ∧ t.deployed = s.deployed ∧ t.zombies = s.zombies := by
  cases h <;> first | exact ⟨rfl, rfl, rfl⟩ | (simp only [World.prepare]; split <;> exact ⟨rfl, rfl, rfl⟩)

/-- Finitely many process steps. -/
inductive PReach : World → World → Prop where
  | refl (s : World) : PReach s s
  | step {s t u : World} : PStep s t → PReach t u → PReach s u

theorem PReach.trans {s t u : World} (h : PReach s t) (h' : PReach t u) : PReach s u := by
  induction h with
  | refl => exact h'
  | step hst _ ih => exact .step hst (ih h')

theorem PReach.reachable {s t : World} (h : PReach s t) (hs : Reachable s) : Reachable t := by
  induction h with
  | refl => exact hs
  | step hst _ ih => exact ih (hs.step hst.step)

theorem PReach.env {s t : World} (h : PReach s t) :
    t.src = s.src ∧ t.deployed = s.deployed ∧ t.zombies = s.zombies := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | step hst _ ih =>
    obtain ⟨a, b, c⟩ := hst.env
    obtain ⟨a', b', c'⟩ := ih
    exact ⟨a'.trans a, b'.trans b, c'.trans c⟩

/-- A process's view is not ahead of the source, and only finitely many slots
have a process. -/
def Inv3 (s : World) : Prop :=
  (∀ i, (s.ws i).ver ≤ s.src) ∧ ∃ N, ∀ i, N ≤ i → (s.ws i).phase = .down

theorem inv3_of_upd {s t : World} {i : Nat} {w : Writer} (hs : Inv3 s)
    (hws : t.ws = upd s.ws i w) (hsrc : s.src ≤ t.src) (hw : w.ver ≤ t.src) : Inv3 t := by
  obtain ⟨hv, N, hN⟩ := hs
  refine ⟨fun j => ?_, max N (i + 1), fun j hj => ?_⟩
  · rw [hws]
    by_cases hji : j = i
    · subst hji; rw [upd_same]; exact hw
    · rw [upd_other _ _ hji]; exact Nat.le_trans (hv j) hsrc
  · rw [hws, upd_other _ _ (by omega)]
    exact hN j (by omega)

theorem inv3_of_same {s t : World} (hs : Inv3 s) (hws : t.ws = s.ws) (hsrc : s.src ≤ t.src) :
    Inv3 t := by
  obtain ⟨hv, N, hN⟩ := hs
  refine ⟨fun j => ?_, N, fun j hj => ?_⟩
  · rw [hws]; exact Nat.le_trans (hv j) hsrc
  · rw [hws]; exact hN j hj

theorem inv3_step {s t : World} (hs : Inv3 s) (h : Step s t) : Inv3 t := by
  have hv := hs.1
  cases h with
  | start i _ => exact inv3_of_upd hs rfl (Nat.le_refl _) (Nat.zero_le _)
  | stop i _ _ => exact inv3_of_upd hs rfl (Nat.le_refl _) (Nat.zero_le _)
  | refresh i _ => exact inv3_of_upd hs rfl (Nat.le_refl _) (Nat.le_refl _)
  | prepare i _ =>
    cases hnext : next (record s.log) (kept s.log) (s.ws i) with
    | skip wr =>
      simp only [World.prepare, hnext]
      exact inv3_of_upd hs rfl (Nat.le_refl _) (hv i)
    | write m wr =>
      simp only [World.prepare, hnext]
      exact inv3_of_upd hs rfl (Nat.le_refl _) (hv i)
  | land i o _ _ => exact inv3_of_upd hs rfl (Nat.le_refl _) (hv i)
  | landLostAck i o _ _ => exact inv3_of_upd hs rfl (Nat.le_refl _) (hv i)
  | fail i o _ => exact inv3_of_upd hs rfl (Nat.le_refl _) (hv i)
  | conflict i o _ _ => exact inv3_of_upd hs rfl (Nat.le_refl _) (hv i)
  | crash i _ => exact inv3_of_upd (t := s.crash i) hs rfl (Nat.le_refl _) (Nat.zero_le _)
  | zombieLands o _ _ => exact inv3_of_same hs rfl (Nat.le_refl _)
  | sourceChanges => exact inv3_of_same hs rfl (Nat.le_succ _)
  | foreignWrite => exact inv3_of_same hs rfl (Nat.le_refl _)
  | deploy => exact inv3_of_same hs rfl (Nat.le_refl _)

theorem inv3_reachable {s : World} (h : Reachable s) : Inv3 s := by
  induction h with
  | init => exact ⟨fun _ => Nat.le_refl _, 0, fun _ _ => rfl⟩
  | step _ hst ih => exact inv3_step ih hst

/-- How far a process is from rest: a process of the deployed plan is at rest
between refreshes; one of an old plan is stopped there. -/
def rank (s : World) (i : Nat) : Nat :=
  match (s.ws i).phase with
  | .down => 0
  | .idle => if (s.ws i).plan = s.deployed then 0 else 1
  | .writing _ => 2
  | .ready => 3

def mu (s : World) : Nat → Nat
  | 0 => 0
  | n + 1 => mu s n + rank s n

/-- Every process is down, or idle and of the deployed plan. -/
def Quiescent (s : World) : Prop :=
  ∀ i, (s.ws i).phase = .down ∨ ((s.ws i).phase = .idle ∧ (s.ws i).plan = s.deployed)

theorem mu_congr {s t : World} {N : Nat} (h : ∀ j, j < N → rank t j = rank s j) :
    mu t N = mu s N := by
  induction N with
  | zero => rfl
  | succ n ih => simp only [mu]; rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem mu_lt {s t : World} {N i : Nat} (hi : i < N)
    (hother : ∀ j, j ≠ i → rank t j = rank s j) (hlt : rank t i < rank s i) :
    mu t N < mu s N := by
  induction N with
  | zero => omega
  | succ n ih =>
    simp only [mu]
    by_cases hin : i = n
    · subst hin
      rw [mu_congr (fun j hj => hother j (by omega))]
      omega
    · have := ih (by omega)
      rw [hother n (Ne.symm hin)]
      omega

theorem rank_upd {s t : World} {i j : Nat} {w : Writer} (hws : t.ws = upd s.ws i w)
    (hdep : t.deployed = s.deployed) (hj : j ≠ i) : rank t j = rank s j := by
  unfold rank
  rw [hws, upd_other _ _ hj, hdep]

/-- The processes' own steps bring every process to rest. -/
theorem drain (N : Nat) (n : Nat) : ∀ s : World, mu s N = n → Reachable s → s.zombies = [] →
    (∀ i, N ≤ i → (s.ws i).phase = .down) →
    ∃ t, PReach s t ∧ Reachable t ∧ t.zombies = [] ∧ (∀ i, N ≤ i → (t.ws i).phase = .down) ∧
      Quiescent t := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro s hmu hr hz hN
  by_cases hall : ∀ i, i < N → rank s i = 0
  · refine ⟨s, .refl s, hr, hz, hN, fun i => ?_⟩
    by_cases hi : i < N
    · have h0 := hall i hi
      unfold rank at h0
      cases hph : (s.ws i).phase with
      | down => exact Or.inl rfl
      | idle =>
        rw [hph] at h0
        simp only at h0
        split at h0
        · next hp => exact Or.inr ⟨rfl, hp⟩
        · cases h0
      | writing o => rw [hph] at h0; cases h0
      | ready => rw [hph] at h0; cases h0
    · exact Or.inl (hN i (by omega))
  · obtain ⟨i, hi⟩ := Classical.not_forall.mp hall
    have hiN : i < N := by
      by_cases h : i < N
      · exact h
      · exact absurd (fun h' => absurd h' h) hi
    have hpos : rank s i ≠ 0 := fun h0 => hi (fun _ => h0)
    have key : ∀ t, PStep s t → (∃ w, t.ws = upd s.ws i w) → rank t i < rank s i →
        ∃ t', PReach s t' ∧ Reachable t' ∧ t'.zombies = [] ∧
          (∀ i, N ≤ i → (t'.ws i).phase = .down) ∧ Quiescent t' := by
      intro t hst ⟨w, hws⟩ hlt
      obtain ⟨_, hdep, hzomb⟩ := hst.env
      have hmu' : mu t N < n := by
        rw [← hmu]; exact mu_lt hiN (fun j hj => rank_upd hws hdep hj) hlt
      obtain ⟨t', h1, h2, h3, h4, h5⟩ := ih (mu t N) hmu' t rfl (hr.step hst.step)
        (hzomb ▸ hz) (fun j hj => by rw [hws, upd_other _ _ (by omega)]; exact hN j hj)
      exact ⟨t', .step hst h1, h2, h3, h4, h5⟩
    cases hph : (s.ws i).phase with
    | down => unfold rank at hpos; rw [hph] at hpos; exact absurd rfl hpos
    | idle =>
      have hp : (s.ws i).plan ≠ s.deployed := by
        intro hp; apply hpos; unfold rank; rw [hph]; simp [hp]
      refine key (s.stop i) (.stop s i hph hp) ⟨{}, rfl⟩ ?_
      show rank { s with ws := upd s.ws i {} } i < rank s i
      unfold rank
      simp only [upd_same, hph]
      simp [hp]
    | ready =>
      cases hnext : next (record s.log) (kept s.log) (s.ws i) with
      | skip wr =>
        refine key (s.prepare i) (.prepare s i hph) (by simp only [World.prepare, hnext]; exact ⟨_, rfl⟩) ?_
        simp only [World.prepare, hnext]
        unfold rank
        simp only [upd_same, hph]
        split <;> omega
      | write m wr =>
        refine key (s.prepare i) (.prepare s i hph) (by simp only [World.prepare, hnext]; exact ⟨_, rfl⟩) ?_
        simp only [World.prepare, hnext]
        unfold rank
        simp only [upd_same, hph]
        omega
    | writing o =>
      by_cases hc : s.log.length = o.head
      · refine key _ (.land s i o hph hc) ⟨_, rfl⟩ ?_
        unfold rank
        simp only [upd_same, hph]
        split <;> omega
      · refine key _ (.conflict s i o hph hc) ⟨_, rfl⟩ ?_
        unfold rank
        simp only [upd_same, hph]
        split <;> omega

/-- No commit of the node, and no write in flight, is of a version the source
has not reached. -/
def KeyLe (s : World) : Prop :=
  (∀ c ∈ s.log, c.app = true → c.key.ver ≤ s.src) ∧ (∀ o, Pending s o → o.key.ver ≤ s.src)

theorem keyle_of_sub {s t : World} (hs : KeyLe s) (hlog : t.log = s.log) (hsrc : s.src ≤ t.src)
    (hp : ∀ o, Pending t o → Pending s o) : KeyLe t :=
  ⟨fun c hc hca => Nat.le_trans (hs.1 c (hlog ▸ hc) hca) hsrc,
   fun o ho => Nat.le_trans (hs.2 o (hp o ho)) hsrc⟩

theorem keyle_commit {s t : World} {o : Out} (hs : KeyLe s) (hpo : Pending s o)
    (hlog : t.log = ⟨true, o.key⟩ :: s.log) (hsrc : t.src = s.src)
    (hp : ∀ o', Pending t o' → Pending s o') : KeyLe t := by
  refine ⟨fun c hc hca => ?_, fun o' ho' => ?_⟩
  · rw [hlog] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [hsrc]; exact hs.2 o hpo
    · rw [hsrc]; exact hs.1 c hc hca
  · rw [hsrc]; exact hs.2 o' (hp o' ho')

theorem keyle_step {s t : World} (h3 : Inv3 s) (hs : KeyLe s) (h : Step s t) : KeyLe t := by
  cases h with
  | start i _ =>
    exact keyle_of_sub hs rfl (Nat.le_refl _) fun o ho => pending_upd (by intro o' h; cases h) ho
  | stop i _ _ =>
    exact keyle_of_sub hs rfl (Nat.le_refl _) fun o ho => pending_upd (by intro o' h; cases h) ho
  | refresh i _ =>
    exact keyle_of_sub hs rfl (Nat.le_refl _) fun o ho => pending_upd (by intro o' h; cases h) ho
  | prepare i _ =>
    cases hnext : next (record s.log) (kept s.log) (s.ws i) with
    | skip wr =>
      simp only [World.prepare, hnext]
      exact keyle_of_sub hs rfl (Nat.le_refl _) fun o ho =>
        pending_upd (by intro o' h; cases h) ho
    | write m wr =>
      simp only [World.prepare, hnext]
      refine ⟨hs.1, fun o ho => ?_⟩
      rcases ho with ⟨j, hj⟩ | hz
      · dsimp only at hj
        by_cases hji : j = i
        · subst hji
          rw [upd_same] at hj
          simp only [Phase.writing.injEq] at hj
          subst hj
          exact h3.1 j
        · rw [upd_other _ _ hji] at hj
          exact hs.2 o (Or.inl ⟨j, hj⟩)
      · exact hs.2 o (Or.inr hz)
  | land i o hw hc =>
    refine keyle_commit hs (Or.inl ⟨i, hw⟩) rfl rfl fun o' ho' => ?_
    exact pending_upd (s := s.commit o) (by intro o' h; cases h) ho'
  | landLostAck i o hw hc =>
    refine keyle_commit hs (Or.inl ⟨i, hw⟩) rfl rfl fun o' ho' => ?_
    have hw' : ∀ o'', ({ s.ws i with phase := .idle } : Writer).phase ≠ .writing o'' := by
      intro o'' h; cases h
    exact pending_upd (s := s.commit o) hw' ho'
  | fail i o _ =>
    exact keyle_of_sub hs rfl (Nat.le_refl _) fun o' ho' =>
      pending_upd (by intro o'' h; cases h) ho'
  | conflict i o _ _ =>
    exact keyle_of_sub hs rfl (Nat.le_refl _) fun o' ho' =>
      pending_upd (by intro o'' h; cases h) ho'
  | crash i _ =>
    refine keyle_of_sub (t := s.crash i) hs rfl (Nat.le_refl _) ?_
    intro o ho
    unfold World.crash at ho
    rcases ho with ⟨j, hj⟩ | hz
    · dsimp only at hj
      by_cases hji : j = i
      · subst hji; simp [upd_same] at hj
      · exact Or.inl ⟨j, by simpa [upd_other _ _ hji] using hj⟩
    · simp only at hz
      split at hz
      · next o' hph =>
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inl ⟨i, hph⟩
        · exact Or.inr hz
      · exact Or.inr hz
  | zombieLands o hz hc =>
    refine keyle_commit hs (Or.inr hz) rfl rfl fun o' ho' => ?_
    rcases ho' with ⟨j, hj⟩ | hz'
    · exact Or.inl ⟨j, hj⟩
    · exact Or.inr (List.mem_of_mem_erase hz')
  | sourceChanges =>
    exact keyle_of_sub hs rfl (Nat.le_succ _) fun o ho => ho
  | foreignWrite =>
    refine ⟨fun c hc hca => ?_, fun o ho => hs.2 o ho⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · exact absurd hca (by simp)
    · exact hs.1 c hc hca
  | deploy => exact keyle_of_sub hs rfl (Nat.le_refl _) fun o ho => ho

theorem keyle_reachable {s : World} (h : Reachable s) : KeyLe s := by
  induction h with
  | init => exact ⟨fun c hc => by simp at hc, fun o ho => by rcases ho with ⟨_, h⟩ | h <;> cases h⟩
  | step hr hst ih => exact keyle_step (inv3_reachable hr) ih hst

/-- The sink's record is the newest commit, of the deployed plan and of the
source's version, and every process rests or is about to prepare, under the
deployed plan. -/
def Conv (s : World) : Prop :=
  kept s.log = true ∧ (∃ r, record s.log = some r ∧ r.plan = s.deployed ∧ r.ver = s.src) ∧
    ∀ i, (s.ws i).phase = .down ∨
      (((s.ws i).phase = .idle ∨ (s.ws i).phase = .ready) ∧ (s.ws i).plan = s.deployed)

theorem record_mem {log : List Commit} {r : Key} (h : record log = some r) :
    ∃ c ∈ log, c.app = true ∧ c.key = r := by
  unfold record at h
  cases hf : log.find? (·.app) with
  | none => simp [hf] at h
  | some c =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    exact ⟨c, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩

theorem ite_ne_skip {c : Prop} [Decidable c] {a b : Decision} {wr : Option Key}
    (ha : a ≠ .skip wr) (hb : b ≠ .skip wr) : (if c then a else b) ≠ .skip wr := by
  by_cases hc : c <;> simp [hc, ha, hb]

/-- A skip is on a record of the writer's plan, not below its version. -/
theorem next_skip_facts {rec : Option Key} {k : Bool} {w : Writer} {wr : Option Key}
    (h : next rec k w = .skip wr) :
    ∃ r, rec = some r ∧ k = true ∧ r.plan = w.plan ∧ w.ver ≤ r.ver := by
  cases rec with
  | none => simp [next] at h
  | some r =>
    by_cases hp : r.plan = w.plan
    · by_cases hk : k = true
      · by_cases hv : w.ver ≤ r.ver
        · exact ⟨r, rfl, hk, hp, hv⟩
        · exfalso
          simp [next, hp, hk, hv] at h
          exact ite_ne_skip (by simp) (by simp) h
      · exfalso
        have hk' : k = false := by simpa using hk
        simp [next, hp, hk'] at h
    · exfalso
      simp [next, hp] at h

theorem next_skip_of {r : Key} {w : Writer} (hp : r.plan = w.plan) (hv : w.ver ≤ r.ver) :
    ∃ wr, next (some r) true w = .skip wr := by
  refine ⟨if r.ver = w.ver then some r else none, ?_⟩
  simp [next, hp, hv]

theorem conv_of_upd {s t : World} {i : Nat} {w : Writer} (hc : Conv s)
    (hlog : t.log = s.log) (hsrc : t.src = s.src) (hdep : t.deployed = s.deployed)
    (hws : t.ws = upd s.ws i w)
    (hw : w.phase = .down ∨ ((w.phase = .idle ∨ w.phase = .ready) ∧ w.plan = s.deployed)) :
    Conv t := by
  obtain ⟨hk, ⟨r, hrec, hrp, hrv⟩, hall⟩ := hc
  refine ⟨by rw [hlog]; exact hk, ⟨r, by rw [hlog]; exact hrec, by rw [hdep]; exact hrp,
    by rw [hsrc]; exact hrv⟩, fun j => ?_⟩
  rw [hws, hdep]
  by_cases hji : j = i
  · subst hji; rw [upd_same]; exact hw
  · rw [upd_other _ _ hji]; exact hall j

theorem conv_step {s t : World} (h3 : Inv3 s) (hc : Conv s) (h : PStep s t) : Conv t := by
  obtain ⟨hk, ⟨r, hrec, hrp, hrv⟩, hall⟩ := hc
  have hc : Conv s := ⟨hk, ⟨r, hrec, hrp, hrv⟩, hall⟩
  cases h with
  | start i _ => exact conv_of_upd hc rfl rfl rfl rfl (Or.inr ⟨Or.inl rfl, rfl⟩)
  | stop i _ _ => exact conv_of_upd hc rfl rfl rfl rfl (Or.inl rfl)
  | refresh i hi =>
    rcases hall i with h | ⟨_, hp⟩
    · rw [h] at hi; cases hi
    · exact conv_of_upd hc rfl rfl rfl rfl (Or.inr ⟨Or.inr rfl, hp⟩)
  | prepare i hi =>
    rcases hall i with h | ⟨_, hp⟩
    · rw [h] at hi; cases hi
    · obtain ⟨wr, hnext⟩ := next_skip_of (r := r) (w := s.ws i) (by rw [hrp, hp])
        (by rw [hrv]; exact h3.1 i)
      have hn : next (record s.log) (kept s.log) (s.ws i) = .skip wr := by
        rw [hrec, hk]; exact hnext
      simp only [World.prepare, hn]
      exact conv_of_upd hc rfl rfl rfl rfl (Or.inr ⟨Or.inl rfl, hp⟩)
  | land i o hw _ =>
    rcases hall i with h | ⟨h, _⟩
    · rw [h] at hw; cases hw
    · rcases h with h | h <;> rw [h] at hw <;> cases hw
  | conflict i o hw _ =>
    rcases hall i with h | ⟨h, _⟩
    · rw [h] at hw; cases hw
    · rcases h with h | h <;> rw [h] at hw <;> cases hw

theorem conv_reach {s t : World} (hr : Reachable s) (hc : Conv s) (h : PReach s t) : Conv t := by
  induction h with
  | refl => exact hc
  | step hst _ ih => exact ih (hr.step hst.step) (conv_step (inv3_reachable hr) hc hst)

/-- One process, started after the others have come to rest, brings the sink to
the deployed plan's state of the source. -/
theorem fresh {s : World} (N : Nat) (hr : Reachable s) (hq : Quiescent s)
    (hN : ∀ i, N ≤ i → (s.ws i).phase = .down) : ∃ t, PReach s t ∧ Conv t := by
  have hv := (inv3_reachable hr).1
  have hk := keyle_reachable hr
  have h1 : PStep s (s.start N) := .start s N (hN N (Nat.le_refl _))
  have hw1 : (s.start N).ws N = { phase := .idle, plan := s.deployed } := by
    simp [World.start, upd_same]
  have h2 : PStep (s.start N) ((s.start N).refresh N) := .refresh _ N (by rw [hw1])
  have hw2 : (((s.start N).refresh N).ws N).phase = .ready ∧
      (((s.start N).refresh N).ws N).plan = s.deployed ∧
      (((s.start N).refresh N).ws N).ver = s.src :=
    ⟨by simp [World.refresh, upd_same, hw1], by simp [World.refresh, upd_same, hw1],
     by simp [World.refresh, upd_same, hw1] <;> rfl⟩
  have h3 : PStep ((s.start N).refresh N) (((s.start N).refresh N).prepare N) :=
    .prepare _ N hw2.1
  have hoth : ∀ j, j ≠ N → ∀ (f : Writer → Writer),
      (upd (upd (upd s.ws N { phase := .idle, plan := s.deployed }) N
        (((s.start N).refresh N).ws N)) N (f (((s.start N).refresh N).ws N))) j = s.ws j := by
    intro j hj f
    rw [upd_other _ _ hj, upd_other _ _ hj, upd_other _ _ hj]
  cases hn : next (record ((s.start N).refresh N).log) (kept ((s.start N).refresh N).log)
      (((s.start N).refresh N).ws N) with
  | skip wr =>
    obtain ⟨r, hrec, hkt, hrp, hrv⟩ := next_skip_facts hn
    have hrec : record s.log = some r := hrec
    have hkt : kept s.log = true := hkt
    obtain ⟨c, hc, hca, hck⟩ := record_mem hrec
    have hle : r.ver ≤ s.src := hck ▸ hk.1 c hc hca
    refine ⟨_, .step h1 (.step h2 (.step h3 (.refl _))), ?_⟩
    simp only [World.prepare, hn]
    refine ⟨hkt, ⟨r, hrec, hrp.trans hw2.2.1, ?_⟩, fun j => ?_⟩
    · exact Nat.le_antisymm hle (hw2.2.2 ▸ hrv)
    · by_cases hj : j = N
      · subst hj
        right
        simp [upd_same, hw2.2.1] <;> rfl
      · simp only [World.start, World.refresh] at *
        rw [upd_other _ _ hj, upd_other _ _ hj, upd_other _ _ hj]
        rcases hq j with h | ⟨h, hp⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inl h, hp⟩
  | write m wr =>
    let o : Out := ⟨⟨(((s.start N).refresh N).ws N).plan, (((s.start N).refresh N).ws N).ver⟩,
      m, (wr.map Key.tbl).getD .none, ((s.start N).refresh N).log.length⟩
    have hph : ((((s.start N).refresh N).prepare N).ws N).phase = .writing o := by
      simp only [World.prepare, hn]
      simp [upd_same, o]
    have h4 : PStep (((s.start N).refresh N).prepare N)
        { (((s.start N).refresh N).prepare N).commit o with
          ws := upd (((s.start N).refresh N).prepare N).ws N
            { (((s.start N).refresh N).prepare N).ws N with
              phase := .idle, written := some o.key, pend := none } } :=
      .land _ N o hph (by simp only [World.prepare, hn, o])
    refine ⟨_, .step h1 (.step h2 (.step h3 (.step h4 (.refl _)))), ?_⟩
    refine ⟨rfl, ⟨o.key, ?_, ?_, ?_⟩, fun j => ?_⟩
    · exact record_cons rfl
    · simp only [World.prepare, hn, o]; exact hw2.2.1
    · simp only [World.prepare, hn, o]; exact hw2.2.2
    · by_cases hj : j = N
      · subst hj
        right
        simp [upd_same, World.prepare, hn] <;> first | rfl | exact hw2.2.1
      · simp only [World.prepare, hn, World.start, World.refresh, World.commit] at *
        rw [upd_other _ _ hj, upd_other _ _ hj, upd_other _ _ hj, upd_other _ _ hj]
        rcases hq j with h | ⟨h, hp⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inl h, hp⟩

end Refresh

open Refresh

/-- From every reachable state with no write of a crashed process in flight, the
processes' own steps, with no source change, deploy, foreign commit, crash or
lost acknowledgement, bring the sink's table to the deployed plan's state of
the source, and every further process step leaves it there (#933: the safety
half of `Converges`; the fairness that makes the processes take these steps
is a hypothesis of the TLA+ model and not stated here). -/
theorem Refresh.quiet {s : World} (h : Reachable s) (hz : s.zombies = []) :
    ∃ t, PReach s t ∧ ∀ t', PReach t t' → t'.tbl = .rows s.deployed s.src := by
  obtain ⟨N, hN⟩ := (inv3_reachable h).2
  obtain ⟨d, hd, hdr, hdz, hdN, hdq⟩ := drain N _ s rfl h hz hN
  obtain ⟨t, ht, hc⟩ := fresh N hdr hdq hdN
  refine ⟨t, hd.trans ht, fun t' ht' => ?_⟩
  have hrt := ht.reachable hdr
  have hrt' := ht'.reachable hrt
  have hc' := conv_reach hrt hc ht'
  obtain ⟨hk, ⟨r, hrec, hrp, hrv⟩, _⟩ := hc'
  obtain ⟨r', hr', htbl⟩ := Refresh.record_describes_table hrt' hk
  rw [hrec] at hr'
  simp only [Option.some.injEq] at hr'
  subst hr'
  obtain ⟨e1, e2, _⟩ := ((hd.trans ht).trans ht').env
  rw [htbl]
  simp [Key.tbl, hrp, hrv, e1, e2]

end Substrait
