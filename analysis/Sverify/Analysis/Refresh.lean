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

end Substrait
