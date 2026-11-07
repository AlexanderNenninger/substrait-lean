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
                                     written := if w.first then resumed else w.written } }

def prepare (s : World) (i : Nat) : World :=
  let w := s.ws i
  match next (record s.log) (kept s.log) w with
  | .skip wr => { s with ws := upd s.ws i { w with phase := .idle, written := wr, pend := none } }
  | .write m wr =>
    let o : Out := ⟨⟨w.plan, w.ver⟩, m, (wr.map Key.tbl).getD .none, s.log.length⟩
    { s with ws := upd s.ws i { w with phase := .writing o, written := wr,
                                       pend := some ⟨w.plan, w.ver⟩ } }

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

end Substrait
