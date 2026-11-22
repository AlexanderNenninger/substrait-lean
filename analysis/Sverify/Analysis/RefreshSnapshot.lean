/-
The refresh protocol of one stored node for a source that cannot restore
(`from_frame`, #988), as a transition system (#933).

`Refresh.lean` states the protocol for a durable source, whose version names
its contents. A source that cannot restore numbers its snapshots per process:
a restarted process counts again from the record's version, and the digest of
the contents the record carries says whether the sink holds this very state
(`Contract.digests`, #965). This module states the protocol sverify runs with
that digest and with the restore of #889, the model's `Durable = FALSE` with
every `Fix*` switch on, and proves its safety for every scope.

The data is abstract as in `Refresh.lean`. The source is a counter of its
contents `c`. The node's rows are `Tbl.rows plan c`; a commit's key is the
plan, the process's version and the digest, which is the contents' counter, so
the key names the table it wrote (`Key.tbl`).

The view a process computes is left out, and that is sound. In the TLA+ model a
process's view is `rows plan c` of the contents `c` it read, except on its first
refresh when it resumes: there the view is `rows plan c` only if the table it
read back is the record's state, and `Corrupt` otherwise. The resume happens
only under `same` (the record is the newest commit and of the process's plan),
and then `record_describes_table` says the table is exactly the record's state,
`rows r.plan r.dig`. So the `Corrupt` branch is never taken on a reachable
state, and the view is always `rows plan c`; the model's `refresh` reads
`s.tbl` as the written table under the same condition.
-/

namespace Substrait
namespace RefreshSnap

inductive Tbl where
  | none
  | rows (plan c : Nat)
  | foreign
  | corrupt
  deriving DecidableEq, Repr

/-- What a commit's contract says: the plan, the writing process's version of
the source and the digest of the contents. -/
structure Key where
  plan : Nat
  ver : Nat
  dig : Nat
  deriving DecidableEq, Repr

def Key.tbl (k : Key) : Tbl := .rows k.plan k.dig

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
change to the table `base`, and the log length `contract()` read. -/
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

/-- A process refreshing the node: its plan, its version and the contents it
read, the table it wrote, skipped to or resumed from (`_written`) and the
record of it (`last`), a write that raised (`pend`), and a ghost: the record
its first refresh could resume from, until its first `prepare` (#889). -/
structure Writer where
  phase : Phase := .down
  plan : Nat := 0
  first : Bool := true
  ver : Nat := 0
  c : Nat := 0
  written : Tbl := .none
  last : Option Key := none
  pend : Option Key := none
  resumable : Option Key := none
  deriving DecidableEq, Repr

structure World where
  src : Nat := 0
  log : List Commit := []
  tbl : Tbl := .none
  ws : Nat → Writer := fun _ => {}
  zombies : List Out := []
  deployed : Nat := 0

def upd (f : Nat → Writer) (i : Nat) (w : Writer) : Nat → Writer :=
  fun j => if j = i then w else f j

def record (log : List Commit) : Option Key := (log.find? (·.app)).map (·.key)

def kept : List Commit → Bool
  | c :: _ => c.app
  | [] => false

inductive Decision where
  | skip (ver : Nat) (written : Tbl) (last : Option Key)
  | write (mode : Mode) (ver : Nat) (written : Tbl) (last : Option Key)
  deriving DecidableEq, Repr

/-- The record is the write the process sent last, which raised (`_pending`). -/
def hitOf (rec : Option Key) (w : Writer) : Bool :=
  match w.pend, rec with
  | some p, some r => p == r
  | _, _ => false

/-- The table and its record the process writes on: after a write that raised
and landed, the record's own; else what it holds. -/
def w0Of (rec : Option Key) (w : Writer) : Tbl :=
  if hitOf rec w then (w.pend.map Key.tbl).getD .none else w.written

def l0Of (rec : Option Key) (w : Writer) : Option Key :=
  if hitOf rec w then rec else w.last

/-- The sink has this very state: the plan, and the digest of the contents. -/
def sameOf (r : Key) (k : Bool) (w : Writer) : Bool := r.plan == w.plan && k && r.dig == w.c

/-- The sink has other contents at a version not below the process's. -/
def clashOf (r : Key) (w : Writer) : Bool :=
  r.plan == w.plan && decide (w.ver ≤ r.ver) && r.dig != w.c

/-- The version the process commits: above a clashing record. -/
def verOf (r : Key) (w : Writer) : Nat := if clashOf r w then r.ver + 1 else w.ver

/-- The record has this state or a later one. -/
def skip2Of (r : Key) (k : Bool) (w : Writer) : Bool :=
  r.plan == w.plan && k && !clashOf r w && decide (verOf r w ≤ r.ver)

/-- The process may not write a change on what it holds. -/
def badOf (r : Key) (k : Bool) (w : Writer) (l0 : Option Key) : Bool :=
  r.plan != w.plan || !k || l0 != some r || clashOf r w

/-- `Sink._commit`'s decision, from the sink's record and the writer's own
state: skip when the sink has this state or a later one, number the state
above a record of other contents at its version, and write the change only
on the record the process wrote, skipped to or resumed from. -/
def next (rec : Option Key) (kept : Bool) (w : Writer) : Decision :=
  match rec with
  | none => .write (if w0Of none w = .none then .replace else .merge) w.ver (w0Of none w)
      (l0Of none w)
  | some r =>
    if sameOf r kept w then .skip r.ver (Key.tbl ⟨w.plan, 0, w.c⟩) (some r)
    else if skip2Of r kept w then .skip w.ver .none none
    else
      let wr : Tbl := if badOf r kept w (l0Of (some r) w) then .none else w0Of (some r) w
      .write (if wr = .none then .replace else .merge) (verOf r w) wr (l0Of (some r) w)

def newTbl (o : Out) (t : Tbl) : Tbl :=
  match o.mode with
  | .replace => o.key.tbl
  | .merge => if t = o.base then o.key.tbl else .corrupt

namespace World

def start (s : World) (i : Nat) : World :=
  { s with ws := upd s.ws i { phase := .idle, plan := s.deployed } }

def stop (s : World) (i : Nat) : World :=
  { s with ws := upd s.ws i {} }

/-- `Group.refresh` up to the write: the process reads the source; on its first
refresh it resumes from the sink's record, when that is its plan's and the
newest commit. -/
def refreshW (s : World) (i : Nat) : Writer :=
  let w := s.ws i
  let rec_ := record s.log
  let same : Bool := match rec_ with
    | some r => kept s.log && r.plan == w.plan
    | none => false
  let ver : Nat :=
    if w.first then
      match rec_ with
      | some r => if r.dig == s.src then r.ver else r.ver + 1
      | none => 1
    else if s.src != w.c then w.ver + 1 else w.ver
  { w with phase := .ready, first := false, ver := ver, c := s.src,
           written := if w.first then (if same then s.tbl else .none) else w.written,
           last := if w.first then (if same then rec_ else none) else w.last,
           resumable := if w.first && same then rec_ else none }

def refresh (s : World) (i : Nat) : World := { s with ws := upd s.ws i (refreshW s i) }

def prepare (s : World) (i : Nat) : World :=
  let w := s.ws i
  match next (record s.log) (kept s.log) w with
  | .skip v wr l =>
    { s with ws := upd s.ws i { w with phase := .idle, ver := v, written := wr, last := l,
                                       pend := none, resumable := none } }
  | .write m v wr l =>
    let o : Out := ⟨⟨w.plan, v, w.c⟩, m, wr, s.log.length⟩
    { s with ws := upd s.ws i { w with phase := .writing o, ver := v, written := wr, last := l,
                                       pend := some o.key, resumable := none } }

def commit (s : World) (o : Out) : World :=
  { s with log := ⟨true, o.key⟩ :: s.log, tbl := newTbl o s.tbl }

def crash (s : World) (i : Nat) : World :=
  { s with ws := upd s.ws i {},
           zombies := match (s.ws i).phase with
             | .writing o => o :: s.zombies
             | _ => s.zombies }

end World

inductive Step : World → World → Prop where
  | start (s i) : (s.ws i).phase = .down → Step s (s.start i)
  | stop (s i) : (s.ws i).phase = .idle → (s.ws i).plan ≠ s.deployed → Step s (s.stop i)
  | refresh (s i) : (s.ws i).phase = .idle → Step s (s.refresh i)
  | prepare (s i) : (s.ws i).phase = .ready → Step s (s.prepare i)
  | land (s i o) : (s.ws i).phase = .writing o → s.log.length = o.head →
      Step s { s.commit o with
        ws := upd s.ws i { s.ws i with phase := .idle, written := o.key.tbl,
                                       last := some o.key, pend := none } }
  | landLostAck (s i o) : (s.ws i).phase = .writing o → s.log.length = o.head →
      Step s { s.commit o with ws := upd s.ws i { s.ws i with phase := .idle } }
  | fail (s i o) : (s.ws i).phase = .writing o →
      Step s { s with ws := upd s.ws i { s.ws i with phase := .idle } }
  | conflict (s i o) : (s.ws i).phase = .writing o → s.log.length ≠ o.head →
      Step s { s with ws := upd s.ws i { s.ws i with phase := .idle, written := .none,
                                                     pend := none } }
  | crash (s i) : (s.ws i).phase ≠ .down → Step s (s.crash i)
  | zombieLands (s o) : o ∈ s.zombies → s.log.length = o.head →
      Step s { s.commit o with zombies := s.zombies.erase o }
  | sourceChanges (s) : Step s { s with src := s.src + 1 }
  | foreignWrite (s) : Step s { s with log := ⟨false, ⟨0, 0, 0⟩⟩ :: s.log, tbl := .foreign }
  | deploy (s) : Step s { s with deployed := s.deployed + 1 }

inductive Reachable : World → Prop where
  | init : Reachable {}
  | step {s t} : Reachable s → Step s t → Reachable t

theorem upd_same (f : Nat → Writer) (i : Nat) (w : Writer) : upd f i w i = w := by
  simp [upd]

theorem upd_other (f : Nat → Writer) {i j : Nat} (w : Writer) (h : j ≠ i) :
    upd f i w j = f j := by
  simp [upd, h]

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

/-- A write in flight read a log no longer than the current one, and while the
log is still the one it read, its change was computed against the table. -/
def OutOK (s : World) (o : Out) : Prop :=
  o.head ≤ s.log.length ∧ (o.mode = .merge → s.log.length = o.head → s.tbl = o.base)

/-- The log has a commit of the node with this key. -/
def AppKey (log : List Commit) (k : Key) : Prop := ∃ c ∈ log, c.app = true ∧ c.key = k

/-- A process that holds a table holds the table of a commit of the node, which
its `last` names. -/
def WOK (s : World) : Prop :=
  ∀ i, (s.ws i).written ≠ .none →
    ∃ k, (s.ws i).last = some k ∧ (s.ws i).written = k.tbl ∧ AppKey s.log k

def Inv (s : World) : Prop := TblOK s ∧ (∀ o, Pending s o → OutOK s o) ∧ WOK s

theorem pending_upd {s : World} {i : Nat} {w : Writer} {o : Out}
    (hw : ∀ o', w.phase ≠ .writing o') (h : Pending { s with ws := upd s.ws i w } o) :
    Pending s o := by
  rcases h with ⟨j, hj⟩ | hz
  · change (upd s.ws i w j).phase = _ at hj
    by_cases hji : j = i
    · subst hji; rw [upd_same] at hj; exact absurd hj (hw o)
    · exact Or.inl ⟨j, by rw [upd_other _ _ hji] at hj; exact hj⟩
  · exact Or.inr hz

theorem record_cons {c : Commit} {rest : List Commit} (h : c.app = true) :
    record (c :: rest) = some c.key := by
  simp [record, List.find?, h]

theorem record_of_kept {log : List Commit} (h : kept log = true) :
    ∃ c rest, log = c :: rest ∧ c.app = true ∧ record log = some c.key := by
  cases log with
  | nil => simp [kept] at h
  | cons c rest =>
    simp only [kept] at h
    exact ⟨c, rest, rfl, h, record_cons h⟩

theorem record_appkey {log : List Commit} {r : Key} (h : record log = some r) : AppKey log r := by
  unfold record at h
  cases hf : log.find? (·.app) with
  | none => simp [hf] at h
  | some c =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    exact ⟨c, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩

/-- A step that keeps the log and the table, and starts no write. -/
theorem inv_of_keep {s t : World} (hs : Inv s) (hlog : t.log = s.log) (htbl : t.tbl = s.tbl)
    (hws : ∀ i, (t.ws i).written = (s.ws i).written ∧ (t.ws i).last = (s.ws i).last)
    (hp : ∀ o, Pending t o → Pending s o) : Inv t := by
  refine ⟨?_, fun o ho => ?_, fun i hi => ?_⟩
  · have := hs.1; unfold TblOK at this ⊢; rw [hlog, htbl]; exact this
  · have := hs.2.1 o (hp o ho); unfold OutOK at this ⊢; rw [hlog, htbl]; exact this
  · obtain ⟨hw, hl⟩ := hws i
    rw [hw] at hi
    obtain ⟨k, hk, hk2, hk3⟩ := hs.2.2 i hi
    exact ⟨k, by rw [hl]; exact hk, by rw [hw]; exact hk2, by rw [hlog]; exact hk3⟩

theorem sameOf_iff {r : Key} {k : Bool} {w : Writer} :
    sameOf r k w = true ↔ r.plan = w.plan ∧ k = true ∧ r.dig = w.c := by
  simp [sameOf, and_assoc]

/-- A skip leaves no table, or the record's. -/
theorem next_skip {rec : Option Key} {k : Bool} {w : Writer} {v : Nat} {wr : Tbl}
    {l : Option Key} (h : next rec k w = .skip v wr l) :
    wr = .none ∨ ∃ r, rec = some r ∧ wr = r.tbl ∧ l = some r := by
  cases rec with
  | none => simp only [next] at h; split at h <;> cases h
  | some r =>
    simp only [next] at h
    split at h
    · next hs =>
      simp only [Decision.skip.injEq] at h
      obtain ⟨_, rfl, rfl⟩ := h
      obtain ⟨h1, _, h3⟩ := sameOf_iff.mp hs
      exact Or.inr ⟨r, rfl, by simp [Key.tbl, h1, h3], rfl⟩
    · split at h
      · simp only [Decision.skip.injEq] at h
        exact Or.inl h.2.1.symm
      · split at h <;> cases h

theorem hitOf_some {r : Key} {w : Writer} (h : hitOf (some r) w = true) : w.pend = some r := by
  unfold hitOf at h
  cases hp : w.pend with
  | none => simp [hp] at h
  | some p => simp [hp] at h; rw [h]

theorem ite_replace {c : Prop} [Decidable c] :
    (if c then Mode.replace else Mode.merge) = Mode.replace ↔ c := by
  by_cases h : c <;> simp [h]

theorem ite_merge {c : Prop} [Decidable c] :
    (if c then Mode.replace else Mode.merge) = Mode.merge ↔ ¬c := by
  by_cases h : c <;> simp [h]

/-- A write that replaces the table has none to change. -/
theorem next_replace {rec : Option Key} {k : Bool} {w : Writer} {v : Nat} {wr : Tbl}
    {l : Option Key} (h : next rec k w = .write .replace v wr l) : wr = .none := by
  cases rec with
  | none =>
    simp only [next, Decision.write.injEq] at h
    obtain ⟨hm, _, rfl, _⟩ := h
    exact ite_replace.mp hm
  | some r =>
    simp only [next] at h
    split at h
    · cases h
    · split at h
      · cases h
      · simp only [Decision.write.injEq] at h
        obtain ⟨hm, _, rfl, _⟩ := h
        exact ite_replace.mp hm

/-- A write of a change is on the record, which the process holds. -/
theorem next_merge {rec : Option Key} {k : Bool} {w : Writer} {v : Nat} {wr : Tbl}
    {l : Option Key}
    (hw : w.written ≠ .none → (∃ k, w.last = some k ∧ w.written = k.tbl) ∧ rec ≠ none)
    (h : next rec k w = .write .merge v wr l) :
    ∃ r, rec = some r ∧ k = true ∧ wr = r.tbl ∧ l = some r := by
  cases rec with
  | none =>
    simp only [next, Decision.write.injEq] at h
    obtain ⟨hm, _, rfl, _⟩ := h
    exfalso
    have hn := ite_merge.mp hm
    have h0 : w.written ≠ .none := by
      intro hz; apply hn; simp [w0Of, hitOf, hz]
    exact (hw h0).2 rfl
  | some r =>
    simp only [next] at h
    split at h
    · cases h
    · split at h
      · cases h
      · simp only [Decision.write.injEq] at h
        obtain ⟨hm, _, rfl, rfl⟩ := h
        have hne := ite_merge.mp hm
        split at hne
        · exact absurd rfl hne
        · next hbad =>
          have hk : k = true := by
            cases k with
            | true => rfl
            | false => exact absurd (by simp [badOf]) hbad
          have hl : l0Of (some r) w = some r := by
            by_cases hl : l0Of (some r) w = some r
            · exact hl
            · exact absurd (by simp [badOf, hl]) hbad
          refine ⟨r, rfl, hk, ?_, hl⟩
          simp only [hbad]
          by_cases hh : hitOf (some r) w = true
          · simp [w0Of, hh, hitOf_some hh]
          · have hw0 : w0Of (some r) w = w.written := by simp [w0Of, hh]
            rw [hw0] at hne ⊢
            have hl' : w.last = some r := by
              simpa [l0Of, hh] using hl
            obtain ⟨⟨k', hk', hk2⟩, _⟩ := hw hne
            rw [hk'] at hl'
            simp only [Option.some.injEq] at hl'
            rw [hk2, hl']; rfl

theorem record_ne_none {log : List Commit} {k : Key} (h : AppKey log k) : record log ≠ none := by
  obtain ⟨c, hc, hca, _⟩ := h
  unfold record
  intro h0
  have h1 : log.find? (·.app) = none := by simpa using h0
  have := List.find?_eq_none.mp h1 c hc
  simp [hca] at this

theorem appkey_cons {log : List Commit} {c : Commit} {k : Key} (h : AppKey log k) :
    AppKey (c :: log) k := by
  obtain ⟨d, hd, h2⟩ := h
  exact ⟨d, List.mem_cons_of_mem _ hd, h2⟩

/-- A step that changes one writer, to one that is not writing, and nothing
else. -/
theorem inv_of_upd {s t : World} {i : Nat} {w : Writer} (hs : Inv s)
    (hws : t.ws = upd s.ws i w) (hlog : t.log = s.log) (htbl : t.tbl = s.tbl)
    (hz : ∀ o, o ∈ t.zombies → Pending s o)
    (hw : w.written ≠ .none → ∃ k, w.last = some k ∧ w.written = k.tbl ∧ AppKey s.log k)
    (hph : ∀ o, w.phase ≠ .writing o) : Inv t := by
  refine ⟨?_, fun o ho => ?_, fun j hj => ?_⟩
  · have := hs.1; unfold TblOK at this ⊢; rw [hlog, htbl]; exact this
  · have hp : Pending s o := by
      rcases ho with ⟨j, hj⟩ | hz'
      · rw [hws] at hj
        by_cases hji : j = i
        · subst hji; rw [upd_same] at hj; exact absurd hj (hph o)
        · exact Or.inl ⟨j, by rw [upd_other _ _ hji] at hj; exact hj⟩
      · exact hz o hz'
    have := hs.2.1 o hp; unfold OutOK at this ⊢; rw [hlog, htbl]; exact this
  · rw [hws] at hj ⊢
    by_cases hji : j = i
    · subst hji; rw [upd_same] at hj ⊢
      obtain ⟨k, hk1, hk2, hk3⟩ := hw hj
      exact ⟨k, hk1, hk2, by rw [hlog]; exact hk3⟩
    · rw [upd_other _ _ hji] at hj ⊢
      obtain ⟨k, hk1, hk2, hk3⟩ := hs.2.2 j hj
      exact ⟨k, hk1, hk2, by rw [hlog]; exact hk3⟩

/-- A commit of `o` on the log `o` read. -/
theorem inv_commit {s t : World} {o : Out} (hs : Inv s) (hpo : Pending s o)
    (hc : s.log.length = o.head) (hlog : t.log = ⟨true, o.key⟩ :: s.log)
    (htbl : t.tbl = newTbl o s.tbl) (hp : ∀ o', Pending t o' → Pending s o')
    (hwok : WOK t) : Inv t := by
  have ho := hs.2.1 o hpo
  refine ⟨?_, fun o' ho' => ?_, hwok⟩
  · unfold TblOK; rw [hlog, htbl]
    simp only [↓reduceIte]
    unfold newTbl
    cases hm : o.mode with
    | replace => rfl
    | merge => simp [ho.2 hm hc]
  · have h' := hs.2.1 o' (hp o' ho')
    unfold OutOK at h' ⊢
    rw [hlog]
    simp only [List.length_cons]
    refine ⟨Nat.le_succ_of_le h'.1, fun _ heq => ?_⟩
    have := h'.1
    omega

/-- The writers' tables survive a commit onto the log. -/
theorem wok_cons {s t : World} {c : Commit} (hs : WOK s) (hws : t.ws = s.ws)
    (hlog : t.log = c :: s.log) : WOK t := by
  intro i hi
  rw [hws] at hi ⊢
  obtain ⟨k, hk1, hk2, hk3⟩ := hs i hi
  exact ⟨k, hk1, hk2, by rw [hlog]; exact appkey_cons hk3⟩

/-- A step that changes nothing but the source or the plan deployed. -/
theorem inv_of_same {s t : World} (hs : Inv s) (hws : t.ws = s.ws) (hlog : t.log = s.log)
    (htbl : t.tbl = s.tbl) (hz : t.zombies = s.zombies) : Inv t := by
  refine ⟨?_, fun o ho => ?_, fun j hj => ?_⟩
  · have := hs.1; unfold TblOK at this ⊢; rw [hlog, htbl]; exact this
  · have hp : Pending s o := by
      rcases ho with ⟨j, hj⟩ | hz'
      · rw [hws] at hj; exact Or.inl ⟨j, hj⟩
      · exact Or.inr (hz ▸ hz')
    have := hs.2.1 o hp; unfold OutOK at this ⊢; rw [hlog, htbl]; exact this
  · rw [hws] at hj ⊢
    obtain ⟨k, hk1, hk2, hk3⟩ := hs.2.2 j hj
    exact ⟨k, hk1, hk2, by rw [hlog]; exact hk3⟩

/-- A commit, and the change of one writer. -/
theorem wok_upd_commit {s : World} {o : Out} {i : Nat} {w : Writer} (hs : WOK s)
    (hw : w.written ≠ .none → ∃ k, w.last = some k ∧ w.written = k.tbl ∧
      AppKey (⟨true, o.key⟩ :: s.log) k) :
    WOK { s.commit o with ws := upd s.ws i w } := by
  intro j hj
  by_cases hji : j = i
  · subst hji
    change (upd s.ws j w j).written ≠ _ at hj
    rw [upd_same] at hj
    change ∃ k, (upd s.ws j w j).last = some k ∧ (upd s.ws j w j).written = k.tbl ∧ _
    rw [upd_same]
    exact hw hj
  · change (upd s.ws i w j).written ≠ _ at hj
    rw [upd_other _ _ hji] at hj
    obtain ⟨k, hk1, hk2, hk3⟩ := hs j hj
    change ∃ k, (upd s.ws i w j).last = some k ∧ (upd s.ws i w j).written = k.tbl ∧ _
    rw [upd_other _ _ hji]
    exact ⟨k, hk1, hk2, appkey_cons hk3⟩

theorem inv_step {s t : World} (hs : Inv s) (h : Step s t) : Inv t := by
  cases h with
  | start i _ =>
    exact inv_of_upd hs rfl rfl rfl (fun o h => Or.inr h) (fun h => absurd rfl h)
      (fun o h => by cases h)
  | stop i _ _ =>
    exact inv_of_upd hs rfl rfl rfl (fun o h => Or.inr h) (fun h => absurd rfl h)
      (fun o h => by cases h)
  | refresh i _ =>
    refine inv_of_upd hs rfl rfl rfl (fun o h => Or.inr h) ?_ (fun o h => by cases h)
    intro hne
    by_cases hf : (s.ws i).first = true
    · cases hrec : record s.log with
      | none => simp [World.refreshW, hf, hrec] at hne
      | some r =>
        by_cases hk : kept s.log = true ∧ r.plan = (s.ws i).plan
        · obtain ⟨c, rest, hlog, happ, hrc⟩ := record_of_kept hk.1
          have htbl := hs.1
          unfold TblOK at htbl
          rw [hlog] at htbl
          simp only [happ, ↓reduceIte] at htbl
          rw [hrec] at hrc
          simp only [Option.some.injEq] at hrc
          refine ⟨r, ?_, ?_, record_appkey hrec⟩
          · simp [World.refreshW, hf, hrec, hk.1, hk.2]
          · simp [World.refreshW, hf, hrec, hk.1, hk.2, htbl, ← hrc]
        · exfalso
          apply hne
          simp only [World.refreshW, hf, hrec]
          simp only [Bool.and_eq_true, beq_iff_eq] at *
          simp [hk]
    · have hf' : (s.ws i).first = false := by simpa using hf
      simp only [World.refreshW, hf'] at hne ⊢
      simpa using hs.2.2 i hne
  | prepare i hr =>
    cases hnext : next (record s.log) (kept s.log) (s.ws i) with
    | skip v wr l =>
      simp only [World.prepare, hnext]
      refine inv_of_upd hs rfl rfl rfl (fun o h => Or.inr h) ?_ (fun o h => by cases h)
      intro hne
      rcases next_skip hnext with h0 | ⟨r, hrec, hwr, hl⟩
      · exact absurd h0 hne
      · exact ⟨r, hl, hwr, record_appkey hrec⟩
    | write m v wr l =>
      simp only [World.prepare, hnext]
      have hwi : (s.ws i).written ≠ .none →
          (∃ k, (s.ws i).last = some k ∧ (s.ws i).written = k.tbl) ∧ record s.log ≠ none := by
        intro hne
        obtain ⟨k, h1, h2, h3⟩ := hs.2.2 i hne
        exact ⟨⟨k, h1, h2⟩, record_ne_none h3⟩
      refine ⟨hs.1, fun o ho => ?_, fun j hj => ?_⟩
      · rcases ho with ⟨j, hj⟩ | hz
        · dsimp only at hj
          by_cases hji : j = i
          · subst hji
            rw [upd_same] at hj
            simp only [Phase.writing.injEq] at hj
            subst hj
            refine ⟨Nat.le_refl _, fun hm _ => ?_⟩
            simp only at hm
            subst hm
            obtain ⟨r, hrec, hk, hwr, _⟩ := next_merge hwi hnext
            obtain ⟨c, rest, hlog, happ, hrc⟩ := record_of_kept hk
            have ht := hs.1
            unfold TblOK at ht
            rw [hlog] at ht
            simp only [happ, ↓reduceIte] at ht
            rw [hrec] at hrc
            simp only [Option.some.injEq] at hrc
            simp [ht, hwr, hrc]
          · rw [upd_other _ _ hji] at hj
            exact hs.2.1 o (Or.inl ⟨j, hj⟩)
        · exact hs.2.1 o (Or.inr hz)
      · dsimp only at hj ⊢
        by_cases hji : j = i
        · subst hji
          rw [upd_same] at hj ⊢
          cases m with
          | replace => exact absurd (next_replace hnext) hj
          | merge =>
            obtain ⟨r, hrec, _, hwr, hl⟩ := next_merge hwi hnext
            exact ⟨r, hl, hwr, record_appkey hrec⟩
        · rw [upd_other _ _ hji] at hj ⊢
          exact hs.2.2 j hj
  | land i o hw hc =>
    refine inv_commit hs (Or.inl ⟨i, hw⟩) hc rfl rfl (fun o' ho' => ?_) ?_
    · exact pending_upd (s := s.commit o) (by intro o' h; cases h) ho'
    · refine wok_upd_commit hs.2.2 ?_
      intro _
      exact ⟨o.key, rfl, rfl, ⟨⟨true, o.key⟩, List.mem_cons_self .., rfl, rfl⟩⟩
  | landLostAck i o hw hc =>
    refine inv_commit hs (Or.inl ⟨i, hw⟩) hc rfl rfl (fun o' ho' => ?_) ?_
    · have hw' : ∀ o'', ({ s.ws i with phase := .idle } : Writer).phase ≠ .writing o'' := by
        intro o'' h; cases h
      exact pending_upd (s := s.commit o) hw' ho'
    · refine wok_upd_commit hs.2.2 ?_
      intro hne
      obtain ⟨k, h1, h2, h3⟩ := hs.2.2 i hne
      exact ⟨k, h1, h2, appkey_cons h3⟩
  | fail i o _ =>
    exact inv_of_upd hs rfl rfl rfl (fun o h => Or.inr h) (fun hne => hs.2.2 i hne)
      (fun o' h => by cases h)
  | conflict i o _ _ =>
    exact inv_of_upd hs rfl rfl rfl (fun o h => Or.inr h) (fun h => absurd rfl h)
      (fun o' h => by cases h)
  | crash i _ =>
    refine inv_of_upd (t := s.crash i) hs rfl rfl rfl ?_ (fun h => absurd rfl h)
      (fun o h => by cases h)
    intro o ho
    unfold World.crash at ho
    simp only at ho
    split at ho
    · next o' hph =>
      rcases List.mem_cons.mp ho with rfl | hz
      · exact Or.inl ⟨i, hph⟩
      · exact Or.inr hz
    · exact Or.inr ho
  | zombieLands o hz hc =>
    refine inv_commit hs (Or.inr hz) hc rfl rfl (fun o' ho' => ?_) (wok_cons hs.2.2 rfl rfl)
    rcases ho' with ⟨j, hj⟩ | hz'
    · exact Or.inl ⟨j, hj⟩
    · exact Or.inr (List.mem_of_mem_erase hz')
  | sourceChanges => exact inv_of_same hs rfl rfl rfl rfl
  | foreignWrite =>
    refine ⟨by simp [TblOK], fun o ho => ?_, wok_cons hs.2.2 rfl rfl⟩
    have h' := hs.2.1 o ho
    unfold OutOK at h' ⊢
    simp only [List.length_cons]
    refine ⟨Nat.le_succ_of_le h'.1, fun _ heq => ?_⟩
    have := h'.1
    omega
  | deploy => exact inv_of_same hs rfl rfl rfl rfl

theorem inv_init : Inv ({} : World) :=
  ⟨rfl, fun o ho => (by rcases ho with ⟨_, h⟩ | h <;> cases h), fun i hi => absurd rfl hi⟩

theorem inv_reachable {s : World} (h : Reachable s) : Inv s := by
  induction h with
  | init => exact inv_init
  | step _ hst ih => exact inv_step ih hst


/-! ## What a write reads, and the order of the commits

`ReadIsHead`, `Monotone` and `NoRewriteUnchanged` of `models/refresh/Refresh.tla`,
for a source that cannot restore. While the log still has the length a write
read, it is the log the write read: its change was computed from the newest
commit of the node, and its state is above that commit's, of other contents. -/

/-- Adjacent commits of the node under one plan: a version not below the
earlier one, and other contents (no state is committed twice in a row). -/
def AdjOK : List Commit → Prop
  | c' :: c :: rest =>
      (c'.app = true → c.app = true → c.key.plan = c'.key.plan →
        c.key.ver ≤ c'.key.ver ∧ c.key.dig ≠ c'.key.dig) ∧ AdjOK (c :: rest)
  | _ => True

def Reads (s : World) (o : Out) : Prop :=
  s.log.length = o.head →
    (∀ c rest, s.log = c :: rest → c.app = true → c.key.plan = o.key.plan →
        c.key.ver ≤ o.key.ver ∧ c.key.dig ≠ o.key.dig) ∧
    (o.mode = .merge → kept s.log = true ∧ ∃ r, record s.log = some r ∧ o.base = r.tbl)

def Inv2 (s : World) : Prop := AdjOK s.log ∧ ∀ o, Pending s o → Reads s o

theorem kept_cons {c : Commit} {rest : List Commit} (h : c.app = true) :
    kept (c :: rest) = true := by
  simp [kept, h]

/-- A write of the process, on a record of its plan, is of a version not below
the record's, and of other contents: the record has the state or a later one
otherwise. -/
theorem next_above {r : Key} {k : Bool} {w : Writer} {m : Mode} {v : Nat} {wr : Tbl}
    {l : Option Key} (h : next (some r) k w = .write m v wr l) (hk : k = true)
    (hp : r.plan = w.plan) : r.ver ≤ v ∧ r.dig ≠ w.c := by
  simp only [next] at h
  split at h
  · cases h
  · next hs =>
    split at h
    · cases h
    · next hs2 =>
      simp only [Decision.write.injEq] at h
      obtain ⟨_, rfl, _, _⟩ := h
      refine ⟨?_, fun hd => hs ?_⟩
      · by_cases hc : clashOf r w = true
        · simp [verOf, hc]
        · apply Nat.le_of_lt
          by_cases hv : verOf r w ≤ r.ver
          · exact absurd (by simp [skip2Of, hp, hk, hc, hv]) hs2
          · omega
      · exact sameOf_iff.mpr ⟨hp, hk, hd⟩

theorem inv2_of_upd {s t : World} {i : Nat} {w : Writer} (hs : Inv2 s)
    (hws : t.ws = upd s.ws i w) (hlog : t.log = s.log)
    (hz : ∀ o, o ∈ t.zombies → Pending s o) (hph : ∀ o, w.phase ≠ .writing o) : Inv2 t := by
  refine ⟨by rw [hlog]; exact hs.1, fun o ho => ?_⟩
  have hp : Pending s o := by
    rcases ho with ⟨j, hj⟩ | hz'
    · rw [hws] at hj
      by_cases hji : j = i
      · subst hji; rw [upd_same] at hj; exact absurd hj (hph o)
      · exact Or.inl ⟨j, by rw [upd_other _ _ hji] at hj; exact hj⟩
    · exact hz o hz'
  have := hs.2 o hp
  unfold Reads at this ⊢
  rw [hlog]
  exact this

theorem inv2_of_same {s t : World} (hs : Inv2 s) (hws : t.ws = s.ws) (hlog : t.log = s.log)
    (hz : t.zombies = s.zombies) : Inv2 t := by
  refine ⟨by rw [hlog]; exact hs.1, fun o ho => ?_⟩
  have hp : Pending s o := by
    rcases ho with ⟨j, hj⟩ | hz'
    · rw [hws] at hj; exact Or.inl ⟨j, hj⟩
    · exact Or.inr (hz ▸ hz')
  have := hs.2 o hp
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
      exact ⟨fun _ hca hpl => (hr.1 c rest hl hca hpl), h1⟩
  · have hh := (hi.2.1 o' (hp o' ho')).1
    intro heq
    exfalso
    rw [hlog] at heq
    have heq' : s.log.length + 1 = o'.head := heq
    omega

theorem inv2_step {s t : World} (hi : Inv s) (hs : Inv2 s) (h : Step s t) : Inv2 t := by
  cases h with
  | start i _ => exact inv2_of_upd hs rfl rfl (fun o h => Or.inr h) (fun o h => by cases h)
  | stop i _ _ => exact inv2_of_upd hs rfl rfl (fun o h => Or.inr h) (fun o h => by cases h)
  | refresh i _ => exact inv2_of_upd hs rfl rfl (fun o h => Or.inr h) (fun o h => by cases h)
  | prepare i hr =>
    cases hnext : next (record s.log) (kept s.log) (s.ws i) with
    | skip v wr l =>
      simp only [World.prepare, hnext]
      exact inv2_of_upd hs rfl rfl (fun o h => Or.inr h) (fun o h => by cases h)
    | write m v wr l =>
      simp only [World.prepare, hnext]
      have hwi : (s.ws i).written ≠ .none →
          (∃ k, (s.ws i).last = some k ∧ (s.ws i).written = k.tbl) ∧ record s.log ≠ none := by
        intro hne
        obtain ⟨k, h1, h2, h3⟩ := hi.2.2 i hne
        exact ⟨⟨k, h1, h2⟩, record_ne_none h3⟩
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
            obtain ⟨h1, h2⟩ := next_above hnext rfl hpl
            exact ⟨h1, fun h => h2 h⟩
          · simp only at hm
            subst hm
            obtain ⟨r, hrec, hk, hwr, _⟩ := next_merge hwi hnext
            exact ⟨hk, r, hrec, hwr⟩
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
  | fail i o _ => exact inv2_of_upd hs rfl rfl (fun o h => Or.inr h) (fun o' h => by cases h)
  | conflict i o _ _ => exact inv2_of_upd hs rfl rfl (fun o h => Or.inr h) (fun o' h => by cases h)
  | crash i _ =>
    refine inv2_of_upd (t := s.crash i) hs rfl rfl ?_ (fun o h => by cases h)
    intro o ho
    unfold World.crash at ho
    simp only at ho
    split at ho
    · next o' hph =>
      rcases List.mem_cons.mp ho with rfl | hz
      · exact Or.inl ⟨i, hph⟩
      · exact Or.inr hz
    · exact Or.inr ho
  | zombieLands o hz hc =>
    refine inv2_of_commit hi hs (Or.inr hz) hc rfl fun o' ho' => ?_
    rcases ho' with ⟨j, hj⟩ | hz'
    · exact Or.inl ⟨j, hj⟩
    · exact Or.inr (List.mem_of_mem_erase hz')
  | sourceChanges => exact inv2_of_same hs rfl rfl rfl
  | foreignWrite =>
    refine ⟨?_, fun o ho => ?_⟩
    · show AdjOK (⟨false, ⟨0, 0, 0⟩⟩ :: s.log)
      have h1 := hs.1
      cases hl : s.log with
      | nil => simp [AdjOK]
      | cons c rest =>
        rw [hl] at h1
        exact ⟨fun h => absurd h (by simp), h1⟩
    · have h' := (hi.2.1 o ho).1
      intro heq
      exfalso
      have heq' : s.log.length + 1 = o.head := heq
      omega
  | deploy => exact inv2_of_same hs rfl rfl rfl

theorem inv2_reachable {s : World} (h : Reachable s) : Inv2 s := by
  induction h with
  | init => exact ⟨trivial, fun o ho => (by rcases ho with ⟨_, h⟩ | h <;> cases h)⟩
  | step hr hst ih => exact inv2_step (inv_reachable hr) ih hst


/-! ## #889: what a new process does with the sink's record -/

/-- A process that holds the record as its own, of its plan, with a version
not below it (and its digest, when equal), writes at most a change on it. -/
theorem next_resumes {r : Key} {w : Writer} (hp : r.plan = w.plan) (hl : w.last = some r)
    (hw : w.written = r.tbl) (hv : r.ver ≤ w.ver) (hd : r.ver = w.ver → r.dig = w.c)
    (v : Nat) (wr : Tbl) (l : Option Key) : next (some r) true w ≠ .write .replace v wr l := by
  intro h
  simp only [next] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Decision.write.injEq] at h
      obtain ⟨hm, _, rfl, _⟩ := h
      have hne := ite_replace.mp hm
      have hl0 : l0Of (some r) w = some r := by
        unfold l0Of; split
        · rfl
        · exact hl
      have hnb : badOf r true w (l0Of (some r) w) = false := by
        have hc : clashOf r w = false := by
          by_cases hle : w.ver ≤ r.ver
          · have := hd (Nat.le_antisymm hv hle)
            simp [clashOf, this]
          · simp [clashOf, hle]
        simp [badOf, hp, hl0, hc]
      simp only [hnb, Bool.false_eq_true, ↓reduceIte] at hne
      unfold w0Of at hne
      split at hne
      · next hh =>
        simp [hitOf_some hh, Key.tbl] at hne
      · rw [hw] at hne
        simp [Key.tbl] at hne

/-- A process that is ready and could resume from `r` holds `r` as its own,
under its plan, with a version not below it. -/
def ResOK (s : World) : Prop :=
  ∀ i r, (s.ws i).phase = .ready → (s.ws i).resumable = some r →
    (s.ws i).written = r.tbl ∧ (s.ws i).last = some r ∧ r.plan = (s.ws i).plan ∧
      r.ver ≤ (s.ws i).ver ∧ (r.ver = (s.ws i).ver → r.dig = (s.ws i).c)

theorem resok_step {s t : World} (hi : Inv s) (hs : ResOK s) (h : Step s t) : ResOK t := by
  have other : ∀ (i : Nat) (w : Writer), (∀ r, w.phase = .ready → w.resumable = some r →
      w.written = r.tbl ∧ w.last = some r ∧ r.plan = w.plan ∧ r.ver ≤ w.ver ∧
        (r.ver = w.ver → r.dig = w.c)) →
      ∀ ws : Nat → Writer, ws = upd s.ws i w → ∀ j r, (ws j).phase = .ready →
        (ws j).resumable = some r →
        (ws j).written = r.tbl ∧ (ws j).last = some r ∧ r.plan = (ws j).plan ∧
          r.ver ≤ (ws j).ver ∧ (r.ver = (ws j).ver → r.dig = (ws j).c) := by
    intro i w hw ws hws j r hph hr
    subst hws
    by_cases hji : j = i
    · subst hji; rw [upd_same] at hph hr ⊢; exact hw r hph hr
    · rw [upd_other _ _ hji] at hph hr ⊢; exact hs j r hph hr
  cases h with
  | start i _ => exact other i _ (fun r hp => by simp at hp) _ rfl
  | stop i _ _ => exact other i _ (fun r hp => by simp at hp) _ rfl
  | refresh i _ =>
    refine other i _ ?_ _ rfl
    intro r _ hr
    simp only [World.refreshW] at hr ⊢
    by_cases hf : (s.ws i).first = true
    · cases hrec : record s.log with
      | none => simp [hf, hrec] at hr
      | some r' =>
        by_cases hk : kept s.log = true ∧ r'.plan = (s.ws i).plan
        · obtain ⟨c, rest, hlog, happ, hrc⟩ := record_of_kept hk.1
          have htbl := hi.1
          unfold TblOK at htbl
          rw [hlog] at htbl
          simp only [happ, ↓reduceIte] at htbl
          rw [hrec] at hrc
          simp only [Option.some.injEq] at hrc
          simp only [hf, hrec, hk.1, hk.2, Bool.and_self, beq_self_eq_true, ↓reduceIte,
            Option.some.injEq] at hr ⊢
          subst hr
          refine ⟨by simp [htbl, ← hrc], rfl, hk.2, ?_, ?_⟩
          · split <;> omega
          · split
            · next hd => simpa using hd
            · omega
        · exfalso
          simp [hf, hrec] at hr
          exact hk hr.1
    · simp [hf] at hr
  | prepare i _ =>
    cases hnext : next (record s.log) (kept s.log) (s.ws i) with
    | skip v wr l =>
      simp only [World.prepare, hnext]
      exact other i _ (fun r hp => by simp at hp) _ rfl
    | write m v wr l =>
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
  | step hr hst ih => exact resok_step (inv_reachable hr) ih hst


/-! ## The quiet regime

Once the environment is quiet (no source change, deploy, foreign commit, crash,
lost acknowledgement or late write of a crashed process), the processes' own
steps reach the deployed plan's state of the source and keep it. This is the
safety half of the TLA+ model's `Converges`; the fairness that makes the
processes take these steps is not stated here. -/

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
        ws := upd s.ws i { s.ws i with phase := .idle, written := o.key.tbl,
                                       last := some o.key, pend := none } }
  | conflict (s : World) (i : Nat) (o : Out) : (s.ws i).phase = .writing o →
      s.log.length ≠ o.head →
      PStep s { s with ws := upd s.ws i { s.ws i with phase := .idle, written := .none,
                                                      pend := none } }

theorem PStep.step {s t : World} (h : PStep s t) : Step s t := by
  cases h with
  | start i h => exact .start _ i h
  | stop i h1 h2 => exact .stop _ i h1 h2
  | refresh i h => exact .refresh _ i h
  | prepare i h => exact .prepare _ i h
  | land i o h1 h2 => exact .land _ i o h1 h2
  | conflict i o h1 h2 => exact .conflict _ i o h1 h2

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

/-- Only finitely many slots have a process. -/
def FinSupp (s : World) : Prop := ∃ N, ∀ i, N ≤ i → (s.ws i).phase = .down

theorem finsupp_of_upd {s t : World} {i : Nat} {w : Writer} (hs : FinSupp s)
    (hws : t.ws = upd s.ws i w) : FinSupp t := by
  obtain ⟨N, hN⟩ := hs
  refine ⟨max N (i + 1), fun j hj => ?_⟩
  rw [hws, upd_other _ _ (by omega)]
  exact hN j (by omega)

theorem finsupp_of_same {s t : World} (hs : FinSupp s) (hws : t.ws = s.ws) : FinSupp t := by
  obtain ⟨N, hN⟩ := hs
  exact ⟨N, fun j hj => by rw [hws]; exact hN j hj⟩

theorem finsupp_step {s t : World} (hs : FinSupp s) (h : Step s t) : FinSupp t := by
  cases h with
  | start i _ => exact finsupp_of_upd hs rfl
  | stop i _ _ => exact finsupp_of_upd hs rfl
  | refresh i _ => exact finsupp_of_upd hs rfl
  | prepare i _ =>
    cases hnext : next (record s.log) (kept s.log) (s.ws i) with
    | skip v wr l => simp only [World.prepare, hnext]; exact finsupp_of_upd hs rfl
    | write m v wr l => simp only [World.prepare, hnext]; exact finsupp_of_upd hs rfl
  | land i o _ _ => exact finsupp_of_upd hs rfl
  | landLostAck i o _ _ => exact finsupp_of_upd hs rfl
  | fail i o _ => exact finsupp_of_upd hs rfl
  | conflict i o _ _ => exact finsupp_of_upd hs rfl
  | crash i _ => exact finsupp_of_upd (t := s.crash i) hs rfl
  | zombieLands o _ _ => exact finsupp_of_same hs rfl
  | sourceChanges => exact finsupp_of_same hs rfl
  | foreignWrite => exact finsupp_of_same hs rfl
  | deploy => exact finsupp_of_same hs rfl

theorem finsupp_reachable {s : World} (h : Reachable s) : FinSupp s := by
  induction h with
  | init => exact ⟨0, fun _ _ => rfl⟩
  | step _ hst ih => exact finsupp_step ih hst

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
      | skip v wr l =>
        refine key (s.prepare i) (.prepare s i hph)
          (by simp only [World.prepare, hnext]; exact ⟨_, rfl⟩) ?_
        simp only [World.prepare, hnext]
        unfold rank
        simp only [upd_same, hph]
        split <;> omega
      | write m v wr l =>
        refine key (s.prepare i) (.prepare s i hph)
          (by simp only [World.prepare, hnext]; exact ⟨_, rfl⟩) ?_
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

/-- The sink's record is the newest commit, of the deployed plan and of the
source's contents, and every process rests or is about to prepare, under the
deployed plan, having read the source as it is. -/
def Conv (s : World) : Prop :=
  kept s.log = true ∧ (∃ r, record s.log = some r ∧ r.plan = s.deployed ∧ r.dig = s.src) ∧
    ∀ i, (s.ws i).phase = .down ∨
      ((s.ws i).phase = .idle ∧ (s.ws i).plan = s.deployed) ∨
      ((s.ws i).phase = .ready ∧ (s.ws i).plan = s.deployed ∧ (s.ws i).c = s.src)

theorem next_same {r : Key} {w : Writer} (hp : r.plan = w.plan) (hd : r.dig = w.c) :
    ∃ v wr l, next (some r) true w = .skip v wr l := by
  refine ⟨r.ver, Key.tbl ⟨w.plan, 0, w.c⟩, some r, ?_⟩
  simp [next, sameOf, hp, hd]

theorem conv_of_upd {s t : World} {i : Nat} {w : Writer} (hc : Conv s)
    (hlog : t.log = s.log) (hsrc : t.src = s.src) (hdep : t.deployed = s.deployed)
    (hws : t.ws = upd s.ws i w)
    (hw : w.phase = .down ∨ (w.phase = .idle ∧ w.plan = s.deployed) ∨
      (w.phase = .ready ∧ w.plan = s.deployed ∧ w.c = s.src)) : Conv t := by
  obtain ⟨hk, ⟨r, hrec, hrp, hrv⟩, hall⟩ := hc
  refine ⟨by rw [hlog]; exact hk, ⟨r, by rw [hlog]; exact hrec, by rw [hdep]; exact hrp,
    by rw [hsrc]; exact hrv⟩, fun j => ?_⟩
  rw [hws, hdep, hsrc]
  by_cases hji : j = i
  · subst hji; rw [upd_same]; exact hw
  · rw [upd_other _ _ hji]; exact hall j

theorem conv_step {s t : World} (hc : Conv s) (h : PStep s t) : Conv t := by
  obtain ⟨hk, ⟨r, hrec, hrp, hrv⟩, hall⟩ := hc
  have hc : Conv s := ⟨hk, ⟨r, hrec, hrp, hrv⟩, hall⟩
  cases h with
  | start i _ => exact conv_of_upd hc rfl rfl rfl rfl (Or.inr (Or.inl ⟨rfl, rfl⟩))
  | stop i _ _ => exact conv_of_upd hc rfl rfl rfl rfl (Or.inl rfl)
  | refresh i hi =>
    rcases hall i with h | ⟨_, hp⟩ | ⟨h, _⟩
    · rw [h] at hi; cases hi
    · exact conv_of_upd hc rfl rfl rfl rfl (Or.inr (Or.inr ⟨rfl, hp, rfl⟩))
    · rw [h] at hi; cases hi
  | prepare i hi =>
    rcases hall i with h | ⟨h, _⟩ | ⟨_, hp, hcs⟩
    · rw [h] at hi; cases hi
    · rw [h] at hi; cases hi
    · obtain ⟨v, wr, l, hnext⟩ := next_same (r := r) (w := s.ws i) (by rw [hrp, hp])
        (by rw [hrv, hcs])
      have hn : next (record s.log) (kept s.log) (s.ws i) = .skip v wr l := by
        rw [hrec, hk]; exact hnext
      simp only [World.prepare, hn]
      exact conv_of_upd hc rfl rfl rfl rfl (Or.inr (Or.inl ⟨rfl, hp⟩))
  | land i o hw _ =>
    rcases hall i with h | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hw <;> cases hw
  | conflict i o hw _ =>
    rcases hall i with h | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hw <;> cases hw

theorem conv_reach {s t : World} (hr : Reachable s) (hc : Conv s) (h : PReach s t) : Conv t := by
  induction h with
  | refl => exact hc
  | step hst _ ih => exact ih (hr.step hst.step) (conv_step hc hst)


/-- A skip is on a record of the writer's plan: of its contents, or at a version
not below its own. -/
theorem next_skip_facts {rec : Option Key} {k : Bool} {w : Writer} {v : Nat} {wr : Tbl}
    {l : Option Key} (h : next rec k w = .skip v wr l) :
    ∃ r, rec = some r ∧ k = true ∧ r.plan = w.plan ∧
      (r.dig = w.c ∨ (r.dig ≠ w.c ∧ w.ver ≤ r.ver)) := by
  cases rec with
  | none => simp only [next] at h; split at h <;> cases h
  | some r =>
    simp only [next] at h
    split at h
    · next hs =>
      obtain ⟨h1, h2, h3⟩ := sameOf_iff.mp hs
      exact ⟨r, rfl, h2, h1, Or.inl h3⟩
    · next hs =>
      split at h
      · next hs2 =>
        have hs2' := hs2
        simp only [skip2Of, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
          beq_iff_eq] at hs2'
        obtain ⟨⟨⟨hp, hk⟩, hc⟩, hv⟩ := hs2'
        refine ⟨r, rfl, hk, hp, Or.inr ⟨fun hd => hs (sameOf_iff.mpr ⟨hp, hk, hd⟩), ?_⟩⟩
        simpa [verOf, hc] using hv
      · cases h

/-- One process, started after the others have come to rest, brings the sink to
the deployed plan's state of the source. -/
theorem fresh {s : World} (N : Nat) (hq : Quiescent s)
    (hN : ∀ i, N ≤ i → (s.ws i).phase = .down) : ∃ t, PReach s t ∧ Conv t := by
  have h1 : PStep s (s.start N) := .start s N (hN N (Nat.le_refl _))
  have hw1 : (s.start N).ws N = { phase := .idle, plan := s.deployed } := by
    simp [World.start, upd_same]
  have h2 : PStep (s.start N) ((s.start N).refresh N) := .refresh _ N (by rw [hw1])
  have hw2 : (((s.start N).refresh N).ws N).phase = .ready ∧
      (((s.start N).refresh N).ws N).plan = s.deployed ∧
      (((s.start N).refresh N).ws N).c = s.src ∧
      (((s.start N).refresh N).ws N).ver =
        (match record s.log with
          | some r => if r.dig == s.src then r.ver else r.ver + 1
          | none => 1) :=
    ⟨by simp [World.refresh, World.refreshW, upd_same, hw1],
     by simp [World.refresh, World.refreshW, upd_same, hw1],
     by simp [World.refresh, World.refreshW, upd_same, hw1] <;> rfl,
     by simp [World.refresh, World.refreshW, upd_same, hw1] <;> rfl⟩
  have h3 : PStep ((s.start N).refresh N) (((s.start N).refresh N).prepare N) :=
    .prepare _ N hw2.1
  cases hn : next (record ((s.start N).refresh N).log) (kept ((s.start N).refresh N).log)
      (((s.start N).refresh N).ws N) with
  | skip v wr l =>
    obtain ⟨r, hrec, hkt, hrp, hdisj⟩ := next_skip_facts hn
    have hrec : record s.log = some r := hrec
    have hkt : kept s.log = true := hkt
    have hdig : r.dig = s.src := by
      rcases hdisj with hd | ⟨hd, hv⟩
      · rw [hd, hw2.2.2.1]
      · exfalso
        rw [hw2.2.2.2, hrec] at hv
        have : (r.dig == s.src) = false := by
          simpa using (fun h => hd (h.trans hw2.2.2.1.symm))
        simp [this] at hv
        omega
    refine ⟨_, .step h1 (.step h2 (.step h3 (.refl _))), ?_⟩
    simp only [World.prepare, hn]
    refine ⟨hkt, ⟨r, hrec, hrp.trans hw2.2.1, hdig⟩, fun j => ?_⟩
    by_cases hj : j = N
    · subst hj
      right; left
      simp [upd_same, hw2.2.1] <;> rfl
    · simp only [World.start, World.refresh] at *
      rw [upd_other _ _ hj, upd_other _ _ hj, upd_other _ _ hj]
      rcases hq j with h | ⟨h, hp⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h, hp⟩)
  | write m v wr l =>
    let o : Out := ⟨⟨(((s.start N).refresh N).ws N).plan, v, (((s.start N).refresh N).ws N).c⟩,
      m, wr, ((s.start N).refresh N).log.length⟩
    have hph : ((((s.start N).refresh N).prepare N).ws N).phase = .writing o := by
      simp only [World.prepare, hn]
      simp [upd_same, o]
    have h4 : PStep (((s.start N).refresh N).prepare N)
        { (((s.start N).refresh N).prepare N).commit o with
          ws := upd (((s.start N).refresh N).prepare N).ws N
            { (((s.start N).refresh N).prepare N).ws N with
              phase := .idle, written := o.key.tbl, last := some o.key, pend := none } } :=
      .land _ N o hph (by simp only [World.prepare, hn, o])
    refine ⟨_, .step h1 (.step h2 (.step h3 (.step h4 (.refl _)))), ?_⟩
    refine ⟨rfl, ⟨o.key, ?_, ?_, ?_⟩, fun j => ?_⟩
    · exact record_cons rfl
    · simp only [World.prepare, hn, o]; exact hw2.2.1
    · simp only [World.prepare, hn, o]; exact hw2.2.2.1
    · by_cases hj : j = N
      · subst hj
        right; left
        simp [upd_same, World.prepare, hn] <;> first | rfl | exact hw2.2.1
      · simp only [World.prepare, hn, World.start, World.refresh, World.commit] at *
        rw [upd_other _ _ hj, upd_other _ _ hj, upd_other _ _ hj, upd_other _ _ hj]
        rcases hq j with h | ⟨h, hp⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h, hp⟩)

end RefreshSnap

open RefreshSnap

/-- No reachable state has a change applied to a table it was not computed
from (#933, invariants 2 and 4), for a source that cannot restore. -/
theorem RefreshSnap.no_corruption {s : World} (h : Reachable s) : s.tbl ≠ .corrupt := by
  have ht := (inv_reachable h).1
  unfold TblOK at ht
  split at ht
  · rw [ht]; simp
  · split at ht <;> rw [ht] <;> simp [Key.tbl]

/-- When the node's commit is the newest, the table is the state it records:
the plan and the digest of the contents (#933, invariant 4). -/
theorem RefreshSnap.record_describes_table {s : World} (h : Reachable s)
    (hk : kept s.log = true) : ∃ r, record s.log = some r ∧ s.tbl = r.tbl := by
  obtain ⟨c, rest, hlog, happ, hrc⟩ := record_of_kept hk
  have ht := (inv_reachable h).1
  unfold TblOK at ht
  rw [hlog] at ht
  simp only [happ, ↓reduceIte] at ht
  exact ⟨c.key, hrc, ht⟩

/-- A change that lands applies to the newest commit of the node, which is
the sink's record, and was computed against its table (#933, invariant 3). -/
theorem RefreshSnap.read_is_head {s : World} {o : Out} (h : Reachable s) (hp : Pending s o)
    (hm : o.mode = .merge) (hc : s.log.length = o.head) :
    kept s.log = true ∧ ∃ r, record s.log = some r ∧ o.base = r.tbl :=
  ((inv2_reachable h).2 o hp hc).2 hm

/-- Under one plan, adjacent commits of the node are of versions that do not go
down and of other contents: no state is committed twice in a row (#933,
invariants 1 and 5, and #889's `NoRewriteUnchanged`). -/
theorem RefreshSnap.monotone {s : World} (h : Reachable s) : AdjOK s.log :=
  (inv2_reachable h).1

/-- Whenever a process prepares, if the record is still the one its first
refresh could resume from and no other application wrote since, it does not
write the whole table again (#889: `NoNeedlessRewrite`). -/
theorem RefreshSnap.no_needless_rewrite {s : World} (h : Reachable s) {i : Nat} {r : Key}
    (hph : (s.ws i).phase = .ready) (hres : (s.ws i).resumable = some r)
    (hrec : record s.log = some r) (hk : kept s.log = true) (v : Nat) (wr : Tbl)
    (l : Option Key) :
    next (record s.log) (kept s.log) (s.ws i) ≠ .write .replace v wr l := by
  obtain ⟨hw, hl, hp, hv, hd⟩ := resok_reachable h i r hph hres
  rw [hrec, hk]
  exact next_resumes hp hl hw hv hd v wr l

/-- From every reachable state with no write of a crashed process in flight, the
processes' own steps, with no source change, deploy, foreign commit, crash or
lost acknowledgement, bring the sink's table to the deployed plan's state of
the source, and every further process step leaves it there (#933: the safety
half of `Converges`, for a source that cannot restore). -/
theorem RefreshSnap.quiet {s : World} (h : Reachable s) (hz : s.zombies = []) :
    ∃ t, PReach s t ∧ ∀ t', PReach t t' → t'.tbl = .rows s.deployed s.src := by
  obtain ⟨N, hN⟩ := finsupp_reachable h
  obtain ⟨d, hd, hdr, hdz, hdN, hdq⟩ := drain N _ s rfl h hz hN
  obtain ⟨t, ht, hc⟩ := fresh N hdq hdN
  refine ⟨t, hd.trans ht, fun t' ht' => ?_⟩
  have hrt := ht.reachable hdr
  have hrt' := ht'.reachable hrt
  have hc' := conv_reach hrt hc ht'
  obtain ⟨hk, ⟨r, hrec, hrp, hrd⟩, _⟩ := hc'
  obtain ⟨r', hr', htbl⟩ := RefreshSnap.record_describes_table hrt' hk
  rw [hrec] at hr'
  simp only [Option.some.injEq] at hr'
  subst hr'
  obtain ⟨e1, e2, _⟩ := ((hd.trans ht).trans ht').env
  rw [htbl]
  simp [Key.tbl, hrp, hrd, e1, e2]

end Substrait
