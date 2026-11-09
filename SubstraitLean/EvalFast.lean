import Sverify.Core.Rel
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# A fast evaluator, proved equal to `Rel.eval` (#357)

`Rel.eval` is the specification, written for proofs: an inner join is a
filter of the cross product, a left join and a semi-join test the whole
right side for every left row, and `DISTINCT` and `GROUP BY` compare every
row with every other. All of them take time quadratic in the data.

`Rel.evalFast` computes the same list of rows (`Rel.evalFast_eq`), in the
same order, faster:

* An equi-join (`on` a conjunction with `a = b` or `a IS NOT DISTINCT FROM b`,
  `a` reading only left columns and `b` only right ones) hashes the right
  side by its keys once.
  Each left row then tests `on` only on the right rows with its keys, in
  their order on the right, so the output keeps the nested loop's left-major
  order. A left row with a NULL in an `=` key matches nothing; a row of another length
  than the left side's arity, or a join without such keys, falls back to the
  whole right side.
* `DISTINCT`, `fn(DISTINCT …)` and the groups of `GROUP BY` find each
  class's least member with a hash map and keep a hash set of what they
  have seen (`canonRepsH`), and `GROUP BY` collects each group's rows in a
  hash map, both in order of first occurrence.

The executables evaluate data with it (`substrait-check` with inlined data,
and through it the oracle tests and DuckDB's sqllogictest replay).
-/

namespace Substrait
variable [Boxes.Ambient]

/-! ## Hashing values -/

mutual
def Value.hashV : Value → UInt64
  | .null => 11
  | .bool b => mixHash 13 (hash b)
  | .int i => mixHash 17 (hash i)
  | .float c => mixHash 31 (hash c)
  | .date d => mixHash 37 (hash d)
  | .ts t => mixHash 41 (hash t)
  | .tod t => mixHash 43 (hash t)
  | .dec s i => mixHash 47 (mixHash (hash s) (hash i))
  | .str s => mixHash 19 (hash s)
  | .list vs => mixHash 23 (Value.hashList vs)
  | .struct vs => mixHash 53 (Value.hashList vs)

def Value.hashList : List Value → UInt64
  | [] => 29
  | v :: vs => mixHash (Value.hashV v) (Value.hashList vs)
end

instance : Hashable Value := ⟨Value.hashV⟩

/-! ## Distinct elements with a hash set -/

section Dedup

variable {α : Type} [DecidableEq α] [Hashable α]

/-- `dedup` with a hash set of the elements seen so far. -/
def dedupH.go : List α → Std.HashSet α → Array α → Array α
  | [], _, acc => acc
  | x :: xs, seen, acc =>
    if seen.contains x then go xs seen acc else go xs (seen.insert x) (acc.push x)

def dedupH (l : List α) : List α := (dedupH.go l ∅ #[]).toList

omit [Boxes.Ambient] in
theorem dedupH.go_eq : ∀ (l : List α) (seen : Std.HashSet α) (acc : Array α),
    (dedupH.go l seen acc).toList = acc.toList ++ dedup (l.filter fun y => !seen.contains y)
  | [], _, _ => by simp [dedupH.go, dedup, dedupN]
  | x :: xs, seen, acc => by
    by_cases hx : seen.contains x
    · simp [dedupH.go, hx, dedupH.go_eq xs seen acc]
    · simp only [dedupH.go, hx, Bool.false_eq_true, ↓reduceIte, dedupH.go_eq xs _ _,
        List.filter_cons, Bool.not_false, Array.toList_push, List.append_assoc,
        List.singleton_append, dedup_cons, List.filter_filter]
      congr 3
      apply List.filter_congr
      intro y _
      simp only [Std.HashSet.contains_insert, Bool.not_or]
      by_cases h : x = y
      · subst h; simp
      · have h1 : (x == y) = false := beq_false_of_ne h
        have h2 : (y != x) = true := bne_iff_ne.mpr fun e => h e.symm
        simp only [h1, h2, Bool.not_false, Bool.true_and]

omit [Boxes.Ambient] in
theorem dedupH_eq (l : List α) : dedupH l = dedup l := by
  have : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)
  simp [dedupH, dedupH.go_eq, this]

/-! ## Class representatives with a hash map -/

variable {c : α → α} {le : α → α → Bool}

/-- One step of `leastBy`: `y` against the least member of its class so far. -/
def leastStep (c : α → α) (le : α → α → Bool) (m : Std.HashMap α α) (y : α) : Std.HashMap α α :=
  m.insert (c y) (match m[c y]? with | some z => if le z y then z else y | none => y)

/-- The least member of each class of `l`, by its canonical form. -/
def leastBy (c : α → α) (le : α → α → Bool) (l : List α) : Std.HashMap α α :=
  l.foldl (leastStep c le) ∅

/-- What `leastBy` keeps of the members `s` seen so far: for each class with
a member, its least member. -/
def LeastInv (c : α → α) (le : α → α → Bool) (m : Std.HashMap α α) (s : List α) : Prop :=
  ∀ k, (m[k]? = none → ∀ y ∈ s, c y ≠ k) ∧
    ∀ z, m[k]? = some z → z ∈ s ∧ c z = k ∧ ∀ y ∈ s, c y = k → le z y = true

theorem LeastInv.step (h : RawOrder le) {m : Std.HashMap α α} {s : List α}
    (hm : LeastInv c le m s) (y : α) : LeastInv c le (leastStep c le m y) (s ++ [y]) := by
  have hrefl : ∀ a, le a a = true := fun a => (h.total a a).elim id id
  intro k
  simp only [leastStep, Std.HashMap.getElem?_insert]
  by_cases hk : c y = k
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte, reduceCtorEq, false_implies, Option.some.injEq,
      true_and]
    intro z hz
    cases hmy : m[c y]? with
    | none =>
      rw [hmy] at hz; simp only at hz; subst hz
      refine ⟨List.mem_append_right _ List.mem_cons_self, rfl, fun w hw hcw => ?_⟩
      rcases List.mem_append.mp hw with hw | hw
      · exact absurd hcw ((hm _).1 hmy w hw)
      · rw [List.mem_singleton.mp hw]; exact hrefl _
    | some z' =>
      rw [hmy] at hz; simp only at hz
      obtain ⟨hz's, hcz', hlz'⟩ := (hm _).2 z' hmy
      split at hz
      · rename_i hle; subst hz
        refine ⟨List.mem_append_left _ hz's, hcz', fun w hw hcw => ?_⟩
        rcases List.mem_append.mp hw with hw | hw
        · exact hlz' w hw hcw
        · rw [List.mem_singleton.mp hw]; exact hle
      · rename_i hle; subst hz
        have hyz : le y z' = true := (h.total z' y).resolve_left hle
        refine ⟨List.mem_append_right _ List.mem_cons_self, rfl, fun w hw hcw => ?_⟩
        rcases List.mem_append.mp hw with hw | hw
        · exact h.trans _ _ _ hyz (hlz' w hw hcw)
        · rw [List.mem_singleton.mp hw]; exact hrefl _
  · have hb : (c y == k) = false := by simpa using hk
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun hn w hw => ?_, fun z hz => ?_⟩
    · rcases List.mem_append.mp hw with hw | hw
      · exact (hm k).1 hn w hw
      · rw [List.mem_singleton.mp hw]; exact hk
    · obtain ⟨hzs, hcz, hl⟩ := (hm k).2 z hz
      refine ⟨List.mem_append_left _ hzs, hcz, fun w hw hcw => ?_⟩
      rcases List.mem_append.mp hw with hw | hw
      · exact hl w hw hcw
      · rw [List.mem_singleton.mp hw] at hcw; exact absurd hcw hk

theorem LeastInv.foldl (h : RawOrder le) : ∀ (r : List α) {m : Std.HashMap α α} {s : List α},
    LeastInv c le m s → LeastInv c le (r.foldl (leastStep c le) m) (s ++ r)
  | [], _, _, hm => by simpa using hm
  | y :: r, _, s, hm => by
    have := LeastInv.foldl h r (hm.step h y)
    simpa [List.foldl_cons, List.append_assoc] using this

/-- `leastBy` gives each member's `classRep`. -/
theorem leastBy_getD (h : RawOrder le) {l : List α} {x : α} (hx : x ∈ l) :
    (leastBy c le l).getD (c x) x = classRep c le l x := by
  have hinv : LeastInv c le (leastBy c le l) l := by
    have := LeastInv.foldl (c := c) h l (m := ∅) (s := []) fun k =>
      ⟨fun _ _ hy => (nomatch hy), fun z hz => by simp at hz⟩
    simpa [leastBy] using this
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases hm : (leastBy c le l)[c x]? with
  | none => exact absurd rfl ((hinv (c x)).1 hm x hx)
  | some z =>
    obtain ⟨hzl, hcz, hlz⟩ := (hinv (c x)).2 z hm
    exact (classRep_eq_of_least h hx hzl hcz hlz).symm

/-- `canonReps` with a hash map of each class's least member and a hash set
of the representatives seen: linear where `canonReps` is quadratic. -/
def canonRepsH (c : α → α) (le : α → α → Bool) (l : List α) : List α :=
  let m := leastBy c le l
  dedupH (l.map fun x => m.getD (c x) x)

theorem canonRepsH_eq (h : RawOrder le) (l : List α) : canonRepsH c le l = canonReps c le l := by
  simp only [canonRepsH, dedupH_eq, canonReps]
  congr 1
  exact List.map_congr_left fun x hx => leastBy_getD h hx

end Dedup

section Generic

variable {α β : Type} [BEq α] [LawfulBEq α] [Hashable α]

/-! ## Indexing a list by a key -/

/-- The elements of `ys` by their key, each key's in list order. -/
def indexBy (key : β → α) (ys : List β) : Std.HashMap α (Array β) :=
  ys.foldl (fun m y => let k := key y; m.insert k ((m.getD k #[]).push y)) ∅

omit [Boxes.Ambient] in
theorem indexBy_foldl (key : β → α) (k : α) : ∀ (ys : List β) (m : Std.HashMap α (Array β)),
    ((ys.foldl (fun m y => let k := key y; m.insert k ((m.getD k #[]).push y)) m).getD k #[]).toList =
      (m.getD k #[]).toList ++ ys.filter (key · == k)
  | [], _ => by simp
  | y :: ys, m => by
    simp only [List.foldl_cons, indexBy_foldl key k ys, Std.HashMap.getD_insert, List.filter_cons]
    by_cases h : key y = k
    · subst h; simp
    · simp [h]

omit [Boxes.Ambient] in
theorem indexBy_getD (key : β → α) (ys : List β) (k : α) :
    ((indexBy key ys).getD k #[]).toList = ys.filter (key · == k) := by
  simp [indexBy, indexBy_foldl]

omit [Boxes.Ambient] in
/-- Filtering out, before a map, elements that fail the later filter anyway. -/
theorem filter_map_filter {γ : Type} {q : β → Bool} {f : β → γ} {p : γ → Bool} (ys : List β)
    (h : ∀ y ∈ ys, p (f y) = true → q y = true) :
    ((ys.filter q).map f).filter p = (ys.map f).filter p := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    have ih := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hq : q y
    · simp [List.filter_cons, hq, ih]
    · have : p (f y) = false := by
        cases hp : p (f y)
        · rfl
        · exact absurd (h y List.mem_cons_self hp) (by simp [hq])
      simp [hq, this, ih]

omit [Boxes.Ambient] in
theorem any_filter_of {q g : β → Bool} (ys : List β) (h : ∀ y ∈ ys, g y = true → q y = true) :
    (ys.filter q).any g = ys.any g := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    have ih := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hq : q y
    · simp [hq, ih]
    · have : g y = false := by
        cases hg : g y
        · rfl
        · exact absurd (h y List.mem_cons_self hg) (by simp [hq])
      simp [hq, this, ih]

end Generic

/-! ## Equi-join keys -/

/-- The expression on the columns after the first `n` of the row, if it reads
only those; the `k` fields in front are lambda parameters (D28), kept. -/
def Expr.dropColsAt (k n : Nat) : Expr → Option Expr
  | .lit v => some (.lit v)
  | .field i => if i < k then some (.field i) else if k + n ≤ i then some (.field (i - n)) else none
  | .un f a => match a.dropColsAt k n with
    | some a' => some (.un f a')
    | none => none
  | .bin f a b => match a.dropColsAt k n, b.dropColsAt k n with
    | some a', some b' => some (.bin f a' b')
    | _, _ => none
  | .ifThen c t e => match c.dropColsAt k n, t.dropColsAt k n, e.dropColsAt k n with
    | some c', some t', some e' => some (.ifThen c' t' e')
    | _, _, _ => none
  | .hof f l body => match l.dropColsAt k n, body.dropColsAt (k + 1) n with
    | some l', some body' => some (.hof f l' body')
    | _, _ => none

/-- The expression on the columns after the first `n`, if it reads only those. -/
def Expr.dropCols (n : Nat) : Expr → Option Expr := Expr.dropColsAt 0 n

theorem Expr.eval_dropColsAt {x y : Row} : ∀ {e e' : Expr} (ps : Row),
    e.dropColsAt ps.length x.length = some e' → e.eval (ps ++ (x ++ y)) = e'.eval (ps ++ y)
  | .lit _, e', _, h => by simp only [dropColsAt, Option.some.injEq] at h; subst h; rfl
  | .field i, e', ps, h => by
    simp only [dropColsAt] at h
    split at h
    · rename_i hi
      simp only [Option.some.injEq] at h; subst h
      simp [eval, List.getD, List.getElem?_append_left hi]
    · split at h
      · rename_i hi hk
        simp only [Option.some.injEq] at h; subst h
        simp only [eval, List.getD]
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
          List.getElem?_append_right (by omega)]
        congr 2; omega
      · simp at h
  | .un f a, e', ps, h => by
    simp only [dropColsAt] at h
    split at h
    · rename_i a' ha; simp only [Option.some.injEq] at h; subst h
      simp [eval, eval_dropColsAt ps ha]
    · simp at h
  | .bin f a b, e', ps, h => by
    simp only [dropColsAt] at h
    split at h
    · rename_i a' b' ha hb; simp only [Option.some.injEq] at h; subst h
      simp [eval, eval_dropColsAt ps ha, eval_dropColsAt ps hb]
    · simp at h
  | .ifThen c t el, e', ps, h => by
    simp only [dropColsAt] at h
    split at h
    · rename_i c' t' e'' hc ht he; simp only [Option.some.injEq] at h; subst h
      simp [eval, eval_dropColsAt ps hc, eval_dropColsAt ps ht, eval_dropColsAt ps he]
    · simp at h
  | .hof f l body, e', ps, h => by
    simp only [dropColsAt] at h
    split at h
    · rename_i l' body' hl hb; simp only [Option.some.injEq] at h; subst h
      simp only [eval, eval_dropColsAt ps hl]
      congr 1; funext v
      exact eval_dropColsAt (v :: ps) hb
    · simp at h

theorem Expr.eval_dropCols {x y : Row} {e e' : Expr} (h : e.dropCols x.length = some e') :
    e.eval (x ++ y) = e'.eval y :=
  Expr.eval_dropColsAt (x := x) (y := y) [] h

theorem Expr.eval_append_of_refsLtB {x : Row} (y : Row) {e : Expr} (h : e.refsLtB x.length = true) :
    e.eval (x ++ y) = e.eval x :=
  Expr.eval_append y (Expr.refsLtB_iff.mp h) rfl

/-- A join key: `left` on the left row equals `right` on the right row
wherever the condition holds, and is not NULL there if `strict`. -/
structure EqKey where
  left : Expr
  right : Expr
  strict : Bool

/-- `a` on the left row (its first `la` columns) and `b` on the right row. -/
def eqKey (la : Nat) (a b : Expr) : Option (Expr × Expr) :=
  if a.refsLtB la then (b.dropCols la).map (a, ·) else none

/-- The key of `a = b` (`strict`) or `a IS NOT DISTINCT FROM b`, either way
round. -/
def pairKey (la : Nat) (strict : Bool) (a b : Expr) : List EqKey :=
  match eqKey la a b, eqKey la b a with
  | some (l, r), _ => [⟨l, r, strict⟩]
  | none, some (l, r) => [⟨l, r, strict⟩]
  | none, none => []

/-- The key of one conjunct: `a = b`, or `a IS NOT DISTINCT FROM b` as the
parser writes it (`Parse.mkCoreCall?.notDistinct`), which `EXCEPT` and
`INTERSECT` join on. -/
def leafKeys (la : Nat) : Expr → List EqKey
  | .bin .eq a b => pairKey la true a b
  | .ifThen (.un .isNull a) (.un .isNull b)
      (.ifThen (.un .isNull b') (.lit (.bool false)) (.bin .eq a' b'')) =>
    if a' = a ∧ b' = b ∧ b'' = b then pairKey la false a b else []
  | _ => []

/-- The keys of the conjuncts of `on` that compare the two sides. -/
def equiKeys (la : Nat) : Expr → List EqKey
  | .bin .and a b => equiKeys la a ++ equiKeys la b
  | e => leafKeys la e

omit [Boxes.Ambient] in
@[simp] theorem Value.isTrue_bool (c : Bool) : (Value.bool c).isTrue = c := by cases c <;> rfl
omit [Boxes.Ambient] in
@[simp] theorem Value.isTrue_null : Value.null.isTrue = false := rfl

/-- Values `=` calls equal have one canonical form (`-0.0 = 0.0`, D31). -/
theorem isTrue_eq {a b : Value} (h : (BinFn.apply .eq a b).isTrue = true) :
    a.canonV = b.canonV ∧ a ≠ .null := by
  cases a <;> cases b <;> simp_all [BinFn.apply, Value.canonV]
  all_goals (rename_i s _ t _; by_cases hs : s = t <;> simp_all)

theorem eval_notDistinct {row : Row} {a b : Expr}
    (h : ((Expr.ifThen (.un .isNull a) (.un .isNull b)
      (.ifThen (.un .isNull b) (.lit (.bool false)) (.bin .eq a b))).eval row).isTrue = true) :
    (a.eval row).canonV = (b.eval row).canonV := by
  cases ha : a.eval row <;> cases hb : b.eval row <;>
    simp_all [Expr.eval, UnFn.apply, BinFn.apply, Value.canonV]
  all_goals (rename_i s _ t _; by_cases hs : s = t <;> simp_all)

theorem eqKey_sound {x y : Row} {a b : Expr} {l r : Expr} (hk : eqKey x.length a b = some (l, r)) :
    l.eval x = a.eval (x ++ y) ∧ r.eval y = b.eval (x ++ y) := by
  unfold eqKey at hk
  split at hk
  · rename_i ha
    cases hb : b.dropCols x.length with
    | none => simp [hb] at hk
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨(Expr.eval_append_of_refsLtB y ha).symm, (Expr.eval_dropCols hb).symm⟩
  · simp at hk

/-- What a key promises where the condition holds on `x ++ y`. -/
def EqKey.Holds (x y : Row) (k : EqKey) : Prop :=
  (k.left.eval x).canonV = (k.right.eval y).canonV ∧ (k.strict = true → k.left.eval x ≠ .null)

theorem Value.canonV_null {v : Value} : v.canonV = .null ↔ v = .null := by
  cases v <;> simp [Value.canonV]

theorem pairKey_sound {x y : Row} {strict : Bool} {a b : Expr}
    (hab : (a.eval (x ++ y)).canonV = (b.eval (x ++ y)).canonV)
    (hn : strict = true → a.eval (x ++ y) ≠ .null) :
    ∀ k ∈ pairKey x.length strict a b, k.Holds x y := by
  intro k hk
  unfold pairKey at hk
  split at hk
  · rename_i l r hk'
    simp only [List.mem_singleton] at hk; subst hk
    obtain ⟨hl, hr⟩ := eqKey_sound (y := y) hk'
    exact ⟨by rw [hl, hr, hab], fun hs => by rw [hl]; exact hn hs⟩
  · rename_i l r _ hk'
    simp only [List.mem_singleton] at hk; subst hk
    obtain ⟨hl, hr⟩ := eqKey_sound (y := y) hk'
    refine ⟨by rw [hl, hr, hab], fun hs => ?_⟩
    rw [hl]; intro h0
    exact hn hs (Value.canonV_null.mp (hab ▸ Value.canonV_null.mpr h0))
  · simp at hk

theorem leafKeys_sound {x y : Row} {e : Expr} (h : (e.eval (x ++ y)).isTrue = true) :
    ∀ k ∈ leafKeys x.length e, k.Holds x y := by
  intro k hk
  unfold leafKeys at hk
  split at hk
  · obtain ⟨hab, hn⟩ := isTrue_eq h
    exact pairKey_sound hab (fun _ => hn) k hk
  · split at hk
    · rename_i a b b' a' b'' hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      have hab := eval_notDistinct h
      exact pairKey_sound hab (fun h => by simp at h) k hk
    · simp at hk
  · simp at hk

/-- Where `on` holds on `x ++ y`, with `x` of length `la`, every key holds. -/
theorem equiKeys_sound {x y : Row} {on : Expr} (h : (on.eval (x ++ y)).isTrue = true) :
    ∀ k ∈ equiKeys x.length on, k.Holds x y := by
  induction on with
  | bin f a b iha ihb =>
    cases f
    case and =>
      intro k hk
      simp only [Expr.eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at h
      simp only [equiKeys, List.mem_append] at hk
      rcases hk with hk | hk
      · exact iha h.1 k hk
      · exact ihb h.2 k hk
    all_goals exact fun k hk => leafKeys_sound h k (by simpa [equiKeys] using hk)
  | _ => exact fun k hk => leafKeys_sound h k (by simpa [equiKeys] using hk)

/-! ## Joins -/

/-- The right side of a join, hashed by the right halves of its keys. -/
structure JoinIndex where
  keys : List EqKey
  la : Nat
  rows : Relation
  index : Std.HashMap Row (Array Row)

def JoinIndex.make (on : Expr) (la : Nat) (ys : Relation) : JoinIndex :=
  let keys := equiKeys la on
  { keys, la, rows := ys,
    index := if keys.isEmpty then ∅ else indexBy (fun y => keys.map (·.right.eval y |>.canonV)) ys }

/-- The right rows that may satisfy `on` next to `x`: those with `x`'s keys,
none for a NULL in a strict key, and all of them without keys. -/
def JoinIndex.candidates (J : JoinIndex) (x : Row) : Relation :=
  if J.keys.isEmpty || x.length != J.la then J.rows else
    if J.keys.any (fun k => k.strict && k.left.eval x == .null) then [] else
      (J.index.getD (J.keys.map (·.left.eval x |>.canonV)) #[]).toList

theorem JoinIndex.candidates_eq (on : Expr) (la : Nat) (ys : Relation) (x : Row) :
    ∃ q : Row → Bool, (JoinIndex.make on la ys).candidates x = ys.filter q ∧
      ∀ y, (on.eval (x ++ y)).isTrue = true → q y = true := by
  unfold candidates make
  dsimp only
  by_cases hc : ((equiKeys la on).isEmpty || x.length != la) = true
  · rw [ite_eq_left hc]
    exact ⟨fun _ => true, (List.filter_eq_self.mpr fun _ _ => rfl).symm, fun _ _ => rfl⟩
  rw [ite_eq_right hc]
  simp only [Bool.or_eq_true, not_or] at hc
  have hne : (equiKeys la on).isEmpty = false := by simpa using hc.1
  have hlen : x.length = la := by simpa using hc.2
  subst hlen
  have hsound := fun y h => equiKeys_sound (x := x) (y := y) (on := on) h
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  by_cases hnull : (equiKeys x.length on).any (fun k => k.strict && k.left.eval x == .null) = true
  · simp only [hnull, ↓reduceIte]
    refine ⟨fun _ => false, by simp, fun y h => ?_⟩
    exfalso
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hnull
    obtain ⟨k, hk, hs, hkn⟩ := hnull
    exact (hsound y h k hk).2 hs hkn
  · simp only [hnull, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun y => (equiKeys x.length on).map (·.right.eval y |>.canonV) ==
        (equiKeys x.length on).map (·.left.eval x |>.canonV), indexBy_getD _ _ _, fun y h => ?_⟩
    simp only [beq_iff_eq, List.map_inj_left]
    exact fun k hk => (hsound y h k hk).1.symm

def innerJoinFast (on : Expr) (la : Nat) (xs ys : Relation) : Relation :=
  let J := JoinIndex.make on la ys
  xs.flatMap fun x => ((J.candidates x).map (x ++ ·)).filter fun row => (on.eval row).isTrue

def leftJoinFast (on : Expr) (la ra : Nat) (xs ys : Relation) : Relation :=
  let J := JoinIndex.make on la ys
  xs.flatMap fun x => leftJoinRow on ra (J.candidates x) x

def semiFast (on : Expr) (la : Nat) (anti : Bool) (xs ys : Relation) : Relation :=
  let J := JoinIndex.make on la ys
  xs.filter fun x => hasMatch on (J.candidates x) x != anti

theorem matches_candidates (on : Expr) (la : Nat) (ys : Relation) (x : Row) :
    (((JoinIndex.make on la ys).candidates x).map (x ++ ·)).filter (fun row => (on.eval row).isTrue)
      = (ys.map (x ++ ·)).filter fun row => (on.eval row).isTrue := by
  obtain ⟨q, hq, hsound⟩ := JoinIndex.candidates_eq on la ys x
  rw [hq]
  exact filter_map_filter ys fun y _ h => hsound y h

theorem innerJoinFast_eq (on : Expr) (la : Nat) (xs ys : Relation) :
    innerJoinFast on la xs ys = (crossRows xs ys).filter fun row => (on.eval row).isTrue := by
  simp only [innerJoinFast, crossRows, List.filter_flatMap, matches_candidates]

theorem leftJoinFast_eq (on : Expr) (la ra : Nat) (xs ys : Relation) :
    leftJoinFast on la ra xs ys = xs.flatMap (leftJoinRow on ra ys) := by
  simp only [leftJoinFast]
  congr 1
  funext x
  simp only [leftJoinRow, matches_candidates]

theorem semiFast_eq (on : Expr) (la : Nat) (anti : Bool) (xs ys : Relation) :
    semiFast on la anti xs ys = xs.filter fun x => hasMatch on ys x != anti := by
  simp only [semiFast]
  congr 1
  funext x
  obtain ⟨q, hq, hsound⟩ := JoinIndex.candidates_eq on la ys x
  simp only [hasMatch, hq, any_filter_of ys fun y _ h => hsound y h]

/-! ## Aggregation -/

def Measure.inputsFast (m : Measure) (rows : Relation) : List Value :=
  let vs := ((m.kept rows).map m.arg.eval).filter (· != .null)
  if m.distinct then canonRepsH Value.canonV Value.leRaw vs else vs

theorem Measure.inputsFast_eq (m : Measure) (rows : Relation) :
    m.inputsFast rows = m.inputs rows := by
  simp [inputsFast, inputs, canonRepsH_eq Value.leRaw_rawOrder, distinctVals]

def Measure.evalFast (rows : Relation) (m : Measure) : Value :=
  match m.fn with
  | .collect => AggFn.collect.apply (m.inputsFast (rows.mergeSort (sortLe m.sort)))
  | .pick last => (AggFn.pick last).apply (m.inputsFast (rows.mergeSort (sortLe m.sort)))
  | .concat sep => (AggFn.concat sep).apply (m.inputsFast (rows.mergeSort (sortLe m.sort)))
  | .mode => AggFn.mode.apply (m.inputsFast (rows.mergeSort (sortLe m.sort)))
  | f => f.apply (m.inputsFast rows)

theorem Measure.evalFast_eq (rows : Relation) (m : Measure) : m.evalFast rows = m.eval rows := by
  cases h : m.fn <;> simp [evalFast, eval, h, inputsFast_eq]

def aggregateFast (gs : List Expr) (ms : List Measure) (rows : Relation) : Relation :=
  if gs.isEmpty then [ms.map (·.evalFast rows)]
  else
    -- Groups are keyed up to canonical codes (D31).
    let idx := indexBy (fun row => (groupKey gs row).canon) rows
    (canonRepsH Row.canon Row.leRaw (rows.map (groupKey gs))).map fun k =>
      k ++ ms.map (·.evalFast (idx.getD k.canon #[]).toList)

theorem aggregateFast_eq (gs : List Expr) (ms : List Measure) (rows : Relation) :
    aggregateFast gs ms rows = aggregateEval gs ms rows := by
  unfold aggregateFast aggregateEval
  split
  · simp [Measure.evalFast_eq]
  · simp only [indexBy_getD, Measure.evalFast_eq, groupRows, canonRepsH_eq Row.leRaw_rawOrder,
      distinctRows]

/-! ## The evaluator -/

/-- `Rel.eval`, computed with hash joins and hash aggregation. -/
def Rel.evalFast (cat : Catalog) : Rel → Relation
  | .read t => (cat t).rows
  | .values _ rows => rows
  | .filter r c => (r.evalFast cat).filter fun row => (c.eval row).isTrue
  | .project r es => (r.evalFast cat).map fun row => row ++ es.map (·.eval row)
  | .emit r m => (r.evalFast cat).map fun row => m.map (row.getD · .null)
  | .cross a b => crossRows (a.evalFast cat) (b.evalFast cat)
  | .join a b .inner on => innerJoinFast on (a.arity cat) (a.evalFast cat) (b.evalFast cat)
  | .join a b .left on =>
      leftJoinFast on (a.arity cat) (b.arity cat) (a.evalFast cat) (b.evalFast cat)
  | .fetch r off cnt =>
      let rest := (r.evalFast cat).drop off
      match cnt with
      | none => rest
      | some n => rest.take n
  | .unionAll a b => a.evalFast cat ++ b.evalFast cat
  | .window r part sort fns => windowEval part sort fns (r.evalFast cat)
  | .semi a b anti on => semiFast on (a.arity cat) anti (a.evalFast cat) (b.evalFast cat)
  | .orderBy r keys => (r.evalFast cat).mergeSort (sortLe keys)
  | .distinct r => canonRepsH Row.canon Row.leRaw (r.evalFast cat)
  | .aggregate r gs ms => aggregateFast gs ms (r.evalFast cat)
  | .unnest r c => (r.evalFast cat).flatMap (unnestRow c)

theorem Rel.evalFast_eq (cat : Catalog) : ∀ r : Rel, r.evalFast cat = r.eval cat
  | .read _ | .values _ _ => rfl
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ | .unnest r _ | .window r _ _ _ => by
      simp [evalFast, eval, evalFast_eq cat r]
  | .fetch r _ cnt => by cases cnt <;> simp [evalFast, eval, evalFast_eq cat r]
  | .cross a b | .unionAll a b => by simp [evalFast, eval, evalFast_eq cat a, evalFast_eq cat b]
  | .join a b .inner _ => by
      simp [evalFast, eval, evalFast_eq cat a, evalFast_eq cat b, innerJoinFast_eq]
  | .join a b .left _ => by
      simp [evalFast, eval, evalFast_eq cat a, evalFast_eq cat b, leftJoinFast_eq]
  | .semi a b _ _ => by simp [evalFast, eval, evalFast_eq cat a, evalFast_eq cat b, semiFast_eq]
  | .distinct r => by
    simp [evalFast, eval, evalFast_eq cat r, canonRepsH_eq Row.leRaw_rawOrder, distinctRows]
  | .aggregate r _ _ => by simp [evalFast, eval, evalFast_eq cat r, aggregateFast_eq]

end Substrait
