import Sverify.Core.Profile

/-!
# `AND` and `OR` as guards (D50)

The SQL and Ibis frontends lift `p₁ AND … AND pₙ` so that an operation in
`pₖ` that can raise runs only where no earlier operand is FALSE, and `OR`
likewise. The core's `AND` and `OR` stay eager (D19); the lift is an
expression the parser builds from the extension functions `sverify_and` and
`sverify_or` (`Parse.lean`), and a plan read as written is untouched.

`Expr.andG ps` is `(T₁ = 1)` with `Tₖ = CASE WHEN pₖ IS NOT FALSE THEN Tₖ₊₁
ELSE 0` and `Tₙ₊₁ = CASE WHEN p₁ AND … AND pₙ THEN 1 ELSE NULL`: the integer
`1`, `0` or `NULL` stands for TRUE, FALSE or NULL. `ifThen` evaluates only
the branch it takes, so `pₖ₊₁` is evaluated only where `pₖ` is not FALSE, and
no guard is copied. `Expr.orG` is the dual.

Under `Profile.reference` (`Expr.evalP_reference`), with every operand TRUE,
FALSE or NULL, and `k` the first operand whose outcome is FALSE or an error:

* `Expr.andG_false`: if it is FALSE, the outcome is FALSE, whatever the
  operands after `pₖ` do (G2);
* `Expr.andG_error`: if it is an error, the outcome is the eager conjunction's
  (G1);
* `Expr.andG_none`: if there is none, the outcome is the eager conjunction's
  (G1).

The same three for `Expr.orG`, with TRUE in place of FALSE.
-/

namespace Substrait

variable [Boxes.Ambient]

/-- `p IS NOT FALSE`: TRUE where `p` is TRUE or NULL. -/
def Expr.notFalse (p : Expr) : Expr := .bin .or (.un .isNull p) p

/-- `p IS NOT TRUE`: TRUE where `p` is FALSE or NULL. -/
def Expr.notTrue (p : Expr) : Expr := .bin .or (.un .isNull p) (.un .not p)

/-- The conjunction of `ps`, folded from the left (as the parser reads `and`). -/
def Expr.conj : List Expr → Expr
  | [] => .lit (.bool true)
  | p :: ps => ps.foldl (.bin .and) p

/-- The disjunction of `ps`, folded from the left. -/
def Expr.disj : List Expr → Expr
  | [] => .lit (.bool false)
  | p :: ps => ps.foldl (.bin .or) p

/-- `Tₖ` for the conjunction `all`: stop with `0` at a FALSE operand, and at the
end `1` where `all` is TRUE and `NULL` otherwise. -/
def Expr.andChain (all : Expr) : List Expr → Expr
  | [] => .ifThen all (.lit (.int 1)) (.lit .null)
  | p :: ps => .ifThen p.notFalse (Expr.andChain all ps) (.lit (.int 0))

/-- `p₁ AND … AND pₙ`, each operand evaluated only where the earlier ones are
not FALSE. -/
def Expr.andG (ps : List Expr) : Expr :=
  .bin .eq (Expr.andChain (Expr.conj ps) ps) (.lit (.int 1))

/-- The dual: stop with `1` at a TRUE operand, and at the end `0` where every
operand is FALSE and `NULL` otherwise. -/
def Expr.orChain (all : Expr) : List Expr → Expr
  | [] => .ifThen (.un .not all) (.lit (.int 0)) (.lit .null)
  | p :: ps => .ifThen p.notTrue (Expr.orChain all ps) (.lit (.int 1))

/-- `p₁ OR … OR pₙ`, each operand evaluated only where the earlier ones are
not TRUE. -/
def Expr.orG (ps : List Expr) : Expr :=
  .bin .eq (Expr.orChain (Expr.disj ps) ps) (.lit (.int 1))

/-! ## The reference's evaluation of the pieces -/

/-- An operand's value is TRUE, FALSE or NULL. -/
def Expr.BoolVal (row : Row) (p : Expr) : Prop :=
  p.eval row = .null ∨ ∃ b, p.eval row = .bool b

/-- `e` raises under the reference on `row`. -/
def Expr.Raises (row : Row) (e : Expr) : Prop := (firstError (e.issues row)).isSome

omit [Boxes.Ambient] in
theorem UnFn.issueAll_isNull (v : Value) : UnFn.isNull.issueAll v = none := by
  cases v <;> simp [UnFn.issueAll, UnFn.issue, UnFn.infIssue]

omit [Boxes.Ambient] in
theorem UnFn.issueAll_not (v : Value) : UnFn.not.issueAll v = none := by
  cases v <;> simp [UnFn.issueAll, UnFn.issue, UnFn.infIssue]

omit [Boxes.Ambient] in
theorem BinFn.issueAll_logic (f : BinFn) (hf : f = .and ∨ f = .or ∨ f = .eq) (v w : Value) :
    f.issueAll v w = none := by
  rcases hf with rfl | rfl | rfl <;> cases v <;> cases w <;>
    simp [BinFn.issueAll, BinFn.issue, BinFn.infIssue, BinFn.makesInf]

theorem Expr.issues_notFalse (row : Row) (p : Expr) :
    p.notFalse.issues row = p.issues row ++ p.issues row := by
  simp [Expr.notFalse, Expr.issues, UnFn.issueAll_isNull, BinFn.issueAll_logic .or (by simp)]

theorem Expr.issues_notTrue (row : Row) (p : Expr) :
    p.notTrue.issues row = p.issues row ++ p.issues row := by
  simp [Expr.notTrue, Expr.issues, UnFn.issueAll_isNull, UnFn.issueAll_not,
    BinFn.issueAll_logic .or (by simp)]

/-! ### Values of the guards -/

omit [Boxes.Ambient] in
theorem Value.isTrue_or3_isNull (v : Value) :
    (or3 (UnFn.apply .isNull v) v).isTrue = true ↔ v ≠ .bool false := by
  cases v <;> simp [UnFn.apply, or3, Value.isTrue]

omit [Boxes.Ambient] in
theorem Value.isTrue_or3_isNull_not (v : Value) (h : v = .null ∨ ∃ b, v = .bool b) :
    (or3 (UnFn.apply .isNull v) (UnFn.apply .not v)).isTrue = true ↔ v ≠ .bool true := by
  rcases h with rfl | ⟨b, rfl⟩ <;> cases b <;> simp [UnFn.apply, or3, Value.isTrue]

theorem Expr.isTrue_notFalse {row : Row} {p : Expr} :
    (p.notFalse.eval row).isTrue = true ↔ p.eval row ≠ .bool false := by
  simp only [Expr.notFalse, Expr.eval, Impl.lean, BinFn.apply]
  exact Value.isTrue_or3_isNull _

theorem Expr.isTrue_notTrue {row : Row} {p : Expr} (h : Expr.BoolVal row p) :
    (p.notTrue.eval row).isTrue = true ↔ p.eval row ≠ .bool true := by
  simp only [Expr.notTrue, Expr.eval, Impl.lean, BinFn.apply]
  exact Value.isTrue_or3_isNull_not _ h

/-! ### The eager conjunction and disjunction -/

theorem Expr.issues_foldl_and (row : Row) (acc : Expr) (ps : List Expr) :
    ((ps.foldl (.bin .and) acc).issues row) = acc.issues row ++ ps.flatMap (·.issues row) := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, ih, Expr.issues, List.flatMap_cons,
      BinFn.issueAll_logic .and (by simp), Option.map_none, Option.toList_none, List.append_nil,
      List.append_assoc]

theorem Expr.issues_foldl_or (row : Row) (acc : Expr) (ps : List Expr) :
    ((ps.foldl (.bin .or) acc).issues row) = acc.issues row ++ ps.flatMap (·.issues row) := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, ih, Expr.issues, List.flatMap_cons,
      BinFn.issueAll_logic .or (by simp), Option.map_none, Option.toList_none, List.append_nil,
      List.append_assoc]

theorem Expr.eval_foldl_and (row : Row) (acc : Expr) (ps : List Expr) :
    (ps.foldl (.bin .and) acc).eval row = ps.foldl (fun v q => and3 v (q.eval row)) (acc.eval row) := by
  induction ps generalizing acc with
  | nil => rfl
  | cons p ps ih => simp only [List.foldl_cons, ih, Expr.eval, Impl.lean, BinFn.apply]

theorem Expr.eval_foldl_or (row : Row) (acc : Expr) (ps : List Expr) :
    (ps.foldl (.bin .or) acc).eval row = ps.foldl (fun v q => or3 v (q.eval row)) (acc.eval row) := by
  induction ps generalizing acc with
  | nil => rfl
  | cons p ps ih => simp only [List.foldl_cons, ih, Expr.eval, Impl.lean, BinFn.apply]

/-! ### The conjunction -/

/-- An operand that does not raise, is not FALSE, and is TRUE or NULL. -/
def Expr.Go (row : Row) (q : Expr) : Prop :=
  firstError (q.issues row) = none ∧ q.eval row ≠ .bool false ∧ Expr.BoolVal row q

theorem Expr.andChain_stop (row : Row) (all : Expr) (p : Expr) (post : List Expr)
    (hp : firstError (p.issues row) = none) (hf : p.eval row = .bool false) :
    ∀ pre : List Expr, (∀ q ∈ pre, Expr.Go row q) →
      (Expr.andChain all (pre ++ p :: post)).eval row = .int 0 ∧
      firstError ((Expr.andChain all (pre ++ p :: post)).issues row) = none
  | [], _ => by
    have hc : ¬((p.notFalse.eval row).isTrue = true) := by
      rw [Expr.isTrue_notFalse]; simp [hf]
    simp [Expr.andChain, Expr.eval, Expr.issues, hc, Expr.issues_notFalse, firstError_append, hp]
  | q :: pre, h => by
    obtain ⟨hq, hnf, hbv⟩ := h q (by simp)
    have hc : (q.notFalse.eval row).isTrue = true := Expr.isTrue_notFalse.mpr hnf
    obtain ⟨h1, h2⟩ := Expr.andChain_stop row all p post hp hf pre (fun r hr => h r (by simp [hr]))
    simp only [List.cons_append, Expr.andChain, Expr.eval, hc, if_true, Expr.issues,
      Expr.issues_notFalse, firstError_append, hq, Option.or_none, h2]
    exact ⟨h1, rfl⟩

/-- **G2**: where the first operand that is FALSE or raises is FALSE, the guarded
conjunction is FALSE and raises nothing, whatever the operands after it do. -/
theorem Expr.andG_false (row : Row) (pre : List Expr) (p : Expr) (post : List Expr)
    (hpre : ∀ q ∈ pre, Expr.Go row q) (hp : firstError (p.issues row) = none)
    (hf : p.eval row = .bool false) :
    (Expr.andG (pre ++ p :: post)).refOutcome row = .ok (.bool false) := by
  obtain ⟨h1, h2⟩ := Expr.andChain_stop row (Expr.conj (pre ++ p :: post)) p post hp hf pre hpre
  simp [Expr.refOutcome, Expr.andG, Expr.issues, Expr.eval, Impl.lean, BinFn.apply, h1, h2,
    BinFn.issueAll_logic .eq (by simp), firstError_append, Value.numPair]

theorem Expr.andChain_error (row : Row) (all : Expr) (p : Expr) (post : List Expr) (k : Issue)
    (hp : firstError (p.issues row) = some k) :
    ∀ pre : List Expr, (∀ q ∈ pre, Expr.Go row q) →
      firstError ((Expr.andChain all (pre ++ p :: post)).issues row) = some k
  | [], _ => by
    simp [Expr.andChain, Expr.issues, Expr.issues_notFalse, firstError_append, hp]
  | q :: pre, h => by
    obtain ⟨hq, hnf, hbv⟩ := h q (by simp)
    have ih := Expr.andChain_error row all p post k hp pre (fun r hr => h r (by simp [hr]))
    simp only [List.cons_append, Expr.andChain, Expr.issues, Expr.issues_notFalse,
      firstError_append, hq, Option.or_none]
    cases hc : (q.notFalse.eval row).isTrue <;> simp [hc] <;> simpa using ih

/-- **G1, an error**: where the first operand that is FALSE or raises raises, the
guarded conjunction raises the eager conjunction's error. -/
theorem Expr.andG_error (row : Row) (pre : List Expr) (p : Expr) (post : List Expr) (k : Issue)
    (hpre : ∀ q ∈ pre, Expr.Go row q) (hp : firstError (p.issues row) = some k) :
    (Expr.andG (pre ++ p :: post)).refOutcome row = .error k ∧
      (Expr.conj (pre ++ p :: post)).refOutcome row = .error k := by
  have hc := Expr.andChain_error row (Expr.conj (pre ++ p :: post)) p post k hp pre hpre
  constructor
  · simp [Expr.refOutcome, Expr.andG, Expr.issues, BinFn.issueAll_logic .eq (by simp),
      firstError_append, hc]
  · cases pre with
    | nil =>
      simp [Expr.refOutcome, Expr.conj, Expr.issues_foldl_and, firstError_append, hp]
    | cons q pre =>
      obtain ⟨hq, -, -⟩ := hpre q (by simp)
      have hpre' : ∀ r ∈ pre, Expr.Go row r := fun r hr => hpre r (by simp [hr])
      have hall : firstError ((pre.flatMap (·.issues row))) = none := by
        induction pre with
        | nil => rfl
        | cons r pre ih =>
          obtain ⟨hr, -, -⟩ := hpre' r (by simp)
          simp only [List.flatMap_cons, firstError_append, hr, Option.none_or]
          exact ih (fun s hs => hpre' s (by simp [hs]))
      simp [Expr.refOutcome, Expr.conj, Expr.issues_foldl_and, firstError_append, hq, hall, hp]

/-- The eager conjunction of operands that are TRUE or NULL is TRUE or NULL. -/
theorem Expr.fold_and_go {row : Row} (ps : List Expr) :
    ∀ (v : Value), (v = .null ∨ v = .bool true) → (∀ q ∈ ps, Expr.Go row q) →
      (ps.foldl (fun v q => and3 v (q.eval row)) v = .null ∨
        ps.foldl (fun v q => and3 v (q.eval row)) v = .bool true) := by
  induction ps with
  | nil => intro v hv _; exact hv
  | cons q ps ih =>
    intro v hv h
    obtain ⟨-, hnf, hbv⟩ := h q (by simp)
    refine ih (and3 v (q.eval row)) ?_ (fun r hr => h r (by simp [hr]))
    rcases hbv with hq | ⟨b, hq⟩
    · rcases hv with rfl | rfl <;> simp [and3, hq]
    · cases b with
      | false => exact absurd hq hnf
      | true => rcases hv with rfl | rfl <;> simp [and3, hq]

theorem Expr.andChain_end (row : Row) (all : Expr) :
    ∀ ps : List Expr, (∀ q ∈ ps, Expr.Go row q) →
      (Expr.andChain all ps).eval row = (if (all.eval row).isTrue then .int 1 else .null) ∧
      firstError ((Expr.andChain all ps).issues row) = firstError (all.issues row)
  | [], _ => by
    cases hc : (all.eval row).isTrue <;> simp [Expr.andChain, Expr.eval, Expr.issues, hc]
  | q :: ps, h => by
    obtain ⟨hq, hnf, hbv⟩ := h q (by simp)
    have hc : (q.notFalse.eval row).isTrue = true := Expr.isTrue_notFalse.mpr hnf
    obtain ⟨h1, h2⟩ := Expr.andChain_end row all ps (fun r hr => h r (by simp [hr]))
    simp only [Expr.andChain, Expr.eval, hc, if_true, Expr.issues, Expr.issues_notFalse,
      firstError_append, hq, Option.or_none, h2]
    exact ⟨h1, by simp⟩

/-- **G1, no operand is FALSE or raises**: the guarded conjunction has the eager
conjunction's outcome. -/
theorem Expr.andG_none (row : Row) (p : Expr) (ps : List Expr)
    (h : ∀ q ∈ p :: ps, Expr.Go row q) :
    (Expr.andG (p :: ps)).refOutcome row = (Expr.conj (p :: ps)).refOutcome row := by
  obtain ⟨h1, h2⟩ := Expr.andChain_end row (Expr.conj (p :: ps)) (p :: ps) h
  have hall : firstError ((Expr.conj (p :: ps)).issues row) = none := by
    simp only [Expr.conj, Expr.issues_foldl_and, firstError_append]
    obtain ⟨hp, -, -⟩ := h p (by simp)
    have : ∀ qs : List Expr, (∀ q ∈ qs, Expr.Go row q) → firstError (qs.flatMap (·.issues row)) = none := by
      intro qs
      induction qs with
      | nil => intro _; rfl
      | cons r qs ih =>
        intro hh
        obtain ⟨hr, -, -⟩ := hh r (by simp)
        simp only [List.flatMap_cons, firstError_append, hr, Option.none_or]
        exact ih (fun s hs => hh s (by simp [hs]))
    rw [hp, this ps (fun q hq => h q (by simp [hq]))]; rfl
  have hv : (Expr.conj (p :: ps)).eval row = .null ∨ (Expr.conj (p :: ps)).eval row = .bool true := by
    simp only [Expr.conj, Expr.eval_foldl_and]
    obtain ⟨-, hnf, hbv⟩ := h p (by simp)
    refine Expr.fold_and_go ps _ ?_ (fun q hq => h q (by simp [hq]))
    rcases hbv with hq | ⟨b, hq⟩
    · exact .inl hq
    · cases b with
      | false => exact absurd hq hnf
      | true => exact .inr hq
  have hall' : firstError ((Expr.andG (p :: ps)).issues row) = none := by
    simp [Expr.andG, Expr.issues, BinFn.issueAll_logic .eq (by simp), firstError_append, h2, hall]
  unfold Expr.refOutcome
  rw [hall', hall]
  simp only [Expr.andG, Expr.eval, Impl.lean, BinFn.apply, h1]
  rcases hv with hv | hv <;> simp [hv, Value.isTrue, Value.numPair]

end Substrait
