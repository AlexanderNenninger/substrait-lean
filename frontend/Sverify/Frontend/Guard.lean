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

@[simp] theorem UnFn.issueAll_isNull (v : Value) : UnFn.isNull.issueAll v = none := by
  cases v <;> simp [UnFn.issueAll, UnFn.issue, UnFn.infIssue]

@[simp] theorem UnFn.issueAll_not (v : Value) : UnFn.not.issueAll v = none := by
  cases v <;> simp [UnFn.issueAll, UnFn.issue, UnFn.infIssue]

theorem BinFn.infIssue_none {f : BinFn} (h : f.makesInf = false) (v w : Value) :
    f.infIssue v w = none := by
  unfold BinFn.infIssue; split <;> simp [h]

@[simp] theorem BinFn.issueAll_and (v w : Value) : BinFn.and.issueAll v w = none := by
  simp only [BinFn.issueAll, BinFn.infIssue_none (f := .and) rfl]
  cases v <;> cases w <;> simp [BinFn.issue]

@[simp] theorem BinFn.issueAll_or (v w : Value) : BinFn.or.issueAll v w = none := by
  simp only [BinFn.issueAll, BinFn.infIssue_none (f := .or) rfl]
  cases v <;> cases w <;> simp [BinFn.issue]

@[simp] theorem BinFn.issueAll_eq (v w : Value) : BinFn.eq.issueAll v w = none := by
  simp only [BinFn.issueAll, BinFn.infIssue_none (f := .eq) rfl]
  cases v <;> cases w <;> simp [BinFn.issue]

theorem Expr.issues_notFalse (row : Row) (p : Expr) :
    p.notFalse.issues row = p.issues row ++ p.issues row := by
  simp [Expr.notFalse, Expr.issues]

theorem Expr.issues_notTrue (row : Row) (p : Expr) :
    p.notTrue.issues row = p.issues row ++ p.issues row := by
  simp [Expr.notTrue, Expr.issues]

/-! ### Values of the guards -/

theorem Value.isTrue_or3_isNull (v : Value) (h : v = .null ∨ ∃ b, v = .bool b) :
    (or3 (UnFn.apply .isNull v) v).isTrue = true ↔ v ≠ .bool false := by
  rcases h with rfl | ⟨b, rfl⟩
  · simp [UnFn.apply, or3, Value.isTrue]
  · cases b <;> simp [UnFn.apply, or3, Value.isTrue]

theorem Value.isTrue_or3_isNull_not (v : Value) (h : v = .null ∨ ∃ b, v = .bool b) :
    (or3 (UnFn.apply .isNull v) (UnFn.apply .not v)).isTrue = true ↔ v ≠ .bool true := by
  rcases h with rfl | ⟨b, rfl⟩
  · simp [UnFn.apply, or3, Value.isTrue]
  · cases b <;> simp [UnFn.apply, or3, Value.isTrue]

theorem Expr.isTrue_notFalse {row : Row} {p : Expr} (h : Expr.BoolVal row p) :
    (p.notFalse.eval row).isTrue = true ↔ p.eval row ≠ .bool false := by
  simp only [Expr.notFalse, Expr.eval, Impl.lean, BinFn.apply]
  exact Value.isTrue_or3_isNull _ h

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
    simp [List.foldl_cons, ih, Expr.issues, List.flatMap_cons, List.append_assoc]

theorem Expr.issues_foldl_or (row : Row) (acc : Expr) (ps : List Expr) :
    ((ps.foldl (.bin .or) acc).issues row) = acc.issues row ++ ps.flatMap (·.issues row) := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp [List.foldl_cons, ih, Expr.issues, List.flatMap_cons, List.append_assoc]

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

theorem Expr.firstError_flatMap_none (row : Row) :
    ∀ qs : List Expr, (∀ q ∈ qs, firstError (q.issues row) = none) →
      firstError (qs.flatMap (·.issues row)) = none
  | [], _ => rfl
  | q :: qs, h => by
    simp only [List.flatMap_cons, firstError_append, h q (by simp), Option.none_or]
    exact Expr.firstError_flatMap_none row qs (fun r hr => h r (by simp [hr]))

theorem Expr.go_notFalse {row : Row} {q : Expr} (h : Expr.Go row q) :
    (q.notFalse.eval row).isTrue = true :=
  (Expr.isTrue_notFalse h.2.2).mpr h.2.1

theorem Expr.andChain_stop (row : Row) (all : Expr) (p : Expr) (post : List Expr)
    (hp : firstError (p.issues row) = none) (hbv : Expr.BoolVal row p)
    (hf : p.eval row = .bool false) :
    ∀ pre : List Expr, (∀ q ∈ pre, Expr.Go row q) →
      (Expr.andChain all (pre ++ p :: post)).eval row = .int 0 ∧
      firstError ((Expr.andChain all (pre ++ p :: post)).issues row) = none
  | [], _ => by
    have hc : ¬((p.notFalse.eval row).isTrue = true) := by
      rw [Expr.isTrue_notFalse hbv]; simp [hf]
    simp [Expr.andChain, Expr.eval, Expr.issues, hc, Expr.issues_notFalse, firstError_append, hp]
  | q :: pre, h => by
    have hqg := h q (by simp)
    have hc := Expr.go_notFalse hqg
    obtain ⟨h1, h2⟩ := Expr.andChain_stop row all p post hp hbv hf pre (fun r hr => h r (by simp [hr]))
    simp only [List.cons_append, Expr.andChain, Expr.eval, hc, ite_true, Expr.issues,
      Expr.issues_notFalse, firstError_append, hqg.1, Option.or_none, h2]
    exact ⟨h1, trivial⟩

/-- **G2**: where the first operand that is FALSE or raises is FALSE, the guarded
conjunction is FALSE and raises nothing, whatever the operands after it do. -/
theorem Expr.andG_false (row : Row) (pre : List Expr) (p : Expr) (post : List Expr)
    (hpre : ∀ q ∈ pre, Expr.Go row q) (hp : firstError (p.issues row) = none)
    (hbv : Expr.BoolVal row p) (hf : p.eval row = .bool false) :
    (Expr.andG (pre ++ p :: post)).refOutcome row = .ok (.bool false) := by
  obtain ⟨h1, h2⟩ := Expr.andChain_stop row (Expr.conj (pre ++ p :: post)) p post hp hbv hf pre hpre
  simp [Expr.refOutcome, Expr.andG, Expr.issues, Expr.eval, Impl.lean, BinFn.apply, h1, h2,
    Value.numPair]

theorem Expr.andChain_error (row : Row) (all : Expr) (p : Expr) (post : List Expr) (k : Issue)
    (hp : firstError (p.issues row) = some k) :
    ∀ pre : List Expr, (∀ q ∈ pre, Expr.Go row q) →
      firstError ((Expr.andChain all (pre ++ p :: post)).issues row) = some k
  | [], _ => by
    simp [Expr.andChain, Expr.issues, Expr.issues_notFalse, firstError_append, hp]
  | q :: pre, h => by
    have hqg := h q (by simp)
    have hc := Expr.go_notFalse hqg
    have ih := Expr.andChain_error row all p post k hp pre (fun r hr => h r (by simp [hr]))
    simp only [List.cons_append, Expr.andChain, Expr.issues, Expr.issues_notFalse,
      firstError_append, hqg.1, Option.or_none, hc, ite_true, Option.none_or]
    exact ih

theorem Expr.conj_error (row : Row) (pre : List Expr) (p : Expr) (post : List Expr) (k : Issue)
    (hpre : ∀ q ∈ pre, Expr.Go row q) (hp : firstError (p.issues row) = some k) :
    firstError ((Expr.conj (pre ++ p :: post)).issues row) = some k := by
  have hall := Expr.firstError_flatMap_none row pre (fun q hq => (hpre q hq).1)
  cases pre with
  | nil => simp [Expr.conj, Expr.issues_foldl_and, firstError_append, hp]
  | cons q pre =>
    simp only [List.cons_append, Expr.conj, Expr.issues_foldl_and, List.flatMap_cons,
      firstError_append] at hall ⊢
    have hq := (hpre q (by simp)).1
    simp [hq] at hall ⊢
    simp [hall, hp, firstError_append]

/-- **G1, an error**: where the first operand that is FALSE or raises raises, the
guarded conjunction raises the eager conjunction's error. -/
theorem Expr.andG_error (row : Row) (pre : List Expr) (p : Expr) (post : List Expr) (k : Issue)
    (hpre : ∀ q ∈ pre, Expr.Go row q) (hp : firstError (p.issues row) = some k) :
    (Expr.andG (pre ++ p :: post)).refOutcome row = .error k ∧
      (Expr.conj (pre ++ p :: post)).refOutcome row = .error k := by
  have hc := Expr.andChain_error row (Expr.conj (pre ++ p :: post)) p post k hp pre hpre
  constructor
  · simp [Expr.refOutcome, Expr.andG, Expr.issues, hc]
  · simp [Expr.refOutcome, Expr.conj_error row pre p post k hpre hp]

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
    have hqg := h q (by simp)
    have hc := Expr.go_notFalse hqg
    obtain ⟨h1, h2⟩ := Expr.andChain_end row all ps (fun r hr => h r (by simp [hr]))
    simp only [Expr.andChain, Expr.eval, hc, ite_true, Expr.issues, Expr.issues_notFalse,
      firstError_append, hqg.1, Option.or_none, h2, Option.none_or]
    exact ⟨h1, trivial⟩

/-- **G1, no operand is FALSE or raises**: the guarded conjunction has the eager
conjunction's outcome. -/
theorem Expr.andG_none (row : Row) (p : Expr) (ps : List Expr)
    (h : ∀ q ∈ p :: ps, Expr.Go row q) :
    (Expr.andG (p :: ps)).refOutcome row = (Expr.conj (p :: ps)).refOutcome row := by
  obtain ⟨h1, h2⟩ := Expr.andChain_end row (Expr.conj (p :: ps)) (p :: ps) h
  have hall : firstError ((Expr.conj (p :: ps)).issues row) = none := by
    simp only [Expr.conj, Expr.issues_foldl_and, firstError_append, (h p (by simp)).1,
      Option.none_or]
    exact Expr.firstError_flatMap_none row ps (fun q hq => (h q (by simp [hq])).1)
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
    simp [Expr.andG, Expr.issues, h2, hall]
  unfold Expr.refOutcome
  rw [hall', hall]
  simp only [Expr.andG, Expr.eval, Impl.lean, BinFn.apply, h1]
  rcases hv with hv | hv <;> simp [hv, Value.isTrue, Value.numPair]

/-! ### The disjunction -/

/-- An operand that does not raise, is not TRUE, and is FALSE or NULL. -/
def Expr.GoOr (row : Row) (q : Expr) : Prop :=
  firstError (q.issues row) = none ∧ q.eval row ≠ .bool true ∧ Expr.BoolVal row q

theorem Expr.go_notTrue {row : Row} {q : Expr} (h : Expr.GoOr row q) :
    (q.notTrue.eval row).isTrue = true :=
  (Expr.isTrue_notTrue h.2.2).mpr h.2.1

theorem Expr.orChain_stop (row : Row) (all : Expr) (p : Expr) (post : List Expr)
    (hp : firstError (p.issues row) = none) (hbv : Expr.BoolVal row p)
    (ht : p.eval row = .bool true) :
    ∀ pre : List Expr, (∀ q ∈ pre, Expr.GoOr row q) →
      (Expr.orChain all (pre ++ p :: post)).eval row = .int 1 ∧
      firstError ((Expr.orChain all (pre ++ p :: post)).issues row) = none
  | [], _ => by
    have hc : ¬((p.notTrue.eval row).isTrue = true) := by
      rw [Expr.isTrue_notTrue hbv]; simp [ht]
    simp [Expr.orChain, Expr.eval, Expr.issues, hc, Expr.issues_notTrue, firstError_append, hp]
  | q :: pre, h => by
    have hqg := h q (by simp)
    have hc := Expr.go_notTrue hqg
    obtain ⟨h1, h2⟩ := Expr.orChain_stop row all p post hp hbv ht pre (fun r hr => h r (by simp [hr]))
    simp only [List.cons_append, Expr.orChain, Expr.eval, hc, ite_true, Expr.issues,
      Expr.issues_notTrue, firstError_append, hqg.1, Option.or_none, h2]
    exact ⟨h1, trivial⟩

/-- **G2 for `OR`**: where the first operand that is TRUE or raises is TRUE, the
guarded disjunction is TRUE and raises nothing. -/
theorem Expr.orG_true (row : Row) (pre : List Expr) (p : Expr) (post : List Expr)
    (hpre : ∀ q ∈ pre, Expr.GoOr row q) (hp : firstError (p.issues row) = none)
    (hbv : Expr.BoolVal row p) (ht : p.eval row = .bool true) :
    (Expr.orG (pre ++ p :: post)).refOutcome row = .ok (.bool true) := by
  obtain ⟨h1, h2⟩ := Expr.orChain_stop row (Expr.disj (pre ++ p :: post)) p post hp hbv ht pre hpre
  simp [Expr.refOutcome, Expr.orG, Expr.issues, Expr.eval, Impl.lean, BinFn.apply, h1, h2,
    Value.numPair]

theorem Expr.orChain_error (row : Row) (all : Expr) (p : Expr) (post : List Expr) (k : Issue)
    (hp : firstError (p.issues row) = some k) :
    ∀ pre : List Expr, (∀ q ∈ pre, Expr.GoOr row q) →
      firstError ((Expr.orChain all (pre ++ p :: post)).issues row) = some k
  | [], _ => by
    simp [Expr.orChain, Expr.issues, Expr.issues_notTrue, firstError_append, hp]
  | q :: pre, h => by
    have hqg := h q (by simp)
    have hc := Expr.go_notTrue hqg
    have ih := Expr.orChain_error row all p post k hp pre (fun r hr => h r (by simp [hr]))
    simp only [List.cons_append, Expr.orChain, Expr.issues, Expr.issues_notTrue,
      firstError_append, hqg.1, Option.or_none, hc, ite_true, Option.none_or]
    exact ih

theorem Expr.disj_error (row : Row) (pre : List Expr) (p : Expr) (post : List Expr) (k : Issue)
    (hpre : ∀ q ∈ pre, Expr.GoOr row q) (hp : firstError (p.issues row) = some k) :
    firstError ((Expr.disj (pre ++ p :: post)).issues row) = some k := by
  have hall := Expr.firstError_flatMap_none row pre (fun q hq => (hpre q hq).1)
  cases pre with
  | nil => simp [Expr.disj, Expr.issues_foldl_or, firstError_append, hp]
  | cons q pre =>
    simp only [List.cons_append, Expr.disj, Expr.issues_foldl_or, List.flatMap_cons,
      firstError_append] at hall ⊢
    have hq := (hpre q (by simp)).1
    simp [hq] at hall ⊢
    simp [hall, hp, firstError_append]

/-- **G1 for `OR`, an error**. -/
theorem Expr.orG_error (row : Row) (pre : List Expr) (p : Expr) (post : List Expr) (k : Issue)
    (hpre : ∀ q ∈ pre, Expr.GoOr row q) (hp : firstError (p.issues row) = some k) :
    (Expr.orG (pre ++ p :: post)).refOutcome row = .error k ∧
      (Expr.disj (pre ++ p :: post)).refOutcome row = .error k := by
  have hc := Expr.orChain_error row (Expr.disj (pre ++ p :: post)) p post k hp pre hpre
  constructor
  · simp [Expr.refOutcome, Expr.orG, Expr.issues, hc]
  · simp [Expr.refOutcome, Expr.disj_error row pre p post k hpre hp]

/-- The eager disjunction of operands that are FALSE or NULL is FALSE or NULL. -/
theorem Expr.fold_or_go {row : Row} (ps : List Expr) :
    ∀ (v : Value), (v = .null ∨ v = .bool false) → (∀ q ∈ ps, Expr.GoOr row q) →
      (ps.foldl (fun v q => or3 v (q.eval row)) v = .null ∨
        ps.foldl (fun v q => or3 v (q.eval row)) v = .bool false) := by
  induction ps with
  | nil => intro v hv _; exact hv
  | cons q ps ih =>
    intro v hv h
    obtain ⟨-, hnt, hbv⟩ := h q (by simp)
    refine ih (or3 v (q.eval row)) ?_ (fun r hr => h r (by simp [hr]))
    rcases hbv with hq | ⟨b, hq⟩
    · rcases hv with rfl | rfl <;> simp [or3, hq]
    · cases b with
      | true => exact absurd hq hnt
      | false => rcases hv with rfl | rfl <;> simp [or3, hq]

theorem Expr.orChain_end (row : Row) (all : Expr) :
    ∀ ps : List Expr, (∀ q ∈ ps, Expr.GoOr row q) →
      (Expr.orChain all ps).eval row =
        (if (UnFn.apply .not (all.eval row)).isTrue then .int 0 else .null) ∧
      firstError ((Expr.orChain all ps).issues row) = firstError (all.issues row)
  | [], _ => by
    cases hc : (UnFn.apply .not (all.eval row)).isTrue <;>
      simp [Expr.orChain, Expr.eval, Expr.issues, Impl.lean, hc]
  | q :: ps, h => by
    have hqg := h q (by simp)
    have hc := Expr.go_notTrue hqg
    obtain ⟨h1, h2⟩ := Expr.orChain_end row all ps (fun r hr => h r (by simp [hr]))
    simp only [Expr.orChain, Expr.eval, hc, ite_true, Expr.issues, Expr.issues_notTrue,
      firstError_append, hqg.1, Option.or_none, h2, Option.none_or]
    exact ⟨h1, trivial⟩

/-- **G1 for `OR`, no operand is TRUE or raises**. -/
theorem Expr.orG_none (row : Row) (p : Expr) (ps : List Expr)
    (h : ∀ q ∈ p :: ps, Expr.GoOr row q) :
    (Expr.orG (p :: ps)).refOutcome row = (Expr.disj (p :: ps)).refOutcome row := by
  obtain ⟨h1, h2⟩ := Expr.orChain_end row (Expr.disj (p :: ps)) (p :: ps) h
  have hall : firstError ((Expr.disj (p :: ps)).issues row) = none := by
    simp only [Expr.disj, Expr.issues_foldl_or, firstError_append, (h p (by simp)).1,
      Option.none_or]
    exact Expr.firstError_flatMap_none row ps (fun q hq => (h q (by simp [hq])).1)
  have hv : (Expr.disj (p :: ps)).eval row = .null ∨ (Expr.disj (p :: ps)).eval row = .bool false := by
    simp only [Expr.disj, Expr.eval_foldl_or]
    obtain ⟨-, hnt, hbv⟩ := h p (by simp)
    refine Expr.fold_or_go ps _ ?_ (fun q hq => h q (by simp [hq]))
    rcases hbv with hq | ⟨b, hq⟩
    · exact .inl hq
    · cases b with
      | true => exact absurd hq hnt
      | false => exact .inr hq
  have hall' : firstError ((Expr.orG (p :: ps)).issues row) = none := by
    simp [Expr.orG, Expr.issues, h2, hall]
  unfold Expr.refOutcome
  rw [hall', hall]
  simp only [Expr.orG, Expr.eval, Impl.lean, BinFn.apply, h1]
  rcases hv with hv | hv <;> simp [hv, Value.isTrue, Value.numPair, UnFn.apply]

/-! ## Plain expressions

A plain expression raises on no row, so it can guard the operands after it
without being guarded itself, and an operand that is plain stays outside the
chain (`Expr.andLift`). -/

/-- Columns and literals, joined by `=`, `<`, `IS NULL`, `NOT`, `AND` and `OR`. -/
def Expr.plain : Expr → Bool
  | .lit _ | .field _ => true
  | .un .not a | .un .isNull a => a.plain
  | .bin .eq a b | .bin .lt a b | .bin .and a b | .bin .or a b => a.plain && b.plain
  | _ => false

@[simp] theorem BinFn.issueAll_lt (v w : Value) : BinFn.lt.issueAll v w = none := by
  simp only [BinFn.issueAll, BinFn.infIssue_none (f := .lt) rfl]
  cases v <;> cases w <;> simp [BinFn.issue]

/-- **A plain expression raises on no row** (under `Profile.reference`). -/
theorem Expr.issues_plain (row : Row) : ∀ e : Expr, e.plain = true → e.issues row = []
  | .lit _, _ | .field _, _ => rfl
  | .un f a, h => by
    cases f <;> simp [Expr.plain] at h <;>
      simp [Expr.issues, Expr.issues_plain row a h]
  | .bin f a b, h => by
    cases f <;> simp [Expr.plain] at h <;>
      simp [Expr.issues, Expr.issues_plain row a h.1, Expr.issues_plain row b h.2]
  | .ifThen _ _ _, h | .hof _ _ _, h => by simp [Expr.plain] at h

/-- `p₁ AND … AND pₙ` as the frontends lift it: the operands in order, the
plain ones also outside the chain so that an optimizer still sees them. All
plain: the eager `AND`, untouched. -/
def Expr.andLift (ps : List Expr) : Expr :=
  let plains := ps.filter Expr.plain
  if plains.length = ps.length then Expr.conj ps
  else if plains.isEmpty then Expr.andG ps
  else .bin .and (Expr.conj plains) (Expr.andG ps)

/-- `p₁ OR … OR pₙ` as the frontends lift it. -/
def Expr.orLift (ps : List Expr) : Expr :=
  let plains := ps.filter Expr.plain
  if plains.length = ps.length then Expr.disj ps
  else if plains.isEmpty then Expr.orG ps
  else .bin .or (Expr.disj plains) (Expr.orG ps)

theorem Expr.conj_plain_issues (row : Row) (ps : List Expr) (h : ∀ q ∈ ps, q.plain = true) :
    (Expr.conj ps).issues row = [] := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    simp only [Expr.conj, Expr.issues_foldl_and, Expr.issues_plain row p (h p (by simp)),
      List.nil_append]
    simp only [List.flatMap_eq_nil_iff]
    exact fun q hq => Expr.issues_plain row q (h q (List.mem_cons_of_mem _ hq))

theorem Expr.disj_plain_issues (row : Row) (ps : List Expr) (h : ∀ q ∈ ps, q.plain = true) :
    (Expr.disj ps).issues row = [] := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    simp only [Expr.disj, Expr.issues_foldl_or, Expr.issues_plain row p (h p (by simp)),
      List.nil_append]
    simp only [List.flatMap_eq_nil_iff]
    exact fun q hq => Expr.issues_plain row q (h q (List.mem_cons_of_mem _ hq))

omit [Boxes.Ambient] in
theorem Expr.mixed_length {ps : List Expr} (hnp : ∃ q ∈ ps, q.plain = false) :
    (ps.filter Expr.plain).length ≠ ps.length := by
  intro h
  obtain ⟨q, hq, hqf⟩ := hnp
  have := List.filter_eq_self.mp ((List.filter_sublist ps).eq_of_length h) q hq
  simp [hqf] at this

omit [Boxes.Ambient] in
theorem Expr.filter_plain_plain (ps : List Expr) : ∀ q ∈ ps.filter Expr.plain, q.plain = true :=
  fun q hq => by simpa using (List.mem_filter.mp hq).2

omit [Boxes.Ambient] in
theorem and3_false_right (v : Value) : and3 v (.bool false) = .bool false := by
  cases v <;> first | rfl | (rename_i b; cases b <;> rfl)

omit [Boxes.Ambient] in
theorem or3_true_right (v : Value) : or3 v (.bool true) = .bool true := by
  cases v <;> first | rfl | (rename_i b; cases b <;> rfl)

/-- An `AND` whose first operand does not raise takes its second operand's
outcome where that is an error. -/
theorem Expr.and_outer_error (row : Row) (a e : Expr) (k : Issue)
    (hi : a.issues row = []) (he : e.refOutcome row = .error k) :
    (Expr.bin .and a e).refOutcome row = .error k := by
  unfold Expr.refOutcome at he
  split at he
  · next k' hk =>
    cases he
    have : firstError ((Expr.bin .and a e).issues row) = some k := by
      simp [Expr.issues, hi, hk]
    simp [Expr.refOutcome, this]
  · cases he

theorem Expr.and_outer_false (row : Row) (a e : Expr)
    (hi : a.issues row = []) (he : e.refOutcome row = .ok (.bool false)) :
    (Expr.bin .and a e).refOutcome row = .ok (.bool false) := by
  unfold Expr.refOutcome at he
  split at he
  · cases he
  · next hn =>
    have hv : e.eval row = .bool false := by simpa using he
    have : firstError ((Expr.bin .and a e).issues row) = none := by
      simp [Expr.issues, hi, hn]
    simp [Expr.refOutcome, this, Expr.eval, Impl.lean, BinFn.apply, hv, and3_false_right]

theorem Expr.or_outer_error (row : Row) (a e : Expr) (k : Issue)
    (hi : a.issues row = []) (he : e.refOutcome row = .error k) :
    (Expr.bin .or a e).refOutcome row = .error k := by
  unfold Expr.refOutcome at he
  split at he
  · next k' hk =>
    cases he
    have : firstError ((Expr.bin .or a e).issues row) = some k := by
      simp [Expr.issues, hi, hk]
    simp [Expr.refOutcome, this]
  · cases he

theorem Expr.or_outer_true (row : Row) (a e : Expr)
    (hi : a.issues row = []) (he : e.refOutcome row = .ok (.bool true)) :
    (Expr.bin .or a e).refOutcome row = .ok (.bool true) := by
  unfold Expr.refOutcome at he
  split at he
  · cases he
  · next hn =>
    have hv : e.eval row = .bool true := by simpa using he
    have : firstError ((Expr.bin .or a e).issues row) = none := by
      simp [Expr.issues, hi, hn]
    simp [Expr.refOutcome, this, Expr.eval, Impl.lean, BinFn.apply, hv, or3_true_right]

/-- **The lift protects** (G2 for `andLift`): where an operand is FALSE and the
operands before it do not raise, a lift with an operand outside the plain ones
is FALSE, whatever the operands after it would do. -/
theorem Expr.andLift_false (row : Row) (pre : List Expr) (p : Expr) (post : List Expr) (hpre : ∀ q ∈ pre, Expr.Go row q) (hp : firstError (p.issues row) = none)
    (hbv : Expr.BoolVal row p) (hf : p.eval row = .bool false)
    (hnp : ∃ q ∈ pre ++ p :: post, q.plain = false) :
    (Expr.andLift (pre ++ p :: post)).refOutcome row = .ok (.bool false) := by
  have hg := Expr.andG_false row pre p post hpre hp hbv hf
  have hlen := Expr.mixed_length hnp
  unfold Expr.andLift
  dsimp only
  split
  · next h => exact absurd h hlen
  split
  · exact hg
  · exact Expr.and_outer_false row _ _ (Expr.conj_plain_issues row ((pre ++ p :: post).filter Expr.plain) (Expr.filter_plain_plain _)) hg

theorem Expr.orLift_true (row : Row) (pre : List Expr) (p : Expr) (post : List Expr) (hpre : ∀ q ∈ pre, Expr.GoOr row q) (hp : firstError (p.issues row) = none)
    (hbv : Expr.BoolVal row p) (ht : p.eval row = .bool true)
    (hnp : ∃ q ∈ pre ++ p :: post, q.plain = false) :
    (Expr.orLift (pre ++ p :: post)).refOutcome row = .ok (.bool true) := by
  have hg := Expr.orG_true row pre p post hpre hp hbv ht
  have hlen := Expr.mixed_length hnp
  unfold Expr.orLift
  dsimp only
  split
  · next h => exact absurd h hlen
  split
  · exact hg
  · exact Expr.or_outer_true row _ _ (Expr.disj_plain_issues row ((pre ++ p :: post).filter Expr.plain) (Expr.filter_plain_plain _)) hg

/-- **An error in a reached operand still surfaces** through the lift. -/
theorem Expr.andLift_error (row : Row) (pre : List Expr) (p : Expr) (post : List Expr) (k : Issue)
    (hpre : ∀ q ∈ pre, Expr.Go row q) (hp : firstError (p.issues row) = some k)
    (hnp : ∃ q ∈ pre ++ p :: post, q.plain = false) :
    (Expr.andLift (pre ++ p :: post)).refOutcome row = .error k := by
  have hg := (Expr.andG_error row pre p post k hpre hp).1
  have hlen := Expr.mixed_length hnp
  unfold Expr.andLift
  dsimp only
  split
  · next h => exact absurd h hlen
  split
  · exact hg
  · exact Expr.and_outer_error row _ _ k (Expr.conj_plain_issues row ((pre ++ p :: post).filter Expr.plain) (Expr.filter_plain_plain _)) hg

theorem Expr.orLift_error (row : Row) (pre : List Expr) (p : Expr) (post : List Expr) (k : Issue)
    (hpre : ∀ q ∈ pre, Expr.GoOr row q) (hp : firstError (p.issues row) = some k)
    (hnp : ∃ q ∈ pre ++ p :: post, q.plain = false) :
    (Expr.orLift (pre ++ p :: post)).refOutcome row = .error k := by
  have hg := (Expr.orG_error row pre p post k hpre hp).1
  have hlen := Expr.mixed_length hnp
  unfold Expr.orLift
  dsimp only
  split
  · next h => exact absurd h hlen
  split
  · exact hg
  · exact Expr.or_outer_error row _ _ k (Expr.disj_plain_issues row ((pre ++ p :: post).filter Expr.plain) (Expr.filter_plain_plain _)) hg

end Substrait
