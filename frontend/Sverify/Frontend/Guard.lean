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
the branch it takes, so `pₖ₊₁` is evaluated only where `pₖ` is not FALSE. Each
operand is written three times (twice in `IS NOT FALSE`, once in the closing
conjunction). `Expr.orG` is the dual.

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
  have := List.filter_eq_self.mp (List.filter_sublist.eq_of_length h) q hq
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

/-! ## The lift refines the eager form, and is boolean

On a row where the eager conjunction (disjunction) returns, the lift returns the
same (`Expr.andLift_refines`, `Expr.orLift_refines`); its value is TRUE, FALSE or
NULL (`Expr.andLift_boolVal`, `Expr.orLift_boolVal`), so a lift can be an operand
of another. -/

omit [Boxes.Ambient] in
theorem firstError_append_none {xs ys : List (Issue × Expr)}
    (h : firstError (xs ++ ys) = none) : firstError xs = none ∧ firstError ys = none := by
  rw [firstError_append] at h
  rcases hx : firstError xs with _ | k
  · rw [hx] at h; exact ⟨rfl, by simpa using h⟩
  · rw [hx] at h; simp at h

theorem firstError_flatMap_none_inv (row : Row) :
    ∀ qs : List Expr, firstError (qs.flatMap (·.issues row)) = none →
      ∀ q ∈ qs, firstError (q.issues row) = none
  | [], _, q, hq => by simp at hq
  | r :: qs, h, q, hq => by
    rw [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := firstError_append_none h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h1
    · exact firstError_flatMap_none_inv row qs h2 q hq

omit [Boxes.Ambient] in
theorem first_split {α : Type} (P : α → Prop) :
    ∀ l : List α, (∃ x ∈ l, P x) →
      ∃ pre x post, l = pre ++ x :: post ∧ (∀ y ∈ pre, ¬P y) ∧ P x
  | [], ⟨x, hx, _⟩ => by simp at hx
  | a :: l, h => by
    by_cases ha : P a
    · exact ⟨[], a, l, rfl, by simp, ha⟩
    · obtain ⟨x, hx, hPx⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact absurd hPx ha
      · obtain ⟨pre, y, post, hl, hpre, hy⟩ := first_split P l ⟨x, hx, hPx⟩
        refine ⟨a :: pre, y, post, by simp [hl], ?_, hy⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ha
        · exact hpre z hz

/-! ### The conjunction -/

omit [Boxes.Ambient] in
theorem and3_bool (a b : Value) : and3 a b = .null ∨ ∃ c, and3 a b = .bool c := by
  unfold and3; split <;> simp

omit [Boxes.Ambient] in
theorem and3_eq_neut {a b : Value} (h : and3 a b = .bool true) :
    a = .bool true ∧ b = .bool true := by
  unfold and3 at h; split at h <;> simp_all

omit [Boxes.Ambient] in
theorem and3_dom_left (v : Value) : and3 (.bool false) v = .bool false := by simp [and3]

theorem Expr.fold_and_dom (row : Row) : ∀ (ps : List Expr) (v : Value),
    (v = .bool false ∨ ∃ q ∈ ps, q.eval row = .bool false) →
    ps.foldl (fun v q => and3 v (q.eval row)) v = .bool false
  | [], v, h => by
    rcases h with h | ⟨q, hq, _⟩
    · exact h
    · simp at hq
  | q :: ps, v, h => by
    simp only [List.foldl_cons]
    apply Expr.fold_and_dom row ps
    rcases h with h | ⟨r, hr, hrq⟩
    · left; rw [h]; exact and3_dom_left _
    · rcases List.mem_cons.mp hr with rfl | hr'
      · left; rw [hrq]; exact and3_false_right v
      · right; exact ⟨r, hr', hrq⟩

theorem Expr.fold_and_neut (row : Row) : ∀ (ps : List Expr) (v : Value),
    v = .bool true → (∀ q ∈ ps, q.eval row = .bool true) →
    ps.foldl (fun v q => and3 v (q.eval row)) v = .bool true
  | [], v, h, _ => h
  | q :: ps, v, h, hq => by
    simp only [List.foldl_cons]
    apply Expr.fold_and_neut row ps
    · rw [h, hq q (by simp)]; simp [and3]
    · exact fun r hr => hq r (by simp [hr])

theorem Expr.fold_and_neut_inv (row : Row) : ∀ (ps : List Expr) (v : Value),
    ps.foldl (fun v q => and3 v (q.eval row)) v = .bool true →
    v = .bool true ∧ ∀ q ∈ ps, q.eval row = .bool true
  | [], v, h => ⟨h, by simp⟩
  | q :: ps, v, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := Expr.fold_and_neut_inv row ps _ h
    obtain ⟨h3, h4⟩ := and3_eq_neut h1
    refine ⟨h3, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h4
    · exact h2 r hr

theorem Expr.fold_and_boolval (row : Row) : ∀ (ps : List Expr) (v : Value),
    (v = .null ∨ ∃ c, v = .bool c) →
    (ps.foldl (fun v q => and3 v (q.eval row)) v = .null ∨
      ∃ c, ps.foldl (fun v q => and3 v (q.eval row)) v = .bool c)
  | [], v, h => h
  | q :: ps, v, _ => by
    simp only [List.foldl_cons]
    exact Expr.fold_and_boolval row ps _ (and3_bool _ _)

theorem Expr.conj_eval_dom (row : Row) (ps : List Expr)
    (h : ∃ q ∈ ps, q.eval row = .bool false) : (Expr.conj ps).eval row = .bool false := by
  cases ps with
  | nil => obtain ⟨q, hq, _⟩ := h; simp at hq
  | cons p ps =>
    simp only [Expr.conj, Expr.eval_foldl_and]
    apply Expr.fold_and_dom
    obtain ⟨q, hq, hqe⟩ := h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact .inl hqe
    · exact .inr ⟨q, hq, hqe⟩

theorem Expr.conj_eval_neut (row : Row) (ps : List Expr)
    (h : ∀ q ∈ ps, q.eval row = .bool true) : (Expr.conj ps).eval row = .bool true := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    simp only [Expr.conj, Expr.eval_foldl_and]
    exact Expr.fold_and_neut row ps _ (h p (by simp)) (fun q hq => h q (by simp [hq]))

theorem Expr.conj_eval_go (row : Row) (ps : List Expr) (h : ∀ q ∈ ps, Expr.Go row q) :
    (Expr.conj ps).eval row = .null ∨ (Expr.conj ps).eval row = .bool true := by
  cases ps with
  | nil => exact .inr rfl
  | cons p ps =>
    simp only [Expr.conj, Expr.eval_foldl_and]
    obtain ⟨-, hnf, hbv⟩ := h p (by simp)
    refine Expr.fold_and_go ps _ ?_ (fun q hq => h q (by simp [hq]))
    rcases hbv with hq | ⟨b, hq⟩
    · exact .inl hq
    · cases b with
      | false => exact absurd hq hnf
      | true => exact .inr hq

theorem Expr.conj_eval_null (row : Row) (ps : List Expr) (h : ∀ q ∈ ps, Expr.Go row q)
    (hne : ¬ ∀ q ∈ ps, q.eval row = .bool true) : (Expr.conj ps).eval row = .null := by
  rcases Expr.conj_eval_go row ps h with hn | ht
  · exact hn
  · exfalso
    apply hne
    cases ps with
    | nil => simp
    | cons p ps =>
      simp only [Expr.conj, Expr.eval_foldl_and] at ht
      obtain ⟨h1, h2⟩ := Expr.fold_and_neut_inv row ps _ ht
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h1
      · exact h2 q hq

theorem Expr.conj_firstError_none (row : Row) (ps : List Expr)
    (h : ∀ q ∈ ps, firstError (q.issues row) = none) :
    firstError ((Expr.conj ps).issues row) = none := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    simp only [Expr.conj, Expr.issues_foldl_and, firstError_append, h p (by simp), Option.none_or]
    exact Expr.firstError_flatMap_none row ps (fun q hq => h q (by simp [hq]))

theorem Expr.conj_firstError_none_inv (row : Row) (ps : List Expr)
    (h : firstError ((Expr.conj ps).issues row) = none) :
    ∀ q ∈ ps, firstError (q.issues row) = none := by
  cases ps with
  | nil => intro q hq; simp at hq
  | cons p ps =>
    simp only [Expr.conj, Expr.issues_foldl_and] at h
    obtain ⟨h1, h2⟩ := firstError_append_none h
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h1
    · exact firstError_flatMap_none_inv row ps h2 q hq

/-- The guarded conjunction has the eager one's outcome where no operand raises. -/
theorem Expr.andG_outcome (row : Row) (ps : List Expr)
    (hno : ∀ q ∈ ps, firstError (q.issues row) = none) (hbv : ∀ q ∈ ps, Expr.BoolVal row q)
    (hne : ps ≠ []) :
    (Expr.andG ps).refOutcome row = (Expr.conj ps).refOutcome row := by
  by_cases hex : ∃ q ∈ ps, q.eval row = .bool false
  · obtain ⟨pre, p, post, rfl, hpre, hp⟩ := first_split _ ps hex
    have hGo : ∀ q ∈ pre, Expr.Go row q :=
      fun q hq => ⟨hno q (by simp [hq]), hpre q hq, hbv q (by simp [hq])⟩
    have h1 := Expr.andG_false row pre p post hGo (hno p (by simp)) (hbv p (by simp)) hp
    have h2 : (Expr.conj (pre ++ p :: post)).refOutcome row = .ok (.bool false) := by
      have hfe := Expr.conj_firstError_none row (pre ++ p :: post) hno
      have hev := Expr.conj_eval_dom row (pre ++ p :: post) ⟨p, by simp, hp⟩
      simp [Expr.refOutcome, hfe, hev]
    rw [h1, h2]
  · have hex' : ∀ q ∈ ps, q.eval row ≠ .bool false := fun q hq h => hex ⟨q, hq, h⟩
    cases ps with
    | nil => exact absurd rfl hne
    | cons p ps => exact Expr.andG_none row p ps (fun q hq => ⟨hno q hq, hex' q hq, hbv q hq⟩)

/-- The plain operands' conjunction, ANDed with the guarded one, has the eager value. -/
theorem Expr.and_plains_value (row : Row) (ps : List Expr)
    (hno : ∀ q ∈ ps, firstError (q.issues row) = none) (hbv : ∀ q ∈ ps, Expr.BoolVal row q) :
    and3 ((Expr.conj (ps.filter Expr.plain)).eval row) ((Expr.conj ps).eval row) =
      (Expr.conj ps).eval row := by
  by_cases hA : ∃ q ∈ ps, q.eval row = .bool false
  · rw [Expr.conj_eval_dom row ps hA]; exact and3_false_right _
  · have hA' : ∀ q ∈ ps, q.eval row ≠ .bool false := fun q hq h => hA ⟨q, hq, h⟩
    have hGo : ∀ q ∈ ps, Expr.Go row q := fun q hq => ⟨hno q hq, hA' q hq, hbv q hq⟩
    have hplGo : ∀ q ∈ ps.filter Expr.plain, Expr.Go row q := fun q hq => hGo q (List.mem_filter.mp hq).1
    by_cases hB : ∀ q ∈ ps, q.eval row = .bool true
    · rw [Expr.conj_eval_neut row ps hB,
        Expr.conj_eval_neut row _ (fun q hq => hB q (List.mem_filter.mp hq).1)]
      simp [and3]
    · rw [Expr.conj_eval_null row ps hGo hB]
      rcases Expr.conj_eval_go row _ hplGo with hd | hd <;> simp [hd, and3]

/-- **The lift refines the eager conjunction** (D50's first statement): on a row where
the eager conjunction returns, the lift returns the same. -/
theorem Expr.andLift_refines (row : Row) (ps : List Expr) (v : Value)
    (hbv : ∀ q ∈ ps, Expr.BoolVal row q) (h : (Expr.conj ps).refOutcome row = .ok v) :
    (Expr.andLift ps).refOutcome row = .ok v := by
  have hfe : firstError ((Expr.conj ps).issues row) = none := by
    unfold Expr.refOutcome at h
    split at h
    · cases h
    · assumption
  have hv : (Expr.conj ps).eval row = v := by
    unfold Expr.refOutcome at h
    rw [hfe] at h
    simpa using h
  have hno := Expr.conj_firstError_none_inv row ps hfe
  unfold Expr.andLift
  dsimp only
  split
  · exact h
  · next hlen =>
    have hne : ps ≠ [] := by rintro rfl; simp at hlen
    have hG := Expr.andG_outcome row ps hno hbv hne
    split
    · rw [hG]; exact h
    · have hi := Expr.conj_plain_issues row (ps.filter Expr.plain) (Expr.filter_plain_plain _)
      have hGok : (Expr.andG ps).refOutcome row = .ok v := by rw [hG]; exact h
      unfold Expr.refOutcome at hGok
      split at hGok
      · cases hGok
      · next hn =>
        have hev : (Expr.andG ps).eval row = v := by simpa using hGok
        have hne' : firstError ((Expr.bin .and (Expr.conj (ps.filter Expr.plain)) (Expr.andG ps)).issues row) = none := by
          simp [Expr.issues, hi, hn]
        have hval := Expr.and_plains_value row ps hno hbv
        rw [hv] at hval
        unfold Expr.refOutcome
        rw [hne']
        simp only [Expr.eval, Impl.lean, BinFn.apply, hev, hval]

theorem Expr.andChain_vals (row : Row) (all : Expr) : ∀ ps : List Expr,
    (Expr.andChain all ps).eval row = .int 0 ∨ (Expr.andChain all ps).eval row = .int 1 ∨
      (Expr.andChain all ps).eval row = .null
  | [] => by
    simp only [Expr.andChain, Expr.eval]; split <;> simp
  | p :: ps => by
    simp only [Expr.andChain, Expr.eval]
    split
    · exact Expr.andChain_vals row all ps
    · simp

theorem Expr.andG_boolVal (row : Row) (ps : List Expr) : Expr.BoolVal row (Expr.andG ps) := by
  rcases Expr.andChain_vals row (Expr.conj ps) ps with h | h | h <;>
    simp [Expr.BoolVal, Expr.andG, Expr.eval, Impl.lean, BinFn.apply, Value.numPair, h]

/-- **The lift is boolean**: its value is TRUE, FALSE or NULL, so it can be an operand. -/
theorem Expr.andLift_boolVal (row : Row) (ps : List Expr)
    (hbv : ∀ q ∈ ps, Expr.BoolVal row q) : Expr.BoolVal row (Expr.andLift ps) := by
  unfold Expr.andLift
  dsimp only
  split
  · cases ps with
    | nil => exact .inr ⟨true, rfl⟩
    | cons p ps =>
      simp only [Expr.BoolVal, Expr.conj, Expr.eval_foldl_and]
      exact Expr.fold_and_boolval row ps _ (hbv p (by simp))
  · split
    · exact Expr.andG_boolVal row ps
    · simp only [Expr.BoolVal, Expr.eval, Impl.lean, BinFn.apply]
      exact and3_bool _ _

/-! ### The disjunction -/

omit [Boxes.Ambient] in
theorem or3_bool (a b : Value) : or3 a b = .null ∨ ∃ c, or3 a b = .bool c := by
  unfold or3; split <;> simp

omit [Boxes.Ambient] in
theorem or3_eq_neut {a b : Value} (h : or3 a b = .bool false) :
    a = .bool false ∧ b = .bool false := by
  unfold or3 at h; split at h <;> simp_all

omit [Boxes.Ambient] in
theorem or3_dom_left (v : Value) : or3 (.bool true) v = .bool true := by simp [or3]

theorem Expr.fold_or_dom (row : Row) : ∀ (ps : List Expr) (v : Value),
    (v = .bool true ∨ ∃ q ∈ ps, q.eval row = .bool true) →
    ps.foldl (fun v q => or3 v (q.eval row)) v = .bool true
  | [], v, h => by
    rcases h with h | ⟨q, hq, _⟩
    · exact h
    · simp at hq
  | q :: ps, v, h => by
    simp only [List.foldl_cons]
    apply Expr.fold_or_dom row ps
    rcases h with h | ⟨r, hr, hrq⟩
    · left; rw [h]; exact or3_dom_left _
    · rcases List.mem_cons.mp hr with rfl | hr'
      · left; rw [hrq]; exact or3_true_right v
      · right; exact ⟨r, hr', hrq⟩

theorem Expr.fold_or_neut (row : Row) : ∀ (ps : List Expr) (v : Value),
    v = .bool false → (∀ q ∈ ps, q.eval row = .bool false) →
    ps.foldl (fun v q => or3 v (q.eval row)) v = .bool false
  | [], v, h, _ => h
  | q :: ps, v, h, hq => by
    simp only [List.foldl_cons]
    apply Expr.fold_or_neut row ps
    · rw [h, hq q (by simp)]; simp [or3]
    · exact fun r hr => hq r (by simp [hr])

theorem Expr.fold_or_neut_inv (row : Row) : ∀ (ps : List Expr) (v : Value),
    ps.foldl (fun v q => or3 v (q.eval row)) v = .bool false →
    v = .bool false ∧ ∀ q ∈ ps, q.eval row = .bool false
  | [], v, h => ⟨h, by simp⟩
  | q :: ps, v, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := Expr.fold_or_neut_inv row ps _ h
    obtain ⟨h3, h4⟩ := or3_eq_neut h1
    refine ⟨h3, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h4
    · exact h2 r hr

theorem Expr.fold_or_boolval (row : Row) : ∀ (ps : List Expr) (v : Value),
    (v = .null ∨ ∃ c, v = .bool c) →
    (ps.foldl (fun v q => or3 v (q.eval row)) v = .null ∨
      ∃ c, ps.foldl (fun v q => or3 v (q.eval row)) v = .bool c)
  | [], v, h => h
  | q :: ps, v, _ => by
    simp only [List.foldl_cons]
    exact Expr.fold_or_boolval row ps _ (or3_bool _ _)

theorem Expr.disj_eval_dom (row : Row) (ps : List Expr)
    (h : ∃ q ∈ ps, q.eval row = .bool true) : (Expr.disj ps).eval row = .bool true := by
  cases ps with
  | nil => obtain ⟨q, hq, _⟩ := h; simp at hq
  | cons p ps =>
    simp only [Expr.disj, Expr.eval_foldl_or]
    apply Expr.fold_or_dom
    obtain ⟨q, hq, hqe⟩ := h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact .inl hqe
    · exact .inr ⟨q, hq, hqe⟩

theorem Expr.disj_eval_neut (row : Row) (ps : List Expr)
    (h : ∀ q ∈ ps, q.eval row = .bool false) : (Expr.disj ps).eval row = .bool false := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    simp only [Expr.disj, Expr.eval_foldl_or]
    exact Expr.fold_or_neut row ps _ (h p (by simp)) (fun q hq => h q (by simp [hq]))

theorem Expr.disj_eval_go (row : Row) (ps : List Expr) (h : ∀ q ∈ ps, Expr.GoOr row q) :
    (Expr.disj ps).eval row = .null ∨ (Expr.disj ps).eval row = .bool false := by
  cases ps with
  | nil => exact .inr rfl
  | cons p ps =>
    simp only [Expr.disj, Expr.eval_foldl_or]
    obtain ⟨-, hnf, hbv⟩ := h p (by simp)
    refine Expr.fold_or_go ps _ ?_ (fun q hq => h q (by simp [hq]))
    rcases hbv with hq | ⟨b, hq⟩
    · exact .inl hq
    · cases b with
      | true => exact absurd hq hnf
      | false => exact .inr hq

theorem Expr.disj_eval_null (row : Row) (ps : List Expr) (h : ∀ q ∈ ps, Expr.GoOr row q)
    (hne : ¬ ∀ q ∈ ps, q.eval row = .bool false) : (Expr.disj ps).eval row = .null := by
  rcases Expr.disj_eval_go row ps h with hn | ht
  · exact hn
  · exfalso
    apply hne
    cases ps with
    | nil => simp
    | cons p ps =>
      simp only [Expr.disj, Expr.eval_foldl_or] at ht
      obtain ⟨h1, h2⟩ := Expr.fold_or_neut_inv row ps _ ht
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h1
      · exact h2 q hq

theorem Expr.disj_firstError_none (row : Row) (ps : List Expr)
    (h : ∀ q ∈ ps, firstError (q.issues row) = none) :
    firstError ((Expr.disj ps).issues row) = none := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    simp only [Expr.disj, Expr.issues_foldl_or, firstError_append, h p (by simp), Option.none_or]
    exact Expr.firstError_flatMap_none row ps (fun q hq => h q (by simp [hq]))

theorem Expr.disj_firstError_none_inv (row : Row) (ps : List Expr)
    (h : firstError ((Expr.disj ps).issues row) = none) :
    ∀ q ∈ ps, firstError (q.issues row) = none := by
  cases ps with
  | nil => intro q hq; simp at hq
  | cons p ps =>
    simp only [Expr.disj, Expr.issues_foldl_or] at h
    obtain ⟨h1, h2⟩ := firstError_append_none h
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h1
    · exact firstError_flatMap_none_inv row ps h2 q hq

/-- The guarded disjunction has the eager one's outcome where no operand raises. -/
theorem Expr.orG_outcome (row : Row) (ps : List Expr)
    (hno : ∀ q ∈ ps, firstError (q.issues row) = none) (hbv : ∀ q ∈ ps, Expr.BoolVal row q)
    (hne : ps ≠ []) :
    (Expr.orG ps).refOutcome row = (Expr.disj ps).refOutcome row := by
  by_cases hex : ∃ q ∈ ps, q.eval row = .bool true
  · obtain ⟨pre, p, post, rfl, hpre, hp⟩ := first_split _ ps hex
    have hGo : ∀ q ∈ pre, Expr.GoOr row q :=
      fun q hq => ⟨hno q (by simp [hq]), hpre q hq, hbv q (by simp [hq])⟩
    have h1 := Expr.orG_true row pre p post hGo (hno p (by simp)) (hbv p (by simp)) hp
    have h2 : (Expr.disj (pre ++ p :: post)).refOutcome row = .ok (.bool true) := by
      have hfe := Expr.disj_firstError_none row (pre ++ p :: post) hno
      have hev := Expr.disj_eval_dom row (pre ++ p :: post) ⟨p, by simp, hp⟩
      simp [Expr.refOutcome, hfe, hev]
    rw [h1, h2]
  · have hex' : ∀ q ∈ ps, q.eval row ≠ .bool true := fun q hq h => hex ⟨q, hq, h⟩
    cases ps with
    | nil => exact absurd rfl hne
    | cons p ps => exact Expr.orG_none row p ps (fun q hq => ⟨hno q hq, hex' q hq, hbv q hq⟩)

/-- The plain operands' disjunction, ANDed with the guarded one, has the eager value. -/
theorem Expr.or_plains_value (row : Row) (ps : List Expr)
    (hno : ∀ q ∈ ps, firstError (q.issues row) = none) (hbv : ∀ q ∈ ps, Expr.BoolVal row q) :
    or3 ((Expr.disj (ps.filter Expr.plain)).eval row) ((Expr.disj ps).eval row) =
      (Expr.disj ps).eval row := by
  by_cases hA : ∃ q ∈ ps, q.eval row = .bool true
  · rw [Expr.disj_eval_dom row ps hA]; exact or3_true_right _
  · have hA' : ∀ q ∈ ps, q.eval row ≠ .bool true := fun q hq h => hA ⟨q, hq, h⟩
    have hGo : ∀ q ∈ ps, Expr.GoOr row q := fun q hq => ⟨hno q hq, hA' q hq, hbv q hq⟩
    have hplGo : ∀ q ∈ ps.filter Expr.plain, Expr.GoOr row q := fun q hq => hGo q (List.mem_filter.mp hq).1
    by_cases hB : ∀ q ∈ ps, q.eval row = .bool false
    · rw [Expr.disj_eval_neut row ps hB,
        Expr.disj_eval_neut row _ (fun q hq => hB q (List.mem_filter.mp hq).1)]
      simp [or3]
    · rw [Expr.disj_eval_null row ps hGo hB]
      rcases Expr.disj_eval_go row _ hplGo with hd | hd <;> simp [hd, or3]

/-- **The lift refines the eager disjunction** (D50's first statement): on a row where
the eager disjunction returns, the lift returns the same. -/
theorem Expr.orLift_refines (row : Row) (ps : List Expr) (v : Value)
    (hbv : ∀ q ∈ ps, Expr.BoolVal row q) (h : (Expr.disj ps).refOutcome row = .ok v) :
    (Expr.orLift ps).refOutcome row = .ok v := by
  have hfe : firstError ((Expr.disj ps).issues row) = none := by
    unfold Expr.refOutcome at h
    split at h
    · cases h
    · assumption
  have hv : (Expr.disj ps).eval row = v := by
    unfold Expr.refOutcome at h
    rw [hfe] at h
    simpa using h
  have hno := Expr.disj_firstError_none_inv row ps hfe
  unfold Expr.orLift
  dsimp only
  split
  · exact h
  · next hlen =>
    have hne : ps ≠ [] := by rintro rfl; simp at hlen
    have hG := Expr.orG_outcome row ps hno hbv hne
    split
    · rw [hG]; exact h
    · have hi := Expr.disj_plain_issues row (ps.filter Expr.plain) (Expr.filter_plain_plain _)
      have hGok : (Expr.orG ps).refOutcome row = .ok v := by rw [hG]; exact h
      unfold Expr.refOutcome at hGok
      split at hGok
      · cases hGok
      · next hn =>
        have hev : (Expr.orG ps).eval row = v := by simpa using hGok
        have hne' : firstError ((Expr.bin .or (Expr.disj (ps.filter Expr.plain)) (Expr.orG ps)).issues row) = none := by
          simp [Expr.issues, hi, hn]
        have hval := Expr.or_plains_value row ps hno hbv
        rw [hv] at hval
        unfold Expr.refOutcome
        rw [hne']
        simp only [Expr.eval, Impl.lean, BinFn.apply, hev, hval]

theorem Expr.orChain_vals (row : Row) (all : Expr) : ∀ ps : List Expr,
    (Expr.orChain all ps).eval row = .int 0 ∨ (Expr.orChain all ps).eval row = .int 1 ∨
      (Expr.orChain all ps).eval row = .null
  | [] => by
    simp only [Expr.orChain, Expr.eval]
    by_cases hc : (UnFn.not.apply (Expr.eval row all)).isTrue = true <;> simp [hc]
  | p :: ps => by
    simp only [Expr.orChain, Expr.eval]
    split
    · exact Expr.orChain_vals row all ps
    · simp

theorem Expr.orG_boolVal (row : Row) (ps : List Expr) : Expr.BoolVal row (Expr.orG ps) := by
  rcases Expr.orChain_vals row (Expr.disj ps) ps with h | h | h <;>
    simp [Expr.BoolVal, Expr.orG, Expr.eval, Impl.lean, BinFn.apply, Value.numPair, h]

/-- **The lift is boolean**: its value is TRUE, FALSE or NULL, so it can be an operand. -/
theorem Expr.orLift_boolVal (row : Row) (ps : List Expr)
    (hbv : ∀ q ∈ ps, Expr.BoolVal row q) : Expr.BoolVal row (Expr.orLift ps) := by
  unfold Expr.orLift
  dsimp only
  split
  · cases ps with
    | nil => exact .inr ⟨false, rfl⟩
    | cons p ps =>
      simp only [Expr.BoolVal, Expr.disj, Expr.eval_foldl_or]
      exact Expr.fold_or_boolval row ps _ (hbv p (by simp))
  · split
    · exact Expr.orG_boolVal row ps
    · simp only [Expr.BoolVal, Expr.eval, Impl.lean, BinFn.apply]
      exact or3_bool _ _


/-! ## The lift's value (D50-d)

On a row where every operand is TRUE, FALSE or NULL, the lift has the eager
conjunction's value, whatever its operands raise: evaluation computes each
operand it reaches, and an operand it does not reach follows a FALSE (a TRUE
for `OR`), which decides the result. This holds under any `Impl` whose
logical functions are the reference's (`Impl.Logic`): `Impl.lean`, and the
reference profile's, which gives an error NULL. The binder (`Bind.lean`) goes
through these and the lemmas above, never through `andChain`'s shape (ruling
183, O1). -/

/-- The reference's logical functions: `IS NULL`, `NOT`, `AND`, `OR`, and `=`
against the lift's code `1`. -/
structure Impl.Logic (I : Impl) : Prop where
  isNull : ∀ v, I.un .isNull v = UnFn.apply .isNull v
  not : ∀ v, I.un .not v = UnFn.apply .not v
  and : ∀ v w, I.bin .and v w = and3 v w
  or : ∀ v w, I.bin .or v w = or3 v w
  eq : ∀ v, I.bin .eq v (.int 1) = BinFn.apply .eq v (.int 1)

theorem Impl.lean_logic : Impl.lean.Logic :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem Profile.reference_logic : Profile.reference.impl.Logic := by
  have hu (f : UnFn) (v : Value) (h : f.issueAll v = none) :
      Profile.reference.impl.un f v = f.apply v := by
    have : f.issue v = none := by
      simp only [UnFn.issueAll, Option.or_eq_none_iff] at h; exact h.1
    simp [Profile.impl, Profile.reference, this, raiseIf, Outcome.val]
  have hb (f : BinFn) (v w : Value) (h : f.issueAll v w = none) :
      Profile.reference.impl.bin f v w = f.apply v w := by
    have : f.issue v w = none := by
      simp only [BinFn.issueAll, Option.or_eq_none_iff] at h; exact h.1
    simp [Profile.impl, Profile.reference, this, raiseIf, Outcome.val]
  exact ⟨fun v => hu _ v (by simp), fun v => hu _ v (by simp), fun v w => hb _ v w (by simp),
    fun v w => hb _ v w (by simp), fun v => hb _ v _ (by simp)⟩

/-- `p`'s value under `I` is TRUE, FALSE or NULL. -/
def Expr.BoolValI (I : Impl) (row : Row) (p : Expr) : Prop :=
  p.eval row I = .null ∨ ∃ b, p.eval row I = .bool b

/-- A value TRUE, FALSE or NULL. -/
def Value.IsBool (v : Value) : Prop := v = .null ∨ ∃ b, v = .bool b

omit [Boxes.Ambient] in
/-- A left fold of `AND` over values that are TRUE, FALSE or NULL, by cases. -/
theorem foldl_and3_cases : ∀ (vs : List Value) (a : Value), a.IsBool → (∀ x ∈ vs, x.IsBool) →
    vs.foldl and3 a =
      if a = .bool false ∨ .bool false ∈ vs then .bool false
      else if a = .bool true ∧ ∀ x ∈ vs, x = .bool true then .bool true else .null
  | [], a, ha, _ => by
    rcases ha with rfl | ⟨b, rfl⟩
    · simp
    · cases b <;> simp
  | v :: vs, a, ha, hvs => by
    simp only [List.foldl_cons]
    have hv := hvs v (by simp)
    rw [foldl_and3_cases vs (and3 a v) (and3_bool a v) (fun x hx => hvs x (by simp [hx]))]
    rcases ha with rfl | ⟨b, rfl⟩ <;> rcases hv with rfl | ⟨c, rfl⟩ <;>
      (try cases b) <;> (try cases c) <;> simp [and3]

omit [Boxes.Ambient] in
/-- A left fold of `OR`, dually. -/
theorem foldl_or3_cases : ∀ (vs : List Value) (a : Value), a.IsBool → (∀ x ∈ vs, x.IsBool) →
    vs.foldl or3 a =
      if a = .bool true ∨ .bool true ∈ vs then .bool true
      else if a = .bool false ∧ ∀ x ∈ vs, x = .bool false then .bool false else .null
  | [], a, ha, _ => by
    rcases ha with rfl | ⟨b, rfl⟩
    · simp
    · cases b <;> simp
  | v :: vs, a, ha, hvs => by
    simp only [List.foldl_cons]
    have hv := hvs v (by simp)
    rw [foldl_or3_cases vs (or3 a v) (or3_bool a v) (fun x hx => hvs x (by simp [hx]))]
    rcases ha with rfl | ⟨b, rfl⟩ <;> rcases hv with rfl | ⟨c, rfl⟩ <;>
      (try cases b) <;> (try cases c) <;> simp [or3]

/-- The eager conjunction's value under `I`, by cases on its operands' values. -/
theorem Expr.conj_evalI {I : Impl} (hI : I.Logic) (row : Row) (ps : List Expr)
    (hb : ∀ q ∈ ps, Expr.BoolValI I row q) :
    (Expr.conj ps).eval row I =
      if .bool false ∈ ps.map (·.eval row I) then .bool false
      else if ∀ x ∈ ps.map (·.eval row I), x = .bool true then .bool true else .null := by
  cases ps with
  | nil => simp [Expr.conj, Expr.eval]
  | cons p ps =>
    have hfold : ∀ (acc : Expr) (qs : List Expr), (qs.foldl (.bin .and) acc).eval row I =
        (qs.map (·.eval row I)).foldl and3 (acc.eval row I) := by
      intro acc qs
      induction qs generalizing acc with
      | nil => rfl
      | cons q qs ih => simp only [List.foldl_cons, ih, Expr.eval, hI.and, List.map_cons]
    simp only [Expr.conj, hfold]
    rw [foldl_and3_cases _ _ (hb p (by simp)) (by
      intro x hx; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx; exact hb q (by simp [hq]))]
    simp [@eq_comm _ (Value.bool false)]

/-- The eager disjunction's value under `I`, by cases. -/
theorem Expr.disj_evalI {I : Impl} (hI : I.Logic) (row : Row) (ps : List Expr)
    (hb : ∀ q ∈ ps, Expr.BoolValI I row q) :
    (Expr.disj ps).eval row I =
      if .bool true ∈ ps.map (·.eval row I) then .bool true
      else if ∀ x ∈ ps.map (·.eval row I), x = .bool false then .bool false else .null := by
  cases ps with
  | nil => simp [Expr.disj, Expr.eval]
  | cons p ps =>
    have hfold : ∀ (acc : Expr) (qs : List Expr), (qs.foldl (.bin .or) acc).eval row I =
        (qs.map (·.eval row I)).foldl or3 (acc.eval row I) := by
      intro acc qs
      induction qs generalizing acc with
      | nil => rfl
      | cons q qs ih => simp only [List.foldl_cons, ih, Expr.eval, hI.or, List.map_cons]
    simp only [Expr.disj, hfold]
    rw [foldl_or3_cases _ _ (hb p (by simp)) (by
      intro x hx; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx; exact hb q (by simp [hq]))]
    simp [@eq_comm _ (Value.bool true)]

theorem Expr.andChain_evalI {I : Impl} (hI : I.Logic) (row : Row) (all : Expr) : ∀ ps : List Expr,
    (∀ q ∈ ps, Expr.BoolValI I row q) →
    (Expr.andChain all ps).eval row I =
      if .bool false ∈ ps.map (·.eval row I) then .int 0
      else if (all.eval row I).isTrue then .int 1 else .null
  | [], _ => by simp [Expr.andChain, Expr.eval]
  | p :: ps, hb => by
    have ih := Expr.andChain_evalI hI row all ps (fun q hq => hb q (by simp [hq]))
    simp only [Expr.andChain, Expr.eval, List.map_cons, List.mem_cons]
    have hnf : (Expr.notFalse p).eval row I =
        or3 (UnFn.apply .isNull (p.eval row I)) (p.eval row I) := by
      simp [Expr.notFalse, Expr.eval, hI.or, hI.isNull]
    rw [hnf, ih]
    rcases hb p (by simp) with h | ⟨b, h⟩ <;> rw [h]
    · simp [UnFn.apply, or3, Value.isTrue]
    · cases b <;> simp [UnFn.apply, or3, Value.isTrue]

theorem Expr.orChain_evalI {I : Impl} (hI : I.Logic) (row : Row) (all : Expr) : ∀ ps : List Expr,
    (∀ q ∈ ps, Expr.BoolValI I row q) →
    (Expr.orChain all ps).eval row I =
      if .bool true ∈ ps.map (·.eval row I) then .int 1
      else if (UnFn.apply .not (all.eval row I)).isTrue then .int 0 else .null
  | [], _ => by simp [Expr.orChain, Expr.eval, hI.not]
  | p :: ps, hb => by
    have ih := Expr.orChain_evalI hI row all ps (fun q hq => hb q (by simp [hq]))
    simp only [Expr.orChain, Expr.eval, List.map_cons, List.mem_cons]
    have hnt : (Expr.notTrue p).eval row I =
        or3 (UnFn.apply .isNull (p.eval row I)) (UnFn.apply .not (p.eval row I)) := by
      simp [Expr.notTrue, Expr.eval, hI.or, hI.isNull, hI.not]
    rw [hnt, ih]
    rcases hb p (by simp) with h | ⟨b, h⟩ <;> rw [h]
    · simp [UnFn.apply, or3, Value.isTrue]
    · cases b <;> simp [UnFn.apply, or3, Value.isTrue]

/-- **The `AND` lift has the eager conjunction's value** under `I`, on a row
where every operand is TRUE, FALSE or NULL. -/
theorem Expr.andLift_evalI {I : Impl} (hI : I.Logic) (row : Row) (ps : List Expr)
    (hb : ∀ q ∈ ps, Expr.BoolValI I row q) :
    (Expr.andLift ps).eval row I = (Expr.conj ps).eval row I := by
  have hc := Expr.conj_evalI hI row ps hb
  have hg : (Expr.andG ps).eval row I = (Expr.conj ps).eval row I := by
    simp only [Expr.andG, Expr.eval, hI.eq]
    rw [Expr.andChain_evalI hI row _ ps hb, hc]
    split
    · rfl
    · split <;> rfl
  have hpl : ∀ q ∈ ps.filter Expr.plain, Expr.BoolValI I row q :=
    fun q hq => hb q (List.mem_filter.mp hq).1
  unfold Expr.andLift
  dsimp only
  split
  · rfl
  · split
    · exact hg
    · simp only [Expr.eval, hI.and]
      rw [hg, Expr.conj_evalI hI row _ hpl, hc]
      have hsub : ∀ x ∈ (ps.filter Expr.plain).map (·.eval row I), x ∈ ps.map (·.eval row I) := by
        intro x hx; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact List.mem_map.mpr ⟨q, (List.mem_filter.mp hq).1, rfl⟩
      by_cases hf : Value.bool false ∈ ps.map (·.eval row I)
      · simp only [hf, ↓reduceIte]; exact and3_false_right _
      · have hf' : Value.bool false ∉ (ps.filter Expr.plain).map (·.eval row I) := fun h => hf (hsub _ h)
        simp only [hf, hf', ↓reduceIte]
        by_cases ht : ∀ x ∈ ps.map (·.eval row I), x = .bool true
        · have ht' : ∀ x ∈ (ps.filter Expr.plain).map (·.eval row I), x = .bool true :=
            fun x hx => ht x (hsub x hx)
          rw [ite_eq_left_of_eq_true _ _ (eq_true ht), ite_eq_left_of_eq_true _ _ (eq_true ht')]; rfl
        · simp only [ht, ↓reduceIte]
          split <;> simp [and3]

/-- **The `OR` lift has the eager disjunction's value** under `I`. -/
theorem Expr.orLift_evalI {I : Impl} (hI : I.Logic) (row : Row) (ps : List Expr)
    (hb : ∀ q ∈ ps, Expr.BoolValI I row q) :
    (Expr.orLift ps).eval row I = (Expr.disj ps).eval row I := by
  have hc := Expr.disj_evalI hI row ps hb
  have hg : (Expr.orG ps).eval row I = (Expr.disj ps).eval row I := by
    simp only [Expr.orG, Expr.eval, hI.eq]
    rw [Expr.orChain_evalI hI row _ ps hb, hc]
    split
    · rfl
    · by_cases hf : ∀ x ∈ ps.map (·.eval row I), x = .bool false
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hf)]; rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hf)]; rfl
  have hpl : ∀ q ∈ ps.filter Expr.plain, Expr.BoolValI I row q :=
    fun q hq => hb q (List.mem_filter.mp hq).1
  unfold Expr.orLift
  dsimp only
  split
  · rfl
  · split
    · exact hg
    · simp only [Expr.eval, hI.or]
      rw [hg, Expr.disj_evalI hI row _ hpl, hc]
      have hsub : ∀ x ∈ (ps.filter Expr.plain).map (·.eval row I), x ∈ ps.map (·.eval row I) := by
        intro x hx; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact List.mem_map.mpr ⟨q, (List.mem_filter.mp hq).1, rfl⟩
      by_cases ht : Value.bool true ∈ ps.map (·.eval row I)
      · simp only [ht, ↓reduceIte]; exact or3_true_right _
      · have ht' : Value.bool true ∉ (ps.filter Expr.plain).map (·.eval row I) := fun h => ht (hsub _ h)
        simp only [ht, ht', ↓reduceIte]
        by_cases hf : ∀ x ∈ ps.map (·.eval row I), x = .bool false
        · have hf' : ∀ x ∈ (ps.filter Expr.plain).map (·.eval row I), x = .bool false :=
            fun x hx => hf x (hsub x hx)
          rw [ite_eq_left_of_eq_true _ _ (eq_true hf), ite_eq_left_of_eq_true _ _ (eq_true hf')]; rfl
        · simp only [hf, ↓reduceIte]
          split <;> simp [or3]

/-! ## Where the lift raises (D50-d)

The lift raises exactly where some operand raises after operands that all go
on (`Expr.Go`: no raise, not FALSE). From `andLift_error`, `andLift_false` and
`andLift_refines` alone. -/

omit [Boxes.Ambient] in
/-- A list's first element without `P`, if any. -/
theorem List.first_not {α : Type} (P : α → Prop) : ∀ l : List α,
    (∀ x ∈ l, P x) ∨ ∃ pre q post, l = pre ++ q :: post ∧ (∀ x ∈ pre, P x) ∧ ¬ P q
  | [] => .inl (by simp)
  | a :: l => by
    by_cases ha : P a
    · rcases List.first_not P l with h | ⟨pre, q, post, rfl, hpre, hq⟩
      · exact .inl fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact h x hx
      · exact .inr ⟨a :: pre, q, post, rfl, fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hpre x hx, hq⟩
    · exact .inr ⟨[], a, l, rfl, by simp, ha⟩

theorem Expr.refOutcome_isSome (row : Row) (e : Expr) :
    (firstError (e.issues row)).isSome ↔ ∃ k, e.refOutcome row = .error k := by
  unfold Expr.refOutcome
  cases firstError (e.issues row) <;> simp

/-- **Where the `AND` lift raises**: an operand raises, and every operand
before it goes on. -/
theorem Expr.andLift_raises_iff (row : Row) (ps : List Expr)
    (hbv : ∀ q ∈ ps, firstError (q.issues row) = none → Expr.BoolVal row q) :
    (firstError ((Expr.andLift ps).issues row)).isSome ↔
      ∃ pre p post, ps = pre ++ p :: post ∧ (∀ q ∈ pre, Expr.Go row q) ∧
        (firstError (p.issues row)).isSome := by
  by_cases hnp : ∃ q ∈ ps, q.plain = false
  · constructor
    · intro h
      rw [Expr.refOutcome_isSome] at h
      obtain ⟨k, hk⟩ := h
      rcases List.first_not (Expr.Go row) ps with hall | ⟨pre, p, post, rfl, hpre, hp⟩
      · exfalso
        have hn : firstError ((Expr.conj ps).issues row) = none :=
          Expr.conj_firstError_none row ps (fun q hq => (hall q hq).1)
        have hok : (Expr.conj ps).refOutcome row = .ok ((Expr.conj ps).eval row) := by
          unfold Expr.refOutcome; rw [hn]
        rw [Expr.andLift_refines row ps _ (fun q hq => (hall q hq).2.2) hok] at hk
        cases hk
      · by_cases hpr : firstError (p.issues row) = none
        · exfalso
          have hb := hbv p (by simp) hpr
          have hf : p.eval row = .bool false :=
            Classical.byContradiction fun hf => hp ⟨hpr, hf, hb⟩
          rw [Expr.andLift_false row pre p post hpre hpr hb hf hnp] at hk
          cases hk
        · exact ⟨pre, p, post, rfl, hpre, Option.isSome_iff_ne_none.mpr hpr⟩
    · rintro ⟨pre, p, post, rfl, hpre, hp⟩
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hp
      rw [Expr.refOutcome_isSome]
      exact ⟨k, Expr.andLift_error row pre p post k hpre hk hnp⟩
  · -- Every operand plain: the eager `AND`, which raises nowhere, nor does any operand.
    have hpl : ∀ q ∈ ps, q.plain = true := by
      intro q hq
      exact Classical.byContradiction fun h => hnp ⟨q, hq, by simpa using h⟩
    have hlen : (ps.filter Expr.plain).length = ps.length := by
      rw [List.filter_eq_self.mpr (fun q hq => hpl q hq)]
    simp only [Expr.andLift, hlen, ↓reduceIte]
    rw [Expr.conj_firstError_none row ps (fun q hq => by rw [Expr.issues_plain row q (hpl q hq)]; rfl)]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro pre p post hps _ hp
    rw [Expr.issues_plain row p (hpl p (by simp [hps]))] at hp
    exact absurd hp (by simp [firstError])

/-- **Where the `OR` lift raises**: an operand raises, and every operand before
it goes on (`Expr.GoOr`: no raise, not TRUE). -/
theorem Expr.orLift_raises_iff (row : Row) (ps : List Expr)
    (hbv : ∀ q ∈ ps, firstError (q.issues row) = none → Expr.BoolVal row q) :
    (firstError ((Expr.orLift ps).issues row)).isSome ↔
      ∃ pre p post, ps = pre ++ p :: post ∧ (∀ q ∈ pre, Expr.GoOr row q) ∧
        (firstError (p.issues row)).isSome := by
  by_cases hnp : ∃ q ∈ ps, q.plain = false
  · constructor
    · intro h
      rw [Expr.refOutcome_isSome] at h
      obtain ⟨k, hk⟩ := h
      rcases List.first_not (Expr.GoOr row) ps with hall | ⟨pre, p, post, rfl, hpre, hp⟩
      · exfalso
        have hn : firstError ((Expr.disj ps).issues row) = none :=
          Expr.disj_firstError_none row ps (fun q hq => (hall q hq).1)
        have hok : (Expr.disj ps).refOutcome row = .ok ((Expr.disj ps).eval row) := by
          unfold Expr.refOutcome; rw [hn]
        rw [Expr.orLift_refines row ps _ (fun q hq => (hall q hq).2.2) hok] at hk
        cases hk
      · by_cases hpr : firstError (p.issues row) = none
        · exfalso
          have hb := hbv p (by simp) hpr
          have ht : p.eval row = .bool true :=
            Classical.byContradiction fun ht => hp ⟨hpr, ht, hb⟩
          rw [Expr.orLift_true row pre p post hpre hpr hb ht hnp] at hk
          cases hk
        · exact ⟨pre, p, post, rfl, hpre, Option.isSome_iff_ne_none.mpr hpr⟩
    · rintro ⟨pre, p, post, rfl, hpre, hp⟩
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hp
      rw [Expr.refOutcome_isSome]
      exact ⟨k, Expr.orLift_error row pre p post k hpre hk hnp⟩
  · have hpl : ∀ q ∈ ps, q.plain = true := by
      intro q hq
      exact Classical.byContradiction fun h => hnp ⟨q, hq, by simpa using h⟩
    have hlen : (ps.filter Expr.plain).length = ps.length := by
      rw [List.filter_eq_self.mpr (fun q hq => hpl q hq)]
    simp only [Expr.orLift, hlen, ↓reduceIte]
    rw [Expr.disj_firstError_none row ps (fun q hq => by rw [Expr.issues_plain row q (hpl q hq)]; rfl)]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro pre p post hps _ hp
    rw [Expr.issues_plain row p (hpl p (by simp [hps]))] at hp
    exact absurd hp (by simp [firstError])

/-! ## The lift reads what its operands read -/

omit [Boxes.Ambient] in
theorem Expr.foldl_and_refsLt {n : Nat} : ∀ (ps : List Expr) (acc : Expr), acc.refsLt n →
    (∀ q ∈ ps, q.refsLt n) → (ps.foldl (.bin .and) acc).refsLt n
  | [], _, h, _ => h
  | q :: ps, acc, h, hq => Expr.foldl_and_refsLt ps _ ⟨h, hq q (by simp)⟩ (fun r hr => hq r (by simp [hr]))

omit [Boxes.Ambient] in
theorem Expr.foldl_or_refsLt {n : Nat} : ∀ (ps : List Expr) (acc : Expr), acc.refsLt n →
    (∀ q ∈ ps, q.refsLt n) → (ps.foldl (.bin .or) acc).refsLt n
  | [], _, h, _ => h
  | q :: ps, acc, h, hq => Expr.foldl_or_refsLt ps _ ⟨h, hq q (by simp)⟩ (fun r hr => hq r (by simp [hr]))

omit [Boxes.Ambient] in
theorem Expr.conj_refsLt {n : Nat} {ps : List Expr} (h : ∀ q ∈ ps, q.refsLt n) : (Expr.conj ps).refsLt n := by
  cases ps with
  | nil => trivial
  | cons p ps => exact Expr.foldl_and_refsLt ps p (h p (by simp)) (fun q hq => h q (by simp [hq]))

omit [Boxes.Ambient] in
theorem Expr.disj_refsLt {n : Nat} {ps : List Expr} (h : ∀ q ∈ ps, q.refsLt n) : (Expr.disj ps).refsLt n := by
  cases ps with
  | nil => trivial
  | cons p ps => exact Expr.foldl_or_refsLt ps p (h p (by simp)) (fun q hq => h q (by simp [hq]))

omit [Boxes.Ambient] in
theorem Expr.andChain_refsLt {n : Nat} {all : Expr} (ha : all.refsLt n) :
    ∀ {ps : List Expr}, (∀ q ∈ ps, q.refsLt n) → (Expr.andChain all ps).refsLt n
  | [], _ => ⟨ha, trivial, trivial⟩
  | p :: ps, h => by
    have hp := h p (by simp)
    exact ⟨⟨hp, hp⟩, Expr.andChain_refsLt ha (fun q hq => h q (by simp [hq])), trivial⟩

omit [Boxes.Ambient] in
theorem Expr.orChain_refsLt {n : Nat} {all : Expr} (ha : all.refsLt n) :
    ∀ {ps : List Expr}, (∀ q ∈ ps, q.refsLt n) → (Expr.orChain all ps).refsLt n
  | [], _ => ⟨ha, trivial, trivial⟩
  | p :: ps, h => by
    have hp := h p (by simp)
    exact ⟨⟨hp, hp⟩, Expr.orChain_refsLt ha (fun q hq => h q (by simp [hq])), trivial⟩

omit [Boxes.Ambient] in
/-- **The `AND` lift reads only what its operands read.** -/
theorem Expr.andLift_refsLt {n : Nat} {ps : List Expr} (h : ∀ q ∈ ps, q.refsLt n) :
    (Expr.andLift ps).refsLt n := by
  have hg : (Expr.andG ps).refsLt n := ⟨Expr.andChain_refsLt (Expr.conj_refsLt h) h, trivial⟩
  unfold Expr.andLift; dsimp only
  split
  · exact Expr.conj_refsLt h
  · split
    · exact hg
    · exact ⟨Expr.conj_refsLt (fun q hq => h q (List.mem_filter.mp hq).1), hg⟩

omit [Boxes.Ambient] in
/-- **The `OR` lift reads only what its operands read.** -/
theorem Expr.orLift_refsLt {n : Nat} {ps : List Expr} (h : ∀ q ∈ ps, q.refsLt n) :
    (Expr.orLift ps).refsLt n := by
  have hg : (Expr.orG ps).refsLt n := ⟨Expr.orChain_refsLt (Expr.disj_refsLt h) h, trivial⟩
  unfold Expr.orLift; dsimp only
  split
  · exact Expr.disj_refsLt h
  · split
    · exact hg
    · exact ⟨Expr.disj_refsLt (fun q hq => h q (List.mem_filter.mp hq).1), hg⟩

end Substrait
