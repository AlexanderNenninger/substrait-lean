import SubstraitLean.Lowering
import Sverify.Analysis.Partition
import SubstraitLean.Parse
import Sverify.Core.AllowedP

/-!
# Binding shared arguments to columns (#821)

The SQL writers guard a function by testing its argument and computing it in
the same `CASE`: a date shim reads its argument four times or more, an
overflow guard three times. SQL has no `LET`, so a call nested in such a
function is written out at each reading, and nested shims multiply: a date
truncated, moved by a month and by a day was 51 kB of Spark SQL.

`Rel.bindArgs` binds such arguments to columns before the plan is written. A
projection computes an argument that its function would copy (`f (g x)`,
where `f` copies `g x` and `g x` is large enough, `Expr.worthBinding`) as a
column of a projection below it, and reads that column instead; an emit
keeps the columns as they were. It repeats this, innermost arguments first,
so each written function reads columns or small expressions. Equal arguments
share one column. An aggregate's measure arguments move into a projection
below it first (`Rel.pullArgs`), which is then bound the same way.
A term computed in several places, `CASE` branches among them, is bound
too when one of the places evaluates it on every row (`Expr.repeated`).

The pass only moves expressions that every evaluation of the projection
evaluates anyway (`Expr.eager`): arguments of calls, never a `CASE`'s
branches or a lambda's body. It checks each step when it runs: substituting
the bound arguments back gives the original expressions (`Rel.bindStep`), or
the projection stays as it was. The theorems state that the plan computes
the same rows with any functions (`Rel.evalI_bindArgs`, so on every engine,
and `Rel.eval_bindArgs` for the reference), and raises exactly where the
original raises, under any profile (`Rel.raises_bindArgs`).
-/

namespace Substrait

/-! ## Expressions -/

/-- The subexpressions that evaluating `e` always evaluates: the arguments of
its calls, a `CASE`'s condition and a lambda's list, and theirs. -/
def Expr.eager : Expr → List Expr
  | .lit _ | .field _ => []
  | .un _ a => a :: a.eager
  | .bin _ a b => a :: b :: (a.eager ++ b.eager)
  | .ifThen c _ _ => c :: c.eager
  | .hof _ l _ => l :: l.eager

/-- An expression raises where one it always evaluates raises. -/
theorem Expr.raises_of_eager {p : Profile} {row : Row} :
    ∀ {e s : Expr}, s ∈ e.eager → s.RaisesOn p row → e.RaisesOn p row
  | .lit _, _, h, _ | .field _, _, h, _ => by simp [eager] at h
  | .un f a, s, h, hs => by
    have ha : a.RaisesOn p row := by
      simp only [eager, List.mem_cons] at h
      rcases h with rfl | h
      · exact hs
      · exact raises_of_eager h hs
    simp only [RaisesOn, evalP]; exact Outcome.bind_error ha
  | .bin f a b, s, h, hs => by
    simp only [eager, List.mem_cons, List.mem_append] at h
    have hab : a.RaisesOn p row ∨ b.RaisesOn p row := by
      rcases h with rfl | rfl | h | h
      · exact .inl hs
      · exact .inr hs
      · exact .inl (raises_of_eager h hs)
      · exact .inr (raises_of_eager h hs)
    simp only [RaisesOn, evalP]
    rcases hab with ha | hb
    · exact Outcome.bind_error ha
    · cases a.evalP p row with
      | error k => rfl
      | ok x => rw [Outcome.ok_bind]; exact Outcome.bind_error hb
  | .ifThen c t e, s, h, hs => by
    have hc : c.RaisesOn p row := by
      simp only [eager, List.mem_cons] at h
      rcases h with rfl | h
      · exact hs
      · exact raises_of_eager h hs
    simp only [RaisesOn, evalP]; exact Outcome.bind_error hc
  | .hof f l b, s, h, hs => by
    have hl : l.RaisesOn p row := by
      simp only [eager, List.mem_cons] at h
      rcases h with rfl | h
      · exact hs
      · exact raises_of_eager h hs
    simp only [RaisesOn, evalP]; exact Outcome.bind_error hl

theorem Expr.evalI_subst {I : Impl} (σ : List Expr) (row : Row) :
    ∀ e : Expr, (e.subst σ).eval row I = e.eval (σ.map (·.eval row I)) I
  | .lit _ => rfl
  | .field i => by
    simp only [subst, eval, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases σ[i]? <;> rfl
  | .un f a => by simp [subst, eval, Expr.evalI_subst σ row a]
  | .bin f a b => by simp [subst, eval, Expr.evalI_subst σ row a, Expr.evalI_subst σ row b]
  | .ifThen c t e => by
    simp [subst, eval, Expr.evalI_subst σ row c, Expr.evalI_subst σ row t,
      Expr.evalI_subst σ row e]
  | .hof f l b => by
    simp only [subst, eval, Expr.evalI_subst σ row l]
    congr 1; funext x
    rw [Expr.evalI_subst _ (x :: row) b]
    simp [eval, List.map_map, Function.comp_def, Expr.eval_shift_cons]

/-- A call of a function. -/
def Expr.isCall : Expr → Bool
  | .un _ _ | .bin _ _ _ => true
  | _ => false

/-! ### Which arguments to bind

The pass is sound for any choice (`Rel.bindStep` checks it); the choice
only decides the written SQL's size. A column costs a level of subquery,
which passes every column through, so the pass binds an argument where the
writers would copy more than that: where its function copies it (`copies`)
times its estimated size (`Expr.cost`) reaches `bindCost`. The copies are
measured on the writers (`sverify_dev.plan_size`, #821): a double's
operation guards for overflow and NaN, a date's for its range, an integer's
for overflow. -/

/-- About how often the SQL writers write a function's argument. -/
def UnFn.copies : UnFn → Nat
  | .ffloor | .fceil | .fround | .froundTo _ | .ftoi | .narrow _ | .fmath _ | .fneg => 5
  | .dateTrunc _ | .dayTrunc _ | .addMonths _ _ | .bucket _ _ | .dayPart _ | .strftime _ => 6
  | .neg | .upper | .lower | .reverse | .ascii | .timeOfDay | .datePart _ => 3
  | _ => 1

def BinFn.copies : BinFn → Nat
  | .fadd | .fsub | .fmul | .fdiv | .fmod | .fpow | .fatan2 | .flogb => 8
  | .dateAdd | .ipow | .strRepeat | .levenshtein | .ilike => 5
  | .add | .sub | .mul | .idiv | .imod | .bit _ | .substr _ _ => 3
  | _ => 1

/-- An estimate of the size of `e`'s SQL. -/
def Expr.cost : Expr → Nat
  | .lit _ | .field _ => 1
  | .un f a => f.copies * a.cost + 1
  | .bin f a b => f.copies * (a.cost + b.cost) + 1
  | .ifThen c t e => c.cost + t.cost + e.cost + 1
  | .hof _ l b => l.cost + b.cost + 1

/-- The size a copy must reach for a column to pay off. -/
def bindCost : Nat := 40

/-- An argument of a function copying it `k` times worth a column of its own:
a call reading a column, large enough. A `CASE` stays where it is, with what
it reads; constants (`Expr.readsField`) too, as the writers fold them. -/
def Expr.worthBinding (k : Nat) (e : Expr) : Bool :=
  e.isCall && e.readsField && bindCost ≤ k * e.cost

/-- Functions whose argument `Write.writeExpr` writes as one Substrait call
with them: an overflow check around the arithmetic it checks, a decimal's
type around its arithmetic, a time of day around the addition it wraps.
Their argument stays in place; its own arguments may be bound. -/
def UnFn.pinsArg : UnFn → Bool
  | .wrap _ | .fit _ _ | .decimal _ _ | .dkind _ _ | .narrow _ | .timeOfDay => true
  | _ => false

/-- Decimal arithmetic, which the writer reads together with its context. -/
def Expr.pinnedArg : Expr → Bool
  | .bin .dadd _ _ | .bin .dsub _ _ | .bin .dmul _ _ | .bin .ddiv _ _ => true
  | _ => false

mutual
/-- The arguments to bind in `e`: the innermost arguments of calls that are
worth binding (`Expr.worthBinding`). Arguments inside them come first, so
an argument is bound before the calls that read it. -/
def Expr.toBind : Expr → List Expr
  | .un f a => if f.pinsArg then a.toBind else Expr.argToBind f.copies a
  | .bin f a b => Expr.argToBind f.copies a ++ Expr.argToBind f.copies b
  | _ => []

def Expr.argToBind (k : Nat) (a : Expr) : List Expr :=
  match a.toBind with
  | [] => if a.worthBinding k && !a.pinnedArg then [a] else []
  | inner => inner
end

/-- `e` with the arguments `ss` replaced by the columns `base`, `base + 1`, …,
where `free` (the argument of a function that does not pin it). -/
def Expr.bindTo (ss : List Expr) (base : Nat) (free : Bool := true) : Expr → Expr
  | e@(.un f a) =>
    match if free then ss.idxOf? e else none with
    | some j => .field (base + j)
    | none => .un f (a.bindTo ss base !f.pinsArg)
  | e@(.bin f a b) =>
    match if free && !e.pinnedArg then ss.idxOf? e else none with
    | some j => .field (base + j)
    | none => .bin f (a.bindTo ss base) (b.bindTo ss base)
  | e@(.ifThen c t x) =>
    match if free then ss.idxOf? e else none with
    | some j => .field (base + j)
    | none => .ifThen (c.bindTo ss base) (t.bindTo ss base) (x.bindTo ss base)
  | e@(.hof f l b) =>
    match if free then ss.idxOf? e else none with
    | some j => .field (base + j)
    | none => .hof f (l.bindTo ss base) b
  | e => e

/-! ### Repeated subexpressions (#821, step 2)

A term an expression computes in several places, `CASE` branches among
them, is computed once as a column. Evaluating it on every row is safe where
the expressions evaluate it on every row anyway: in an eager position of one
of them (`Expr.eager`; `Rel.bindStep` checks it). A `CASE` chain over the
same value (`CASE WHEN x = 0 THEN … WHEN x = 1 THEN …`) has it in its first
condition. Terms only under a `CASE`'s branches stay: hoisting them could
raise where the `CASE` guards them (`x / y` under `y <> 0`). -/

/-- The terms `e` is built from, outside lambdas' bodies, `e` among them. -/
def Expr.terms : Expr → List Expr
  | .lit _ | .field _ => []
  | e@(.un _ a) => e :: a.terms
  | e@(.bin _ a b) => e :: (a.terms ++ b.terms)
  | e@(.ifThen c t x) => e :: (c.terms ++ t.terms ++ x.terms)
  | e@(.hof _ l _) => e :: l.terms

/-- The repeated terms of `es` worth a column: read a column, occur at least
twice, at least once eagerly, and copy enough (`Expr.cost`); the innermost
of them, so a step binds before what reads them. -/
def Expr.repeated (es : List Expr) : List Expr :=
  let all := es.flatMap Expr.terms
  let eager := es.flatMap Expr.eager
  let cands := all.eraseDups.filter fun s =>
    s.readsField && !s.pinnedArg && bindCost ≤ all.count s * s.cost && 2 ≤ all.count s &&
      eager.contains s
  cands.filter fun s => !cands.any fun t => t != s && s.terms.contains t

/-! ## One step on a projection -/

/-- The columns of a row of length `n`, then `ss`. -/
def bindSubst (n : Nat) (ss : List Expr) : List Expr :=
  (List.range n).map .field ++ ss

/-- One step of the pass on a projection of `es` over rows of `n` columns:
the arguments to bind, `ss`, and the expressions reading them as columns
`n`, `n + 1`, …, if the step checks out: substituting `ss` back gives `es`,
and every expression of `ss` is one some expression of `es` always evaluates. -/
def Rel.bindStep (n : Nat) (es : List Expr) : Option (List Expr × List Expr) :=
  let ss := (es.flatMap Expr.toBind ++ Expr.repeated es).eraseDups
  if ss.isEmpty then none else
  let es' := es.map (·.bindTo ss n)
  if es'.map (·.subst (bindSubst n ss)) == es && ss.all (fun s => es.any (s ∈ ·.eager)) then
    some (ss, es')
  else none

theorem Rel.bindStep_spec {n : Nat} {es ss es' : List Expr} (h : Rel.bindStep n es = some (ss, es')) :
    es'.map (·.subst (bindSubst n ss)) = es ∧ ∀ s ∈ ss, ∃ e ∈ es, s ∈ e.eager := by
  unfold Rel.bindStep at h
  simp only at h
  split at h
  · cases h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
        decide_eq_true_eq] at hc
      exact hc
    · cases h

/-- The emit after a step: the input's `n` columns, then the projection's. -/
def bindEmit (n k m : Nat) : List Nat := List.range n ++ (List.range m).map (n + k + ·)

/-! ### Emits over emits

The writer writes an emit over an emit as one (`Write.writeRel`), so the pass
fuses them, and the written plan parses back as the plan it bound. -/

/-- `emit (emit r m₁) m₂` as one emit, where `m₂` reads only columns `m₁` has. -/
def Rel.fuseEmit (r : Rel) (m : List Nat) : Rel :=
  match r with
  | .emit r' m₁ => if m.all (· < m₁.length) then .emit r' (m.map (m₁.getD · 0)) else .emit r m
  | _ => .emit r m

theorem fuseEmit_row {m₁ m : List Nat} (h : m.all (· < m₁.length) = true) (row : Row) :
    m.map ((m₁.map (row.getD · .null)).getD · .null) = (m.map (m₁.getD · 0)).map (row.getD · .null) := by
  rw [List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < m₁.length := by simpa using List.all_eq_true.mp h i hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']

theorem Rel.evalI_fuseEmit {I : Impl} {cat : Catalog} (r : Rel) (m : List Nat) :
    (Rel.fuseEmit r m).eval cat I = (Rel.emit r m).eval cat I := by
  unfold fuseEmit
  split
  · rename_i r' m₁
    split
    · rename_i h
      simp only [eval, List.map_map]
      exact List.map_congr_left fun row _ => by simpa [List.map_map] using (fuseEmit_row h row).symm
    · rfl
  · rfl

theorem Rel.raises_fuseEmit {p : Profile} {cat : Catalog} (r : Rel) (m : List Nat) :
    (Rel.fuseEmit r m).Raises p cat ↔ (Rel.emit r m).Raises p cat := by
  unfold fuseEmit
  split
  · split <;> simp [Raises]
  · exact Iff.rfl

theorem Rel.arity_fuseEmit {cat : Catalog} (r : Rel) (m : List Nat) :
    (Rel.fuseEmit r m).arity cat = m.length := by
  unfold fuseEmit
  split
  · split <;> simp [arity]
  · rfl

/-- A projection of `es` over `r`, whose rows have `n` columns, with its
arguments bound, step by step (`fuel` of them at most). -/
def Rel.bindProject (n : Nat) : Nat → Rel → List Expr → Rel
  | 0, r, es => .project r es
  | fuel + 1, r, es =>
    match Rel.bindStep n es with
    | none => .project r es
    | some (ss, es') =>
      Rel.fuseEmit (Rel.bindProject (n + ss.length) fuel (.project r ss) es')
        (bindEmit n ss.length es.length)

/-! ### The rows of one step -/

theorem range_map_getD {row : Row} {n : Nat} (h : row.length = n) :
    (List.range n).map (row.getD · .null) = row := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem bindSubst_evalI {I : Impl} {row : Row} {n : Nat} (h : row.length = n) (ss : List Expr) :
    (bindSubst n ss).map (·.eval row I) = row ++ ss.map (·.eval row I) := by
  simp only [bindSubst, List.map_append, List.map_map]
  congr 1
  exact range_map_getD h

/-- Reading the emit's columns from the row the step computes. -/
theorem bindEmit_getD {row xs ys : Row} {n : Nat} (h : row.length = n) :
    (bindEmit n xs.length ys.length).map ((row ++ xs ++ ys).getD · .null) = row ++ ys := by
  simp only [bindEmit, List.map_append, List.map_map]
  congr 1
  · apply List.ext_getElem (by simp [h])
    intro i h1 h2
    have hi : i < row.length := h2
    simp [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_left hi,
      List.getElem?_eq_getElem hi]
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply,
      List.getD_eq_getElem?_getD, List.append_assoc]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    simp only [h]
    rw [show n + xs.length + i - n - xs.length = i by omega]
    simp [List.getElem?_eq_getElem h2]

/-- One step's projection, for rows of `n` columns: the bound arguments,
then the expressions reading them, give the original values. -/
theorem bindStep_row {I : Impl} {n : Nat} {es ss es' : List Expr}
    (h : es'.map (·.subst (bindSubst n ss)) = es) {row : Row} (hl : row.length = n) :
    (bindEmit n ss.length es.length).map
      ((row ++ ss.map (·.eval row I) ++ es'.map (·.eval (row ++ ss.map (·.eval row I)) I)).getD · .null) =
      row ++ es.map (·.eval row I) := by
  have hes : es'.map (·.eval (row ++ ss.map (·.eval row I)) I) = es.map (·.eval row I) := by
    rw [← h, List.map_map]
    exact List.map_congr_left fun e _ => by
      simp only [Function.comp_apply, Expr.evalI_subst, bindSubst_evalI hl]
  rw [hes]
  have := bindEmit_getD (xs := ss.map (·.eval row I)) (ys := es.map (·.eval row I)) hl
  simpa using this

/-- One step raises on a row exactly where the projection does. -/
theorem bindStep_raises {p : Profile} {n : Nat} {es ss es' : List Expr}
    (h : es'.map (·.subst (bindSubst n ss)) = es) (he : ∀ s ∈ ss, ∃ e ∈ es, s ∈ e.eager)
    {row : Row} (hl : row.length = n) :
    ((∃ s ∈ ss, s.RaisesOn p row) ∨
      ∃ e ∈ es', e.RaisesOn p (row ++ ss.map (·.eval row p.impl))) ↔
      ∃ e ∈ es, e.RaisesOn p row := by
  by_cases hs : ∃ s ∈ ss, s.RaisesOn p row
  · obtain ⟨s, hs, hr⟩ := hs
    obtain ⟨e, hee, hse⟩ := he s hs
    exact ⟨fun _ => ⟨e, hee, Expr.raises_of_eager hse hr⟩, fun _ => .inl ⟨s, hs, hr⟩⟩
  · -- No bound argument raises: each evaluates to its column's value.
    have hσ : ∀ i, ((bindSubst n ss).getD i (.lit .null)).evalP p row =
        .ok ((row ++ ss.map (·.eval row p.impl)).getD i .null) := by
      intro i
      simp only [bindSubst, List.getD_eq_getElem?_getD]
      by_cases hi : i < n
      · rw [List.getElem?_append_left (by simpa using hi), List.getElem?_append_left (by omega)]
        simp [List.getElem?_range hi, Expr.evalP]
      · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by omega)]
        simp only [List.length_map, List.length_range, List.getElem?_map, hl]
        cases hj : ss[i - n]? with
        | none => rfl
        | some s =>
          have hm : s ∈ ss := List.mem_of_getElem? hj
          have hnr : ¬s.RaisesOn p row := fun hr => hs ⟨s, hm, hr⟩
          obtain ⟨v, hv⟩ := Expr.ok_of_not_raises hnr
          simp only [Option.map_some, Option.getD_some, hv, Expr.evalI_of_evalP hv]
    have hraise : ∀ e' : Expr, (e'.subst (bindSubst n ss)).RaisesOn p row ↔
        e'.RaisesOn p (row ++ ss.map (·.eval row p.impl)) := fun e' => by
      simp only [Expr.RaisesOn, Expr.evalP_subst hσ e']
    constructor
    · rintro (h' | ⟨e', he', hr⟩)
      · exact absurd h' hs
      · exact ⟨_, h ▸ List.mem_map_of_mem he', (hraise e').mpr hr⟩
    · rintro ⟨e, hee, hr⟩
      rw [← h] at hee
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hee
      exact .inr ⟨e', he', (hraise e').mp hr⟩

/-! ### Rows have the plan's arity, with any functions -/

theorem aggregateEvalI_length {I : Impl} {gs : List Expr} {ms : List Measure} {rows : Relation}
    {row : Row} (h : row ∈ aggregateEval gs ms rows I) : row.length = gs.length + ms.length := by
  unfold aggregateEval at h
  split at h
  · rename_i hg
    simp only [List.mem_singleton] at h; subst h
    simp [List.isEmpty_iff.mp hg]
  · simp only [List.mem_map] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp (canonReps_sub hk)
    simp [groupKey]

/-- **`Rel.eval cat I` has the plan's arity**, as `Rel.eval_arity`, with any functions. -/
theorem Rel.evalI_arity {I : Impl} {cat : Catalog} (hcat : cat.WF) :
    ∀ {r : Rel}, r.WF cat → ∀ row ∈ r.eval cat I, row.length = r.arity cat
  | .read t, _, row, h => hcat t row h
  | .values _ _, hwf, row, h => hwf row h
  | .filter r _, hwf, row, h => by
      simp only [eval, List.mem_filter] at h
      exact evalI_arity hcat hwf.1 row h.1
  | .project r es, hwf, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp [arity, evalI_arity hcat hwf.1 x hx]
  | .emit _ _, _, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, _, rfl⟩ := h
      simp [arity]
  | .cross a b, hwf, row, h => by
      simp only [eval, mem_crossRows] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      simp [arity, evalI_arity hcat hwf.1 x hx, evalI_arity hcat hwf.2 y hy]
  | .join a b .inner _, hwf, row, h => by
      simp only [eval, List.mem_filter, mem_crossRows] at h
      obtain ⟨⟨x, hx, y, hy, rfl⟩, _⟩ := h
      simp [arity, evalI_arity hcat hwf.1 x hx, evalI_arity hcat hwf.2.1 y hy]
  | .join a b .left on, hwf, row, h => by
      simp only [eval, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      have hxl := evalI_arity hcat hwf.1 x hx
      unfold leftJoinRow at h
      simp only [] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        simp [arity, hxl]
      · simp only [List.mem_filter, List.mem_map] at h
        obtain ⟨⟨y, hy, rfl⟩, _⟩ := h
        simp [arity, hxl, evalI_arity hcat hwf.2.1 y hy]
  | .fetch r off cnt, hwf, row, h => by
      simp only [eval] at h
      have := evalI_arity (I := I) hcat (r := r) hwf
      split at h
      · exact this row (List.mem_of_mem_drop h)
      · exact this row (List.mem_of_mem_drop (List.mem_of_mem_take h))
  | .unionAll a b, hwf, row, h => by
      simp only [eval, List.mem_append] at h
      rcases h with h | h
      · exact evalI_arity hcat hwf.1 row h
      · simp only [arity, hwf.2.2]; exact evalI_arity hcat hwf.2.1 row h
  | .window r _ _ _, hwf, row, h => by
      obtain ⟨_, x, _, _, hx, rfl⟩ := mem_windowEval h
      simp [arity, evalI_arity hcat hwf.1 x hx]
  | .semi a _ _ _, hwf, row, h => by
      simp only [eval, List.mem_filter] at h
      exact evalI_arity hcat hwf.1 row h.1
  | .orderBy r _, hwf, row, h => by
      simp only [eval, List.mem_mergeSort] at h
      exact evalI_arity hcat hwf.1 row h
  | .distinct r, hwf, row, h => by
      simp only [eval] at h
      replace h := canonReps_sub h
      exact evalI_arity hcat (r := r) hwf row h
  | .aggregate _ _ _, _, _, h => aggregateEvalI_length h
  | .unnest r _, hwf, row, h => by
      simp only [eval, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      obtain ⟨_, _, _, _, rfl⟩ := mem_unnestRow h
      simp [arity, evalI_arity hcat hwf.1 x hx]

/-! ### A projection, step by step -/

theorem Rel.arity_bindProject {cat : Catalog} :
    ∀ (fuel : Nat) {n : Nat} {r : Rel} {es : List Expr}, r.arity cat = n →
      (Rel.bindProject n fuel r es).arity cat = n + es.length
  | 0, _, _, _, h => by simp [bindProject, arity, h]
  | fuel + 1, n, r, es, h => by
    unfold bindProject
    split
    · simp [arity, h]
    · simp [arity_fuseEmit, bindEmit]

theorem Rel.evalI_bindProject {I : Impl} {cat : Catalog} :
    ∀ (fuel : Nat) {n : Nat} {r : Rel} {es : List Expr}, (∀ row ∈ r.eval cat I, row.length = n) →
      (Rel.bindProject n fuel r es).eval cat I = (Rel.project r es).eval cat I
  | 0, _, _, _, _ => rfl
  | fuel + 1, n, r, es, hl => by
    unfold bindProject
    split
    · rfl
    · rename_i ss es' hs
      have h := (bindStep_spec hs).1
      have hl' : ∀ row ∈ (Rel.project r ss).eval cat I, row.length = n + ss.length := by
        intro row hr
        simp only [eval, List.mem_map] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        simp [hl x hx]
      rw [evalI_fuseEmit]
      simp only [eval]
      rw [evalI_bindProject fuel hl']
      simp only [eval, List.map_map]
      exact List.map_congr_left fun row hr => bindStep_row h (hl row hr)

theorem Rel.raises_bindProject {p : Profile} {cat : Catalog} :
    ∀ (fuel : Nat) {n : Nat} {r : Rel} {es : List Expr}, (∀ row ∈ r.eval cat p.impl, row.length = n) →
      ((Rel.bindProject n fuel r es).Raises p cat ↔ (Rel.project r es).Raises p cat)
  | 0, _, _, _, _ => Iff.rfl
  | fuel + 1, n, r, es, hl => by
    unfold bindProject
    split
    · exact Iff.rfl
    · rename_i ss es' hs
      obtain ⟨h, he⟩ := bindStep_spec hs
      have hl' : ∀ row ∈ (Rel.project r ss).eval cat p.impl, row.length = n + ss.length := by
        intro row hr
        simp only [eval, List.mem_map] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        simp [hl x hx]
      rw [raises_fuseEmit]
      simp only [Raises]
      rw [raises_bindProject fuel hl']
      simp only [Raises, eval]
      constructor
      · rintro ((hr | ⟨row, hrow, s, hs, hsr⟩) | ⟨row', hrow', e', he', her⟩)
        · exact .inl hr
        · exact .inr ⟨row, hrow, (bindStep_raises h he (hl row hrow)).mp (.inl ⟨s, hs, hsr⟩)⟩
        · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hrow'
          exact .inr ⟨row, hrow, (bindStep_raises h he (hl row hrow)).mp (.inr ⟨e', he', her⟩)⟩
      · rintro (hr | ⟨row, hrow, hx⟩)
        · exact .inl (.inl hr)
        · rcases (bindStep_raises h he (hl row hrow)).mpr hx with ⟨s, hs, hsr⟩ | ⟨e', he', her⟩
          · exact .inl (.inr ⟨row, hrow, s, hs, hsr⟩)
          · exact .inr ⟨_, List.mem_map_of_mem hrow, e', he', her⟩


/-! ## Aggregates

An aggregate's measure arguments are computed on every input row, as a
projection's expressions are. `Rel.pullArgs` moves them into a projection
below the aggregate, which `Rel.bindProject` then binds: `SUM(a + b * c)`
over `r` becomes `SUM(#n)` over `r` projected with `a + b * c`. -/

theorem Expr.evalI_append {I : Impl} {e : Expr} {n : Nat} {row : Row} (extra : Row)
    (he : e.refsLt n) (hlen : row.length = n) :
    e.eval (row ++ extra) I = e.eval row I := by
  induction e generalizing n row with
  | lit => rfl
  | field i =>
    simp only [refsLt] at he
    simp [eval, List.getD, List.getElem?_append_left (hlen ▸ he)]
  | un f a ih => simp [eval, ih he hlen]
  | bin f a b iha ihb => simp [eval, iha he.1 hlen, ihb he.2 hlen]
  | ifThen c t e ihc iht ihe => simp [eval, ihc he.1 hlen, iht he.2.1 hlen, ihe he.2.2 hlen]
  | hof f l b ihl ihb =>
    simp only [eval, ihl he.1 hlen]
    congr 1; funext x
    exact ihb (row := x :: row) he.2 (by simp [hlen])

theorem Expr.evalP_append {p : Profile} {e : Expr} {n : Nat} {row : Row} (extra : Row)
    (he : e.refsLt n) (hlen : row.length = n) :
    e.evalP p (row ++ extra) = e.evalP p row := by
  induction e generalizing n row with
  | lit => rfl
  | field i =>
    simp only [refsLt] at he
    simp [evalP, List.getD, List.getElem?_append_left (hlen ▸ he)]
  | un f a ih => simp [evalP, ih he hlen]
  | bin f a b iha ihb => simp [evalP, iha he.1 hlen, ihb he.2 hlen]
  | ifThen c t e ihc iht ihe => simp [evalP, ihc he.1 hlen, iht he.2.1 hlen, ihe he.2.2 hlen]
  | hof f l b ihl ihb =>
    simp only [evalP, ihl he.1 hlen]
    congr 1; funext v; congr 1; funext x
    exact ihb (row := x :: row) he.2 (by simp [hlen])

/-- Two lists related element by element. -/
def AllPulled {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ AllPulled R as bs
  | _, _ => False

/-- The measures reading their arguments from columns `base`, `base + 1`, … -/
def pullMeasures (base : Nat) : List Measure → List Measure
  | [] => []
  | m :: ms => { m with arg := .field base } :: pullMeasures (base + 1) ms

/-- A measure `m'` that is `m` reading its argument from a column of the
rows `g` extends. -/
def PulledFrom (I : Impl) (g : Row → Row) (rows : Relation) (m' m : Measure) : Prop :=
  m' = { m with arg := m'.arg } ∧ ∀ row ∈ rows, m'.arg.eval (g row) I = m.arg.eval row I

theorem pullMeasures_pulled {I : Impl} {n : Nat} {rows : Relation}
    (hl : ∀ row ∈ rows, row.length = n) :
    ∀ (pre : List Expr) (ms : List Measure),
      AllPulled (PulledFrom I (fun row => row ++ (pre ++ ms.map (·.arg)).map (·.eval row I)) rows)
        (pullMeasures (n + pre.length) ms) ms
  | _, [] => trivial
  | pre, m :: ms => by
    refine ⟨⟨rfl, fun row hr => ?_⟩, ?_⟩
    · simp [Expr.eval, List.getD, hl row hr]
    · have := pullMeasures_pulled (I := I) hl (pre ++ [m.arg]) ms
      simpa [Nat.add_assoc] using this

/-- A pulled measure computes the measure's value on rows `g` extends. -/
theorem PulledFrom.evalI {I : Impl} {g : Row → Row} {rows : Relation} {m' m : Measure}
    (h : PulledFrom I g rows m' m) {n : Nat} (hl : ∀ row ∈ rows, row.length = n)
    (hg : ∀ row ∈ rows, ∃ extra, g row = row ++ extra)
    (hf : ∀ c ∈ m.filter, c.refsLt n) (hs : ∀ k ∈ m.sort, k.col < n)
    {sub : Relation} (hsub : ∀ row ∈ sub, row ∈ rows) :
    m'.eval (sub.map g) I = m.eval sub I := by
  obtain ⟨hm', harg⟩ := h
  -- The filter keeps the rows it kept.
  have hkept : ∀ sub' : Relation, (∀ row ∈ sub', row ∈ rows) →
      m'.kept (sub'.map g) I = (m.kept sub' I).map g := by
    intro sub' hs'
    rw [hm']
    unfold Measure.kept
    cases hc : m.filter with
    | none => rfl
    | some c =>
      simp only [List.filter_map]
      congr 1
      refine List.filter_congr fun row hr => ?_
      obtain ⟨extra, he⟩ := hg row (hs' row hr)
      simp only [Function.comp_apply, he]
      rw [Expr.evalI_append extra (hf c (by simp [hc])) (hl row (hs' row hr))]
  have hin : ∀ sub' : Relation, (∀ row ∈ sub', row ∈ rows) →
      m'.inputs (sub'.map g) I = m.inputs sub' I := by
    intro sub' hs'
    have hd : m'.distinct = m.distinct := by rw [hm']
    have hk' : ∀ row ∈ m.kept sub' I, row ∈ rows := fun row hr => by
      unfold Measure.kept at hr; split at hr
      · exact hs' row hr
      · exact hs' row (List.mem_filter.mp hr).1
    unfold Measure.inputs
    rw [hkept sub' hs', hd, List.map_map,
      List.map_congr_left (f := (fun row => m'.arg.eval row I) ∘ g)
        (g := fun row => m.arg.eval row I) fun row hr => harg row (hk' row hr)]
  -- Sorting commutes with extending the rows.
  have hsort : (sub.map g).mergeSort (sortLe m'.sort) = (sub.mergeSort (sortLe m.sort)).map g := by
    have : m'.sort = m.sort := by rw [hm']
    rw [this]
    refine (List.map_mergeSort fun a ha b hb => ?_).symm
    obtain ⟨xa, hxa⟩ := hg a (hsub a ha)
    obtain ⟨xb, hxb⟩ := hg b (hsub b hb)
    rw [hxa, hxb, sortLe_append (fun k hk => (hl a (hsub a ha)) ▸ hs k hk)
      (fun k hk => (hl b (hsub b hb)) ▸ hs k hk)]
  have hsorted : ∀ row ∈ sub.mergeSort (sortLe m.sort), row ∈ rows :=
    fun row hr => hsub row (List.mem_mergeSort.mp hr)
  have hfn : m'.fn = m.fn := by rw [hm']
  unfold Measure.eval
  rw [hfn]
  split
  all_goals first
    | (rw [hsort, hin _ hsorted])
    | (rw [hin _ hsub])

theorem AllPulled.map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (h : ∀ a b, R a b → f a = g b) : ∀ {as : List α} {bs : List β}, AllPulled R as bs →
      as.map f = bs.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨hab, hr⟩ => by simp [h _ _ hab, AllPulled.map_eq h hr]
  | [], _ :: _, h' | _ :: _, [], h' => h'.elim

theorem AllPulled.map_eq_mem {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ} :
    ∀ {as : List α} {bs : List β}, AllPulled R as bs → (∀ a b, R a b → b ∈ bs → f a = g b) →
      as.map f = bs.map g
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, ⟨hab, hr⟩, h => by
    simp only [List.map_cons, h _ _ hab (by simp),
      AllPulled.map_eq_mem hr fun a b hr' hb => h a b hr' (by simp [hb])]
  | [], _ :: _, h', _ | _ :: _, [], h', _ => h'.elim

theorem AllPulled.mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, AllPulled R as bs → ∀ a ∈ as, ∃ b ∈ bs, R a b
  | [], [], _, _, h => by simp at h
  | _ :: _, _ :: _, ⟨hab, hr⟩, a, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨b, hb, hr'⟩ := AllPulled.mem_left hr a h
      exact ⟨b, by simp [hb], hr'⟩
  | [], _ :: _, h', _, _ | _ :: _, [], h', _, _ => h'.elim

theorem AllPulled.mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, AllPulled R as bs → ∀ b ∈ bs, ∃ a ∈ as, R a b
  | [], [], _, _, h => by simp at h
  | _ :: _, _ :: _, ⟨hab, hr⟩, b, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨a, ha, hr'⟩ := AllPulled.mem_right hr b h
      exact ⟨a, by simp [ha], hr'⟩
  | [], _ :: _, h', _, _ | _ :: _, [], h', _, _ => h'.elim

/-- An aggregate over rows `g` extends, with pulled measures, is the aggregate. -/
theorem aggregateEvalI_pull {I : Impl} {g : Row → Row} {rows : Relation} {n : Nat}
    {gs : List Expr} {ms ms' : List Measure}
    (hl : ∀ row ∈ rows, row.length = n) (hg : ∀ row ∈ rows, ∃ extra, g row = row ++ extra)
    (hgs : ∀ e ∈ gs, e.refsLt n) (hms : ∀ m ∈ ms, (∀ c ∈ m.filter, c.refsLt n) ∧ ∀ k ∈ m.sort, k.col < n)
    (hp : AllPulled (PulledFrom I g rows) ms' ms) :
    aggregateEval gs ms' (rows.map g) I = aggregateEval gs ms rows I := by
  have hk : ∀ row ∈ rows, groupKey gs (g row) I = groupKey gs row I := fun row hr => by
    obtain ⟨extra, he⟩ := hg row hr
    simp only [groupKey, he]
    exact List.map_congr_left fun e he' => Expr.evalI_append extra (hgs e he') (hl row hr)
  have hm : ∀ sub : Relation, (∀ row ∈ sub, row ∈ rows) →
      ms'.map (·.eval (sub.map g) I) = ms.map (·.eval sub I) := fun sub hsub =>
    hp.map_eq_mem fun m' m h hm => h.evalI hl hg (hms m hm).1 (hms m hm).2 hsub
  unfold aggregateEval
  split
  · rw [hm rows fun _ h => h]
  · rw [List.map_map, List.map_congr_left (f := (fun row => groupKey gs row I) ∘ g)
      (g := fun row => groupKey gs row I)
      fun row hr => hk row hr]
    refine List.map_congr_left fun k _ => ?_
    have hf : groupRows gs (rows.map g) k I = (groupRows gs rows k I).map g := by
      rw [groupRows, groupRows, List.filter_map]
      congr 1
      exact List.filter_congr fun row hr => by simp only [Function.comp_apply, hk row hr]
    rw [hf, hm (groupRows gs rows k I) fun _ hr => (List.mem_filter.mp hr).1]

/-- An aggregate whose measures read their arguments from columns of a
projection below it (`pullMeasures`), when the step binds something and the
measures sort by columns of the input. -/
def Rel.pullArgs (n fuel : Nat) (r : Rel) (gs : List Expr) (ms : List Measure) : Rel :=
  if ms.all (·.sort.all (·.col < n)) && (Rel.bindStep n (ms.map (·.arg))).isSome then
    .aggregate (Rel.bindProject n fuel r (ms.map (·.arg))) gs (pullMeasures n ms)
  else .aggregate r gs ms

theorem pullArgs_sorts {n : Nat} {ms : List Measure} (h : ms.all (·.sort.all (·.col < n)) = true) :
    ∀ m ∈ ms, ∀ k ∈ m.sort, k.col < n := fun m hm k hk => by
  have := List.all_eq_true.mp (List.all_eq_true.mp h m hm) k hk
  simpa using this

theorem Rel.evalI_pullArgs {I : Impl} {cat : Catalog} {n fuel : Nat} {r : Rel} {gs : List Expr}
    {ms : List Measure} (hl : ∀ row ∈ r.eval cat I, row.length = n)
    (hgs : ∀ e ∈ gs, e.refsLt n) (hms : ∀ m ∈ ms, m.refsLt n) :
    (Rel.pullArgs n fuel r gs ms).eval cat I = (Rel.aggregate r gs ms).eval cat I := by
  unfold pullArgs
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    simp only [eval]
    rw [evalI_bindProject fuel hl]
    simp only [eval]
    have hp := pullMeasures_pulled (I := I) hl [] ms
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at hp
    exact aggregateEvalI_pull hl (fun row _ => ⟨_, rfl⟩) hgs
      (fun m hm => ⟨(hms m hm).2, pullArgs_sorts h.1 m hm⟩) hp
  · rfl

/-- The expressions of a measure that can raise: its argument and filter. -/
theorem Measure.raises_exprs {p : Profile} {row : Row} (m : Measure) :
    (∃ e ∈ m.exprs, e.RaisesOn p row) ↔ m.arg.RaisesOn p row ∨ ∃ c ∈ m.filter, c.RaisesOn p row := by
  constructor
  · rintro ⟨e, he, hr⟩
    rcases List.mem_cons.mp he with rfl | he
    · exact .inl hr
    rcases List.mem_append.mp he with he | he
    · exact .inr ⟨e, by simpa using he, hr⟩
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp he
      simp [Expr.RaisesOn, Expr.evalP, Outcome.err?] at hr
  · rintro (h | ⟨c, hc, h⟩)
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨c, List.mem_cons_of_mem _ (List.mem_append_left _ (by simpa using hc)), h⟩

theorem pullMeasures_arg : ∀ {base : Nat} {ms : List Measure}, ∀ m ∈ pullMeasures base ms,
    ∃ j, m.arg = .field j
  | _, [], _, h => by simp [pullMeasures] at h
  | base, m :: ms, m', h => by
    simp only [pullMeasures, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨base, rfl⟩
    · exact pullMeasures_arg m' h

theorem Rel.raises_pullArgs {p : Profile} {cat : Catalog} {n fuel : Nat} {r : Rel} {gs : List Expr}
    {ms : List Measure} (hl : ∀ row ∈ r.eval cat p.impl, row.length = n)
    (hgs : ∀ e ∈ gs, e.refsLt n) (hms : ∀ m ∈ ms, m.refsLt n) :
    (Rel.pullArgs n fuel r gs ms).Raises p cat ↔ (Rel.aggregate r gs ms).Raises p cat := by
  unfold pullArgs
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have hp := pullMeasures_pulled (I := p.impl) hl [] ms
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at hp
    simp only [Raises]
    rw [raises_bindProject fuel hl, evalI_bindProject fuel hl]
    simp only [Raises, eval, List.mem_map, List.mem_append, List.mem_flatMap]
    -- Row by row: what the pulled aggregate raises on an extended row.
    have hstep : ∀ row ∈ r.eval cat p.impl,
        ((∃ a, (∃ m ∈ ms, m.arg = a) ∧ a.RaisesOn p row) ∨
          ∃ e, (e ∈ gs ∨ ∃ m ∈ pullMeasures n ms, e ∈ m.exprs) ∧
            e.RaisesOn p (row ++ (ms.map (·.arg)).map (·.eval row p.impl))) ↔
        ∃ e, (e ∈ gs ∨ ∃ m ∈ ms, e ∈ m.exprs) ∧ e.RaisesOn p row := by
      intro row hr
      have happ : ∀ e : Expr, e.refsLt n →
          (e.RaisesOn p (row ++ (ms.map (·.arg)).map (·.eval row p.impl)) ↔ e.RaisesOn p row) :=
        fun e he => by simp only [Expr.RaisesOn, Expr.evalP_append _ he (hl row hr)]
      constructor
      · rintro (⟨a, ⟨m, hm, rfl⟩, ha⟩ | ⟨e, he | ⟨m', hm', he⟩, hr'⟩)
        · exact ⟨m.arg, .inr ⟨m, hm, by simp [Measure.exprs]⟩, ha⟩
        · exact ⟨e, .inl he, (happ e (hgs e he)).mp hr'⟩
        · obtain ⟨m, hm, ⟨heq, _⟩⟩ := hp.mem_left m' hm'
          have hr2 : ∃ e ∈ m'.exprs, e.RaisesOn p (row ++ (ms.map (·.arg)).map (·.eval row p.impl)) :=
            ⟨e, he, hr'⟩
          rw [Measure.raises_exprs] at hr2
          rcases hr2 with ha | ⟨c, hc, hcr⟩
          · -- The pulled argument is a column: it does not raise.
            obtain ⟨j, hj⟩ := pullMeasures_arg m' hm'
            simp [hj, Expr.RaisesOn, Expr.evalP, Outcome.err?] at ha
          · have hc' : c ∈ m.filter := by rw [heq] at hc; exact hc
            exact ⟨c, .inr ⟨m, hm, List.mem_cons_of_mem _ (List.mem_append_left _ (by simpa using hc'))⟩,
              (happ c ((hms m hm).2 c hc')).mp hcr⟩
      · rintro ⟨e, he | ⟨m, hm, he⟩, hr'⟩
        · exact .inr ⟨e, .inl he, (happ e (hgs e he)).mpr hr'⟩
        · have hr2 : ∃ e ∈ m.exprs, e.RaisesOn p row := ⟨e, he, hr'⟩
          rw [Measure.raises_exprs] at hr2
          rcases hr2 with ha | ⟨c, hc, hcr⟩
          · exact .inl ⟨m.arg, ⟨m, hm, rfl⟩, ha⟩
          · obtain ⟨m', hm', ⟨heq, _⟩⟩ := hp.mem_right m hm
            refine .inr ⟨c, .inr ⟨m', hm', ?_⟩, (happ c ((hms m hm).2 c hc)).mpr hcr⟩
            rw [heq]
            exact List.mem_cons_of_mem _ (List.mem_append_left _ (by simpa using hc))
    constructor
    · rintro ((hr | ⟨row, hrow, a, ha, har⟩) | ⟨row', ⟨row, hrow, rfl⟩, e, he, her⟩)
      · exact .inl hr
      · exact .inr (by
          obtain ⟨e, he, her⟩ := (hstep row hrow).mp (.inl ⟨a, by simpa using ha, har⟩)
          exact ⟨row, hrow, e, by simpa using he, her⟩)
      · exact .inr (by
          obtain ⟨e', he', her'⟩ := (hstep row hrow).mp (.inr ⟨e, by simpa using he, her⟩)
          exact ⟨row, hrow, e', by simpa using he', her'⟩)
    · rintro (hr | ⟨row, hrow, e, he, her⟩)
      · exact .inl (.inl hr)
      · rcases (hstep row hrow).mpr ⟨e, by simpa using he, her⟩ with ⟨a, ha, har⟩ | ⟨e', he', her'⟩
        · exact .inl (.inr ⟨row, hrow, a, by simpa using ha, har⟩)
        · exact .inr ⟨_, ⟨row, hrow, rfl⟩, e', by simpa using he', her'⟩
  · exact Iff.rfl

/-! ## The pass -/

/-- At most this many steps per projection: each binds a level of nesting. -/
def bindFuel : Nat := 64

/-- Bind the arguments of every projection of the plan (`Rel.bindProject`). -/
def Rel.bindArgs (cat : Catalog) : Rel → Rel
  | .read t => .read t
  | .values n rows => .values n rows
  | .filter r c => .filter (r.bindArgs cat) c
  | .project r es => Rel.bindProject (r.arity cat) bindFuel (r.bindArgs cat) es
  | .emit r m => Rel.fuseEmit (r.bindArgs cat) m
  | .cross a b => .cross (a.bindArgs cat) (b.bindArgs cat)
  | .join a b ty on => .join (a.bindArgs cat) (b.bindArgs cat) ty on
  | .fetch r o c => .fetch (r.bindArgs cat) o c
  | .unionAll a b => .unionAll (a.bindArgs cat) (b.bindArgs cat)
  | .window r part sort fns => .window (r.bindArgs cat) part sort fns
  | .semi a b anti on => .semi (a.bindArgs cat) (b.bindArgs cat) anti on
  | .orderBy r keys => .orderBy (r.bindArgs cat) keys
  | .distinct r => .distinct (r.bindArgs cat)
  | .aggregate r gs ms => Rel.pullArgs (r.arity cat) bindFuel (r.bindArgs cat) gs ms
  | .unnest r c => .unnest (r.bindArgs cat) c

theorem pullMeasures_length : ∀ {base : Nat} {ms : List Measure}, (pullMeasures base ms).length = ms.length
  | _, [] => rfl
  | _, _ :: _ => by simp [pullMeasures, pullMeasures_length]

theorem Rel.arity_pullArgs {cat : Catalog} {n fuel : Nat} {r : Rel} {gs : List Expr} {ms : List Measure} :
    (Rel.pullArgs n fuel r gs ms).arity cat = gs.length + ms.length := by
  unfold pullArgs; split <;> simp [arity, pullMeasures_length]

theorem Rel.arity_bindArgs {cat : Catalog} : ∀ r : Rel, (r.bindArgs cat).arity cat = r.arity cat
  | .read _ | .values _ _ => rfl
  | .aggregate _ _ _ => by simp only [bindArgs, arity_pullArgs, arity]
  | .emit r m => by simp only [bindArgs, arity_fuseEmit, arity]
  | .project r es => by
    simp only [bindArgs, arity]
    exact arity_bindProject bindFuel (arity_bindArgs r)
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .unnest r _ | .semi r _ _ _ => by
    simp [bindArgs, arity, arity_bindArgs r]
  | .window r _ _ fns => by simp [bindArgs, arity, arity_bindArgs r]
  | .cross a b | .join a b _ _ => by simp [bindArgs, arity, arity_bindArgs a, arity_bindArgs b]
  | .unionAll a _ => by simp [bindArgs, arity, arity_bindArgs a]

/-- **The pass computes the same rows**, with any functions: on every engine. -/
theorem Rel.evalI_bindArgs {I : Impl} {cat : Catalog} (hcat : cat.WF) :
    ∀ {r : Rel}, r.WF cat → (r.bindArgs cat).eval cat I = r.eval cat I
  | .read _, _ | .values _ _, _ => rfl
  | .project r es, hwf => by
    have ih := evalI_bindArgs hcat (I := I) hwf.1
    simp only [bindArgs]
    rw [evalI_bindProject bindFuel (by rw [ih]; exact evalI_arity hcat hwf.1)]
    simp only [eval, ih]
  | .filter r _, hwf | .orderBy r _, hwf | .unnest r _, hwf => by
    simp only [bindArgs, eval, evalI_bindArgs hcat hwf.1]
  | .distinct r, hwf | .fetch r _ _, hwf => by
    simp only [bindArgs, eval, evalI_bindArgs hcat (r := r) hwf]
  | .emit r m, hwf => by
    simp only [bindArgs, evalI_fuseEmit, eval, evalI_bindArgs hcat (r := r) hwf.1]
  | .window r _ _ _, hwf => by simp only [bindArgs, eval, evalI_bindArgs hcat hwf.1]
  | .aggregate r gs ms, hwf => by
    have ih := evalI_bindArgs hcat (I := I) hwf.1
    simp only [bindArgs]
    rw [evalI_pullArgs (by rw [ih]; exact evalI_arity hcat hwf.1) hwf.2.1 hwf.2.2]
    simp only [eval, ih]
  | .cross a b, hwf => by simp only [bindArgs, eval, evalI_bindArgs hcat hwf.1, evalI_bindArgs hcat hwf.2]
  | .unionAll a b, hwf => by
    simp only [bindArgs, eval, evalI_bindArgs hcat hwf.1, evalI_bindArgs hcat hwf.2.1]
  | .join a b ty _, hwf | .semi a b ty _, hwf => by
    cases ty <;> simp only [bindArgs, eval, evalI_bindArgs hcat hwf.1, evalI_bindArgs hcat hwf.2.1,
      arity_bindArgs]

/-- **The pass computes the same rows** in the reference. -/
theorem Rel.eval_bindArgs {cat : Catalog} (hcat : cat.WF) {r : Rel} (hwf : r.WF cat) :
    (r.bindArgs cat).eval cat = r.eval cat :=
  evalI_bindArgs hcat hwf

/-- **The pass raises exactly where the plan raises**, under any profile. -/
theorem Rel.raises_bindArgs {p : Profile} {cat : Catalog} (hcat : cat.WF) :
    ∀ {r : Rel}, r.WF cat → ((r.bindArgs cat).Raises p cat ↔ r.Raises p cat)
  | .read _, _ | .values _ _, _ => Iff.rfl
  | .project r es, hwf => by
    have ih := raises_bindArgs (p := p) hcat hwf.1
    have he := evalI_bindArgs (I := p.impl) hcat hwf.1
    simp only [bindArgs]
    rw [raises_bindProject bindFuel (by rw [he]; exact evalI_arity hcat hwf.1)]
    simp only [Raises, ih, he]
  | .filter r _, hwf => by
    simp only [bindArgs, Raises, raises_bindArgs hcat hwf.1, evalI_bindArgs hcat hwf.1]
  | .orderBy r _, hwf | .unnest r _, hwf | .window r _ _ _, hwf => by
    simp only [bindArgs, Raises, raises_bindArgs hcat hwf.1]
  | .distinct r, hwf | .fetch r _ _, hwf => by
    simp only [bindArgs, Raises, raises_bindArgs hcat (r := r) hwf]
  | .emit r m, hwf => by
    simp only [bindArgs, raises_fuseEmit, Raises, raises_bindArgs hcat (r := r) hwf.1]
  | .aggregate r gs ms, hwf => by
    have ih := raises_bindArgs (p := p) hcat hwf.1
    have he := evalI_bindArgs (I := p.impl) hcat hwf.1
    simp only [bindArgs]
    rw [raises_pullArgs (by rw [he]; exact evalI_arity hcat hwf.1) hwf.2.1 hwf.2.2]
    simp only [Raises, ih, he]
  | .cross a b, hwf => by
    simp only [bindArgs, Raises, raises_bindArgs hcat hwf.1, raises_bindArgs hcat hwf.2]
  | .unionAll a b, hwf => by
    simp only [bindArgs, Raises, raises_bindArgs hcat hwf.1, raises_bindArgs hcat hwf.2.1]
  | .join a b _ _, hwf | .semi a b _ _, hwf => by
    simp only [bindArgs, Raises, raises_bindArgs hcat hwf.1, raises_bindArgs hcat hwf.2.1,
      evalI_bindArgs hcat hwf.1, evalI_bindArgs hcat hwf.2.1]

/-- The pass reads the catalog's arities only (`Rel.arity_congr`). -/
theorem Rel.bindArgs_congr {c₁ c₂ : Catalog} (h : ∀ t, (c₁ t).arity = (c₂ t).arity) :
    ∀ r : Rel, r.bindArgs c₁ = r.bindArgs c₂
  | .read _ | .values _ _ => rfl
  | .project r es => by simp only [bindArgs, arity_congr h r, bindArgs_congr h r]
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .unnest r _ | .emit r _
  | .window r _ _ _ => by simp only [bindArgs, bindArgs_congr h r]
  | .aggregate r _ _ => by simp only [bindArgs, arity_congr h r, bindArgs_congr h r]
  | .cross a b | .join a b _ _ | .semi a b _ _ | .unionAll a b => by
    simp only [bindArgs, bindArgs_congr h a, bindArgs_congr h b]

end Substrait
