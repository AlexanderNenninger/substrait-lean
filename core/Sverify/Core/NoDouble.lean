import Sverify.Core.AllowedP
import Sverify.Core.Kinds

/-!
# Where a double may occur (ruling 154)

One family of tests for doubles: `Value.hasDouble` of a value, exact and
nested through lists and structs, and `mayDouble` of everything static
(`Kind`, `UnFn`, `BinFn`, `AggFn`, `WinFn`, `Expr`, `Measure`, `Rel`), a
syntactic test that holds wherever a double may arise: a double literal, a
function or cast that takes or gives one, a black box, a list or struct
access, or an input column whose kind may hold a double.

The lemmas here are about values: a function that is not `mayDouble` gives no
double on arguments without one, and a value of a kind that is not
`mayDouble` holds none. On such values the options that read only doubles
(`floatOnlyOptions`) are out of scope. `Rel.transfer_of_noDouble` builds on
them.
-/

namespace Substrait

/-! ## Values -/


theorem Value.anyDouble_eq_false {vs : List Value} :
    Value.anyDouble vs = false ↔ ∀ v ∈ vs, v.hasDouble = false := by
  induction vs with
  | nil => simp [Value.anyDouble]
  | cons v vs ih => simp [Value.anyDouble, ih]

@[simp] theorem Value.hasDouble_list (vs : List Value) :
    (Value.list vs).hasDouble = Value.anyDouble vs := by simp [Value.hasDouble]

@[simp] theorem Value.hasDouble_struct (vs : List Value) :
    (Value.struct vs).hasDouble = Value.anyDouble vs := by simp [Value.hasDouble]

mutual
theorem Value.hasNaN_of_hasDouble : ∀ {v : Value}, v.hasDouble = false → v.hasNaN = false
  | .float _, h => by simp [Value.hasDouble] at h
  | .list _, h | .struct _, h => by
    simp only [Value.hasNaN]; exact Value.anyNaN_of_anyDouble (by simpa using h)
  | .null, _ | .bool _, _ | .int _, _ | .date _, _ | .ts _, _ | .tod _, _ | .dec _ _, _
  | .str _, _ => rfl

theorem Value.anyNaN_of_anyDouble : ∀ {vs : List Value}, Value.anyDouble vs = false →
    Value.anyNaN vs = false
  | [], _ => rfl
  | _ :: _, h => by
    simp only [Value.anyDouble, Bool.or_eq_false_iff] at h
    simp [Value.anyNaN, Value.hasNaN_of_hasDouble h.1, Value.anyNaN_of_anyDouble h.2]
end

mutual
theorem Value.hasZero_of_hasDouble : ∀ {v : Value}, v.hasDouble = false → v.hasZero = false
  | .float _, h => by simp [Value.hasDouble] at h
  | .list _, h | .struct _, h => by
    simp only [Value.hasZero]; exact Value.anyZero_of_anyDouble (by simpa using h)
  | .null, _ | .bool _, _ | .int _, _ | .date _, _ | .ts _, _ | .tod _, _ | .dec _ _, _
  | .str _, _ => rfl

theorem Value.anyZero_of_anyDouble : ∀ {vs : List Value}, Value.anyDouble vs = false →
    Value.anyZero vs = false
  | [], _ => rfl
  | _ :: _, h => by
    simp only [Value.anyDouble, Bool.or_eq_false_iff] at h
    simp [Value.anyZero, Value.hasZero_of_hasDouble h.1, Value.anyZero_of_anyDouble h.2]
end

mutual
/-- Without a double, `canonV` changes nothing. -/
theorem Value.canonV_of_hasDouble : ∀ {v : Value}, v.hasDouble = false → v.canonV = v
  | .float _, h => by simp [Value.hasDouble] at h
  | .list vs, h => by
    rw [Value.canonV_list, Value.map_canonV_of_anyDouble (by simpa using h)]
  | .struct vs, h => by
    rw [Value.canonV_struct, Value.map_canonV_of_anyDouble (by simpa using h)]
  | .null, _ | .bool _, _ | .int _, _ | .date _, _ | .ts _, _ | .tod _, _ | .dec _ _, _
  | .str _, _ => by simp [Value.canonV]

theorem Value.map_canonV_of_anyDouble : ∀ {vs : List Value}, Value.anyDouble vs = false →
    vs.map Value.canonV = vs
  | [], _ => rfl
  | _ :: _, h => by
    simp only [Value.anyDouble, Bool.or_eq_false_iff] at h
    simp [Value.canonV_of_hasDouble h.1, Value.map_canonV_of_anyDouble h.2]
end

/-! ## Kinds -/

mutual
/-- A kind whose values may hold a double: a double, a kind the parser does
not know, an opaque column (any image), or a list or struct of such kinds. -/
def Kind.mayDouble : Kind → Bool
  | .float | .other | .opaque => true
  | .list k => k.mayDouble
  | .struct ks => Kind.anyMayDouble ks
  | _ => false

def Kind.anyMayDouble : List Kind → Bool
  | [] => false
  | k :: ks => k.mayDouble || Kind.anyMayDouble ks
end

mutual
/-- **A value of a kind without doubles holds none.** -/
theorem Value.hasDouble_of_hasKind : ∀ {k : Kind} {v : Value}, v.hasKind k = true →
    k.mayDouble = false → v.hasDouble = false
  | _, .null, _, _ | _, .bool _, _, _ | _, .int _, _, _ | _, .date _, _, _ | _, .ts _, _, _
  | _, .tod _, _, _ | _, .dec _ _, _, _ | _, .str _, _, _ => rfl
  | k, .float _, h, hk => by cases k <;> simp_all [Value.hasKind, Kind.mayDouble]
  | k, .list vs, h, hk => by
    cases k with
    | list k =>
      simp only [Value.hasDouble_list]
      exact Value.anyDouble_of_allHaveKind (by simpa [Value.hasKind] using h)
        (by simpa [Kind.mayDouble] using hk)
    | _ => simp_all [Value.hasKind, Kind.mayDouble]
  | k, .struct vs, h, hk => by
    cases k with
    | struct ks =>
      simp only [Value.hasDouble_struct]
      exact Value.anyDouble_of_fieldsHaveKinds (by simpa [Value.hasKind] using h)
        (by simpa [Kind.mayDouble] using hk)
    | _ => simp_all [Value.hasKind, Kind.mayDouble]

theorem Value.anyDouble_of_allHaveKind : ∀ {k : Kind} {vs : List Value},
    Value.allHaveKind k vs = true → k.mayDouble = false → Value.anyDouble vs = false
  | _, [], _, _ => rfl
  | _, _ :: _, h, hk => by
    simp only [Value.allHaveKind, Bool.and_eq_true] at h
    simp [Value.anyDouble, Value.hasDouble_of_hasKind h.1 hk, Value.anyDouble_of_allHaveKind h.2 hk]

theorem Value.anyDouble_of_fieldsHaveKinds : ∀ {ks : List Kind} {vs : List Value},
    Value.fieldsHaveKinds ks vs = true → Kind.anyMayDouble ks = false → Value.anyDouble vs = false
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, h, hk => by
    simp only [Value.fieldsHaveKinds, Bool.and_eq_true] at h
    simp only [Kind.anyMayDouble, Bool.or_eq_false_iff] at hk
    simp [Value.anyDouble, Value.hasDouble_of_hasKind h.1 hk.1,
      Value.anyDouble_of_fieldsHaveKinds h.2 hk.2]
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp [Value.fieldsHaveKinds] at h
end

/-! ## Functions -/

variable [Boxes.Ambient]

/-- Fail closed: the constructors that neither take nor give a double are
listed, and any other, a new one included, may. -/
def UnFn.mayDouble : UnFn → Bool
  | .not | .isNull | .neg | .narrow _ | .narrowOrNull _ | .wrap _ | .itos | .dtext | .dtextFull | .dwiden | .atUtc _
  | .upper | .lower | .length | .reverse | .ascii | .replace _ _ | .regexMatch _
  | .regexExtract _ _ | .regexReplace _ _ _ | .md5 | .sha256 | .datePart _ | .dateTrunc _
  | .toDate | .dayPart _ | .dayTrunc _ | .addMonths _ _ | .timeOfDay | .asTime | .dateTime
  | .epochUs | .strftime _ | .bucket _ _ | .decimal _ _ | .dkind _ _ | .dround _ | .dtrunc _
  | .cardinality | .raise _ | .fit _ _ | .isNum _ => false
  | _ => true

/-- Fail closed, as `UnFn.mayDouble`. -/
def BinFn.mayDouble : BinFn → Bool
  | .add | .sub | .mul | .eq | .lt | .and | .or | .idiv | .imod | .ipow | .concat | .strpos
  | .splitFirst | .startsWith | .endsWith | .like | .substr _ _ | .trim _ _ | .strRepeat | .ilike
  | .levenshtein | .dateAdd | .dateDiff | .bit _ | .dadd | .dsub | .dmul | .ddiv | .dmod
  | .greatest | .least => false
  | _ => true

/-- Fail closed, as `UnFn.mayDouble`. `MIN`, `MAX`, `QUANTILE_DISC` and the
picks pass their argument through. -/
def AggFn.mayDouble : AggFn → Bool
  | .count | .sum | .min | .max | .iavg | .bit _ | .pick _ | .concat _ | .mode
  | .quantile false _ _ => false
  | _ => true

def Expr.mayDouble : Expr → Bool
  | .lit v => v.hasDouble
  | .field _ => false
  | .un f a => f.mayDouble || a.mayDouble
  | .bin f a b => f.mayDouble || a.mayDouble || b.mayDouble
  | .ifThen c t e => c.mayDouble || t.mayDouble || e.mayDouble
  -- A lambda reads list elements, which may be doubles.
  | .hof _ _ _ => true

def Measure.mayDouble (m : Measure) : Bool :=
  m.fn.mayDouble || m.arg.mayDouble || (m.filter.map Expr.mayDouble).getD false

/-- Fail closed, as `UnFn.mayDouble`. The value functions pass their column
through. -/
def WinFn.mayDouble : WinFn → Bool
  | .rowNumber | .rank _ | .denseRank _ | .ntile _ | .firstValue _ _ _ | .lastValue _ _ _
  | .nthValue _ _ _ _ => false
  | .lag _ _ v | .lead _ _ v => v.hasDouble
  | .agg m _ _ => m.mayDouble
  | _ => true

/-- **May a double occur in `r`?** The tables' kinds are `tk`, as for
`Rel.inferKinds`; a column past a table's kinds may hold anything. -/
def Rel.mayDouble (cat : Catalog) (tk : String → List Kind) : Rel → Bool
  | .read t => (fitKinds (cat t).arity (tk t)).any Kind.mayDouble
  | .values _ rows => rows.any (·.any Value.hasDouble)
  | .filter r c => r.mayDouble cat tk || c.mayDouble
  | .project r es => r.mayDouble cat tk || es.any Expr.mayDouble
  | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .unnest r _ => r.mayDouble cat tk
  | .window r _ _ fns => r.mayDouble cat tk || fns.any WinFn.mayDouble
  | .aggregate r gs ms => r.mayDouble cat tk || gs.any Expr.mayDouble || ms.any Measure.mayDouble
  | .cross a b | .unionAll a b => a.mayDouble cat tk || b.mayDouble cat tk
  | .join a b _ on | .semi a b _ on => a.mayDouble cat tk || b.mayDouble cat tk || on.mayDouble

theorem UnFn.apply_hasDouble {f : UnFn} (hf : f.mayDouble = false) {v : Value}
    (hv : v.hasDouble = false) : (f.apply v).hasDouble = false := by
  unfold UnFn.apply
  split <;> (try split) <;> simp_all [Value.hasDouble, UnFn.mayDouble]

theorem BinFn.apply_hasDouble {f : BinFn} (hf : f.mayDouble = false) {v w : Value}
    (hv : v.hasDouble = false) (hw : w.hasDouble = false) : (f.apply v w).hasDouble = false := by
  unfold BinFn.apply
  split
  case _ => simp [BinFn.mayDouble] at hf
  case _ => rcases Value.pick_mem (better := Value.ltB) v w with h | h <;> rw [h] <;> assumption
  case _ => rcases Value.pick_mem (better := fun a b => Value.ltB b a) v w with h | h <;> rw [h] <;>
    assumption
  all_goals (try split) <;> (try split) <;> simp_all [Value.hasDouble, BinFn.mayDouble, and3, or3,
    Value.ofLt3] <;> (try split) <;> simp_all [Value.hasDouble]

omit [Boxes.Ambient] in
theorem Value.hasDouble_null : Value.null.hasDouble = false := by simp [Value.hasDouble]

omit [Boxes.Ambient] in
theorem hasDouble_getD {row : Row} (hr : ∀ v ∈ row, v.hasDouble = false) (i : Nat) :
    (row.getD i .null).hasDouble = false := by
  rw [List.getD_eq_getElem?_getD]
  cases h : row[i]? with
  | none => exact Value.hasDouble_null
  | some v => exact hr v (List.mem_of_getElem? h)

/-- **An expression without doubles gives none** on a row without one. -/
theorem Expr.eval_hasDouble : ∀ {e : Expr}, e.mayDouble = false → ∀ {row : Row},
    (∀ v ∈ row, v.hasDouble = false) → (e.eval row).hasDouble = false
  | .lit _, he, _, _ => by simp only [Expr.eval]; simpa [Expr.mayDouble] using he
  | .field i, _, _, hr => hasDouble_getD hr i
  | .un _ _, he, _, hr => by
    simp only [Expr.mayDouble, Bool.or_eq_false_iff] at he
    exact UnFn.apply_hasDouble he.1 (Expr.eval_hasDouble he.2 hr)
  | .bin _ _ _, he, _, hr => by
    simp only [Expr.mayDouble, Bool.or_eq_false_iff] at he
    exact BinFn.apply_hasDouble he.1.1 (Expr.eval_hasDouble he.1.2 hr) (Expr.eval_hasDouble he.2 hr)
  | .ifThen _ _ _, he, _, hr => by
    simp only [Expr.mayDouble, Bool.or_eq_false_iff] at he
    simp only [Expr.eval]
    split
    · exact Expr.eval_hasDouble he.1.2 hr
    · exact Expr.eval_hasDouble he.2 hr
  | .hof _ _ _, he, _, _ => by simp [Expr.mayDouble] at he

/-- The values a measure without doubles aggregates hold none. -/
theorem Measure.inputs_hasDouble {m : Measure} (hm : m.arg.mayDouble = false) {rows : Relation}
    (hr : ∀ row ∈ rows, ∀ v ∈ row, v.hasDouble = false) : ∀ v ∈ m.inputs rows, v.hasDouble = false := by
  have hk : ∀ row ∈ m.kept rows, ∀ v ∈ row, v.hasDouble = false := by
    unfold Measure.kept; split
    · exact hr
    · exact fun row h => hr row (List.mem_filter.mp h).1
  have hv : ∀ v ∈ ((m.kept rows).map fun row => m.arg.eval row).filter (· != .null),
      v.hasDouble = false := fun v h => by
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp (List.mem_filter.mp h).1
    exact Expr.eval_hasDouble hm (hk row hrow)
  unfold Measure.inputs
  split
  · exact fun v h => hv v (canonReps_sub h)
  · exact hv

theorem AggFn.apply_hasDouble {f : AggFn} (hf : f.mayDouble = false) {vs : List Value}
    (hvs : ∀ v ∈ vs, v.hasDouble = false) : (f.apply vs).hasDouble = false := by
  by_cases hc : f.classPick = true
  · rcases AggFn.apply_mem_of_classPick hc vs with h | h
    · exact hvs _ h
    · rw [h]; exact Value.hasDouble_null
  · cases vs with
    | nil => cases f <;> simp_all [AggFn.apply, AggFn.mayDouble, Value.hasDouble]
    | cons w ws =>
      cases f with
      | sum =>
        simp only [AggFn.apply, sumOf]; split <;> (try split) <;> simp [Value.hasDouble]
      | pick last =>
        simp only [AggFn.apply]; split
        · exact hvs _ (List.getLast_mem _)
        · exact hvs _ (List.mem_cons_self ..)
      | mode =>
        simp only [AggFn.apply, modeOf]
        rcases List.mem_cons.mp (pickFold_mem _ _ _) with h | h
        · rw [h]; exact hvs _ (List.mem_cons_self ..)
        · exact hvs _ (mem_dedup.mp h)
      | quantile cont _ _ => cases cont <;> simp_all [AggFn.mayDouble, AggFn.classPick]
      | _ => simp_all [AggFn.apply, AggFn.mayDouble, AggFn.classPick, Value.hasDouble]

/-- What the reference allows an aggregate without doubles holds no double. -/
theorem AggFn.Picks.hasDouble {f : AggFn} (hf : f.mayDouble = false) {vs : List Value}
    (hvs : ∀ v ∈ vs, v.hasDouble = false) {v : Value} (h : f.Picks vs v) : v.hasDouble = false := by
  have ha := AggFn.apply_hasDouble hf hvs
  rcases h with rfl | ⟨-, -, hv | rfl⟩
  · exact ha
  · exact hvs v hv
  · rwa [Value.canonV_of_hasDouble ha]

/-- An aggregate without doubles reads no choice of the table. -/
theorem AggFn.allowedChoice_of_mayDouble {f : AggFn} (hf : f.mayDouble = false) (t : ProfileTable)
    (vs : List Value) (v : Value) : f.AllowedChoice t vs v ↔ f.Picks vs v := by
  cases f <;> simp_all [AggFn.mayDouble, AggFn.AllowedChoice]
  case quantile cont _ _ => cases cont <;> simp_all

/-- The value of a window function without doubles, from rows without
doubles, holds none. -/
theorem WinFn.valueIn_hasDouble {f : WinFn} (hf : f.mayDouble = false) {pb pa : List Row} {x : Row}
    (hr : ∀ row ∈ pb ++ x :: pa, ∀ v ∈ row, v.hasDouble = false) :
    (f.valueIn pb x pa).hasDouble = false := by
  have hcol : ∀ (o : Option Row) (d : Value) (c : Nat), d.hasDouble = false →
      (∀ y ∈ o, y ∈ pb ++ x :: pa) → (o.elim d (·.getD c .null)).hasDouble = false := by
    intro o d c hd ho
    cases o with
    | none => exact hd
    | some y => exact hasDouble_getD (hr y (ho y rfl)) c
  have hfr : ∀ (fr : Frame) sort, ∀ row ∈ fr.rows sort pb x pa, ∀ v ∈ row, v.hasDouble = false :=
    fun _ _ row h => hr row (Frame.mem_rows h)
  cases f with
  | lag c k d | lead c k d =>
    simp only [WinFn.mayDouble] at hf
    refine hcol _ _ _ hf fun y hy => ?_
    have := List.mem_of_getElem? hy
    simp only [List.mem_cons, List.mem_reverse] at this
    rcases this with h | h <;> simp [h]
  | agg m sort fr =>
    simp only [WinFn.mayDouble, Measure.mayDouble, Bool.or_eq_false_iff] at hf
    have hrows : ∀ rows : Relation, (∀ row ∈ rows, row ∈ fr.rows sort pb x pa) →
        (m.fn.apply (m.inputs rows)).hasDouble = false := fun rows hs =>
      AggFn.apply_hasDouble hf.1.1 (Measure.inputs_hasDouble hf.1.2 fun row h => hfr fr sort row (hs row h))
    simp only [WinFn.valueIn, Measure.eval]
    split <;> rename_i heq <;> first
      | (rw [← heq]; exact hrows _ fun row h => List.mem_mergeSort.mp h)
      | exact hrows _ fun row h => h
  | firstValue c sort fr =>
    exact hcol _ _ _ Value.hasDouble_null fun y hy => Frame.mem_rows (List.mem_of_mem_head? hy)
  | lastValue c sort fr =>
    exact hcol _ _ _ Value.hasDouble_null fun y hy => Frame.mem_rows (List.mem_of_getLast? hy)
  | nthValue c n sort fr =>
    exact hcol _ _ _ Value.hasDouble_null fun y hy => Frame.mem_rows (List.mem_of_getElem? hy)
  | _ => simp_all [WinFn.mayDouble, WinFn.valueIn, Value.hasDouble]

/-! ## The options that read only doubles -/

/-- **The options a plan without doubles never meets** (ruling 154, K1): those
`AggFn.AllowedP` interprets, which only aggregates of doubles read, and those
whose scope needs a double (`optionScope_floatOnly`). -/
def floatOnlyOptions : List String := aggInterpreted ++ ["zero_sign", "nan_order", "nan_equality"]

/-- Off `aggInterpreted`, the options of `floatOnlyOptions` are out of scope at
a call whose arguments and result hold no double. An option joins
`floatOnlyOptions` only with its case here. -/
theorem optionScope_floatOnly {o : String} (ho : o ∈ floatOnlyOptions) (hi : o ∉ aggInterpreted)
    {c : Functions.Ctor} {args : List Value} (ha : ∀ v ∈ args, v.hasDouble = false)
    (hr : (c.result args).hasDouble = false) : optionScope o c args = false := by
  have ha' := Value.anyDouble_eq_false.mpr ha
  simp only [floatOnlyOptions, List.mem_append] at ho
  rcases ho with ho | ho
  · exact absurd ho hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> simp [optionScope, Value.anyZero_of_anyDouble ha',
    Value.hasZero_of_hasDouble hr, Value.anyNaN_of_anyDouble ha']

/-! ## A table with the reference's choices at some options -/

/-- `t` with the reference's rows at the options `os`, at every group, and its
own rows elsewhere (ruling 154, D3). -/
def ProfileTable.refAt (t : ProfileTable) (os : List String) : ProfileTable :=
  { t with choices := Profile.reference.table.choices.filter (fun x => x.2.1 ∈ os) ++
      t.choices.filter (fun x => x.2.1 ∉ os) }

omit [Boxes.Ambient] in
theorem find?_filter_of_imp {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x, p x = true → q x = true) :
    (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hp : p x = true
    · simp [h x hp, hp]
    · by_cases hq : q x = true <;> simp [hq, hp, ih]

omit [Boxes.Ambient] in
theorem find?_filter_none {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x, p x = true → q x = false) :
    (l.filter q).find? p = none :=
  List.find?_eq_none.mpr fun x hx hp => by simp [h x hp] at hx

omit [Boxes.Ambient] in
theorem ProfileTable.refAt_choice?_of_not_mem {t : ProfileTable} {os : List String} {o : String}
    (ho : o ∉ os) (g : String) : (t.refAt os).choice? g o = t.choice? g o := by
  have hn : ∀ x : Option String × String × Choice, x.2.1 = o → decide (x.2.1 ∈ os) = false :=
    fun x hx => by simp [hx, ho]
  have hy : ∀ x : Option String × String × Choice, x.2.1 = o → decide (x.2.1 ∉ os) = true :=
    fun x hx => by simp [hx, ho]
  simp only [choice?, refAt, List.find?_append]
  rw [find?_filter_none (fun x hp => hn x (by simp_all)), find?_filter_none (fun x hp => hn x (by simp_all)),
    find?_filter_of_imp (fun x hp => hy x (by simp_all)), find?_filter_of_imp (fun x hp => hy x (by simp_all))]
  simp

omit [Boxes.Ambient] in
theorem ProfileTable.refAt_choice?_of_mem {t : ProfileTable} {os : List String} {o : String}
    (ho : o ∈ os) (g : String) : (t.refAt os).choice? g o = Profile.reference.table.choice? g o := by
  have hy : ∀ x : Option String × String × Choice, x.2.1 = o → decide (x.2.1 ∈ os) = true :=
    fun x hx => by simp [hx, ho]
  have hn : ∀ x : Option String × String × Choice, x.2.1 = o → decide (x.2.1 ∉ os) = false :=
    fun x hx => by simp [hx, ho]
  simp only [choice?, refAt, List.find?_append]
  rw [find?_filter_none (fun x hp => hn x (by simp_all)), find?_filter_none (fun x hp => hn x (by simp_all)),
    find?_filter_of_imp (fun x hp => hy x (by simp_all)), find?_filter_of_imp (fun x hp => hy x (by simp_all))]
  simp

omit [Boxes.Ambient] in
/-- Off `os`, `refAt` allows what `t` does. -/
theorem ProfileTable.refAt_allows_of_not_mem {t : ProfileTable} {os : List String} {o : String}
    (ho : o ∉ os) (g : String) (ps : List Behaviour) : (t.refAt os).allows g o ps = t.allows g o ps := by
  simp only [allows, refAt_choice?_of_not_mem ho]

omit [Boxes.Ambient] in
/-- At `os`, `refAt` allows what the reference does. -/
theorem ProfileTable.refAt_allows_of_mem {t : ProfileTable} {os : List String} {o : String}
    (ho : o ∈ os) (g : String) (ps : List Behaviour) :
    (t.refAt os).allows g o ps = Profile.reference.table.allows g o ps := by
  simp only [allows, refAt_choice?_of_mem ho]

end Substrait
