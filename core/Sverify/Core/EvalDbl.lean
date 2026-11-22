import Sverify.Core.Profile
import Sverify.Core.FloatDbl

/-!
# The reference stays on doubles, through plans (ruling 248, #271)

`Value.dbl` holds when every double in a value, inside lists and structs too,
is a double's code (`FloatFormat.Dbl`). On a catalog of such values, every
value the reference computes is one: each function's `apply` keeps them
(`UnFn.apply_dbl`, `BinFn.apply_dbl`, `AggFn.apply_dbl`), so `Expr.eval` and
`Rel.eval` do. The lemmas of `FloatDbl.lean` close each double arm.
-/

namespace Substrait

variable [Boxes.Ambient]

set_option exponentiation.threshold 2200

omit [Boxes.Ambient] in
@[simp] theorem Value.dbl_float (c : Int) : (Value.float c).dbl = true ↔ FloatCode.Dbl c := by
  simp [Value.dbl, FloatCode.Dbl, FloatFormat.Dbl]

omit [Boxes.Ambient] in
@[simp] theorem Value.dbl_list (vs : List Value) : (Value.list vs).dbl = true ↔ ∀ v ∈ vs, v.dbl = true := by
  simp [Value.dbl, Value.allDbl_iff]

omit [Boxes.Ambient] in
@[simp] theorem Value.dbl_struct (vs : List Value) :
    (Value.struct vs).dbl = true ↔ ∀ v ∈ vs, v.dbl = true := by
  simp [Value.dbl, Value.allDbl_iff]

omit [Boxes.Ambient] in
@[simp] theorem Value.dbl_null : Value.null.dbl = true := rfl
omit [Boxes.Ambient] in
@[simp] theorem Value.dbl_int (i : Int) : (Value.int i).dbl = true := rfl
omit [Boxes.Ambient] in
@[simp] theorem Value.dbl_bool (b : Bool) : (Value.bool b).dbl = true := rfl
omit [Boxes.Ambient] in
@[simp] theorem Value.dbl_str (t : String) : (Value.str t).dbl = true := rfl
omit [Boxes.Ambient] in
@[simp] theorem Value.dbl_date (c : Int) : (Value.date c).dbl = true := rfl
omit [Boxes.Ambient] in
@[simp] theorem Value.dbl_ts (c : Int) : (Value.ts c).dbl = true := rfl
omit [Boxes.Ambient] in
@[simp] theorem Value.dbl_tod (c : Int) : (Value.tod c).dbl = true := rfl
omit [Boxes.Ambient] in
@[simp] theorem Value.dbl_dec (s : Nat) (c : Int) : (Value.dec s c).dbl = true := rfl

omit [Boxes.Ambient] in
theorem Value.dbl_getD {vs : List Value} (h : ∀ v ∈ vs, v.dbl = true) (i : Nat) :
    (vs.getD i .null).dbl = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hv : vs[i]? with
  | none => rfl
  | some v => exact h v (List.mem_of_getElem? hv)

omit [Boxes.Ambient] in
theorem Value.dbl_listElement {vs : List Value} (h : ∀ v ∈ vs, v.dbl = true) (off : Int) :
    (Value.listElement off vs).dbl = true := by
  unfold Value.listElement; dsimp only
  split <;> (try split) <;> first | exact Value.dbl_getD h _ | rfl

omit [Boxes.Ambient] in
theorem Value.dbl_flatten {v : Value} (h : v.dbl = true) : v.flatten.dbl = true := by
  cases v <;> simp only [Value.flatten] <;> try rfl
  rename_i vs
  simp only [Value.dbl_list, List.mem_flatMap] at h ⊢
  rintro w ⟨x, hx, hw⟩
  have := h x hx
  split at hw
  · simp only [Value.dbl_list] at this; exact this w hw
  · simp at hw

/-- Black boxes give doubles: their types ask for it (ruling 251), and the
catalogue in scope is well-formed. -/
theorem Boxes.dblOut :
    (∀ n vs, (BlackBox.callScalar Boxes.Ambient.boxes n vs).dbl = true) ∧
      ∀ n vs, (BlackBox.callAgg Boxes.Ambient.boxes n vs).dbl = true :=
  ⟨BlackBox.callScalar_dbl Boxes.Ambient.wf, BlackBox.callAgg_dbl Boxes.Ambient.wf⟩

omit [Boxes.Ambient] in
theorem FloatCode.dbl_ofInt (i : Int) : FloatCode.Dbl (FloatCode.ofInt i) := intToDouble.dbl i

omit [Boxes.Ambient] in
theorem FloatCode.dbl_ofDecimal (i : Int) (s : Nat) : FloatCode.Dbl (FloatCode.ofDecimal i s) :=
  decToDouble.dbl i s

omit [Boxes.Ambient] in
theorem FMath.apply_dbl {f : FMath} {c r : Int} (h : f.apply c = some r) : FloatCode.Dbl r := by
  unfold FMath.apply at h
  split at h
  · cases h; exact FloatCode.dbl_ofFloat _
  · cases h

/-- **Each unary function keeps doubles.** -/
theorem UnFn.apply_dbl (f : UnFn) {v : Value} (h : v.dbl = true) :
    (f.apply v).dbl = true := by
  unfold UnFn.apply
  split
  all_goals first
    | rfl
    | exact h
    | exact Value.dbl_flatten h
    | exact Boxes.dblOut.1 _ _
    | (simp only [Value.dbl_float] at h ⊢
       first
         | exact FloatCode.dbl_negI h
         | exact FloatCode.dbl_floor h
         | exact FloatCode.dbl_ceil h
         | exact FloatCode.dbl_round h
         | exact FloatCode.dbl_roundEven h
         | exact FloatCode.dbl_roundTo _ h
         | exact FloatCode.dbl_ofInt _)
    | (simp only [Value.dbl_struct, Value.dbl_list] at h
       first
         | exact Value.dbl_getD h _
         | exact Value.dbl_listElement h _)
    | (split
       all_goals first
         | rfl
         | (simp only [Value.dbl_float]; exact FloatCode.dbl_ofDecimal _ _)
         | (simp only [Value.dbl_float]; exact FMath.apply_dbl (by assumption))
         | (split <;> rfl))

omit [Boxes.Ambient] in
theorem and3_dbl (a b : Value) : (and3 a b).dbl = true := by unfold and3; split <;> rfl
omit [Boxes.Ambient] in
theorem or3_dbl (a b : Value) : (or3 a b).dbl = true := by unfold or3; split <;> rfl

omit [Boxes.Ambient] in
theorem Value.pick_dbl (better : Value → Value → Bool) {a b : Value} (ha : a.dbl = true)
    (hb : b.dbl = true) : (Value.pick better a b).dbl = true := by
  unfold Value.pick; split
  · exact hb
  · exact ha
  · split
    · exact hb
    · exact ha

omit [Boxes.Ambient] in
theorem atan2?_dbl {y x r : Int} (h : atan2? y x = some r) : FloatCode.Dbl r := by
  unfold atan2? at h; split at h <;> cases h; exact FloatCode.dbl_lift₂ _ _ _

omit [Boxes.Ambient] in
theorem logb?_dbl {x b r : Int} (h : logb? x b = some r) : FloatCode.Dbl r := by
  unfold logb? at h; split at h <;> cases h; exact FloatCode.dbl_lift₂ _ _ _

omit [Boxes.Ambient] in
theorem ListOp.apply_dbl (op : ListOp) {a b : Value} (ha : a.dbl = true) (hb : b.dbl = true) :
    (op.apply a b).dbl = true := by
  cases op <;> simp only [ListOp.apply]
  · unfold Value.listPrepend; split <;> simp_all
  · unfold Value.listConcat; split
    · simp only [Value.dbl_list, List.mem_append] at ha hb ⊢
      rintro v (hv | hv)
      · exact ha v hv
      · exact hb v hv
    all_goals simp_all
  · unfold Value.listContains; split <;> (try split) <;> rfl
  · unfold Value.listPosition; split <;> (try split) <;> rfl

/-- **Each binary function keeps doubles.** -/
theorem BinFn.apply_dbl (f : BinFn) {a b : Value} (ha : a.dbl = true)
    (hb : b.dbl = true) : (f.apply a b).dbl = true := by
  unfold BinFn.apply
  split
  case _ => exact Boxes.dblOut.1 _ _
  case _ => exact Value.pick_dbl _ ha hb
  case _ => exact Value.pick_dbl _ ha hb
  all_goals (try split) <;> (try split) <;>
    (try simp_all [and3_dbl, or3_dbl, Value.ofLt3, FloatCode.dbl_fadd, FloatCode.dbl_fsub,
      FloatCode.dbl_fmul, FloatCode.dbl_fdiv, FloatCode.dbl_fmod, FloatCode.dbl_lift₂,
      ListOp.apply_dbl])
  all_goals (try split) <;> (try simp_all)
  all_goals first | exact atan2?_dbl (by assumption) | exact logb?_dbl (by assumption) | skip

/-! ## Aggregates -/

omit [Boxes.Ambient] in
theorem FloatCode.dbl_signed_posCode (neg : Prop) [Decidable neg] {m : Nat} (hm : fp64.magDbl m = true) :
    FloatCode.Dbl (if neg then -FloatCode.posCode m else FloatCode.posCode m) := by
  split
  · exact FloatCode.dbl_neg_posCode hm
  · exact FloatCode.dbl_posCode hm

omit [Boxes.Ambient] in
theorem varOf_dbl (sample sqrt : Bool) (vs : List Value) : (varOf sample sqrt vs).dbl = true := by
  unfold varOf
  split
  · rfl
  split
  · simpa using FloatCode.dbl_nan
  · dsimp only; split
    · simpa using FloatCode.dbl_posCode (FloatCode.magDbl_sqrtMag _ _)
    · simpa using FloatCode.dbl_ofExactDiv _ _

omit [Boxes.Ambient] in
theorem covOf_dbl (sample : Bool) (vs : List Value) : (covOf sample vs).dbl = true := by
  unfold covOf
  dsimp only
  split
  · rfl
  split
  · simpa using FloatCode.dbl_nan
  · simpa using FloatCode.dbl_ofExactDiv _ _

omit [Boxes.Ambient] in
theorem corrOf_dbl (vs : List Value) : (corrOf vs).dbl = true := by
  unfold corrOf
  dsimp only
  split
  · rfl
  split
  · simpa using FloatCode.dbl_nan
  · simp only [Value.dbl_float]
    apply FloatCode.dbl_signed_posCode
    rcases Nat.le_total (FloatCode.sqrtMag _ _) (2 ^ 1074) with h | h
    · rw [Nat.min_eq_left h]; exact FloatCode.magDbl_sqrtMag _ _
    · rw [Nat.min_eq_right h]
      simpa using fp64.magDbl_mul (by decide) (k := 1) (by decide) 1074

omit [Boxes.Ambient] in
theorem interpolate_dbl {l h w : Int} (hl : FloatCode.Dbl l) (hh : FloatCode.Dbl h) :
    FloatCode.Dbl (interpolate l h w) := by
  unfold interpolate
  dsimp only
  split
  · exact hl
  split
  · exact hh
  · exact FloatCode.dbl_fadd _ _

omit [Boxes.Ambient] in
theorem contValue_dbl (num scale : Nat) {s : List Value} (hs : ∀ v ∈ s, v.dbl = true) :
    (contValue num scale s).dbl = true := by
  unfold contValue
  split
  · rename_i l h w hc
    obtain ⟨hl, hh⟩ := contNeighbours_mem hc
    have hl' := hs _ hl; have hh' := hs _ hh
    simp only [Value.dbl_float] at hl' hh'
    split
    · simpa using hl'
    · simpa using interpolate_dbl hl' hh'
  · rfl

omit [Boxes.Ambient] in
theorem mem_sortVals {vs : List Value} {v : Value} : v ∈ sortVals vs ↔ v ∈ vs :=
  (List.mergeSort_perm _ _).mem_iff

/-- **Each aggregate keeps doubles.** -/
theorem AggFn.apply_dbl (f : AggFn) {vs : List Value}
    (h : ∀ v ∈ vs, v.dbl = true) : (f.apply vs).dbl = true := by
  unfold AggFn.apply
  split
  all_goals first
    | rfl
    | exact Boxes.dblOut.2 _ _
    | exact varOf_dbl _ _ _
    | exact covOf_dbl _ _
    | exact corrOf_dbl _
    | (simpa using FloatCode.dbl_floatSumCR _)
    | (simpa using FloatCode.dbl_floatAvgCR _)
    | (unfold sumOf; split <;> (try split) <;> rfl)
    | exact h _ (pickFold_mem _ _ _)
    | (simp only [Value.dbl_list]; exact h)
    | (split
       · exact h _ (List.getLast_mem _)
       · exact h _ (List.mem_cons_self ..))
    | exact contValue_dbl _ _ (fun v hv => h v (mem_sortVals.mp hv))
    | exact Value.dbl_getD (fun v hv => h v (mem_sortVals.mp hv)) _
    | (rename_i v vs
       unfold modeOf
       have := pickFold_mem (fun a b => (v :: vs).count a < (v :: vs).count b) v (dedup (v :: vs))
       rw [List.mem_cons, mem_dedup] at this
       rcases this with h' | h'
       · rw [h']; exact h _ (List.mem_cons_self ..)
       · exact h _ h')

/-! ## Expressions and plans

A plan's own constants are part of its input: its literals, its `VALUES` rows
and the defaults of `LAG` and `LEAD` (`Rel.litDbl`). The parser makes each
double of them with `ofFloat` (`FloatCode.dbl_ofFloat`). -/

/-- Every double among the expression's literals is a double's code. -/
def Expr.litDbl : Expr → Bool
  | .lit v => v.dbl
  | .field _ => true
  | .un _ a => a.litDbl
  | .bin _ a b => a.litDbl && b.litDbl
  | .ifThen c t e => c.litDbl && t.litDbl && e.litDbl
  | .hof _ l b => l.litDbl && b.litDbl

omit [Boxes.Ambient] in
theorem HoFn.apply_dbl (f : HoFn) {v : Value} (hv : v.dbl = true) {p : Value → Value}
    (hp : ∀ x ∈ v.elems, (p x).dbl = true) : (f.apply v p).dbl = true := by
  unfold HoFn.apply
  split
  · rename_i vs; cases vs <;> simp only [List.foldr_cons, List.foldr_nil]
    · rfl
    · exact or3_dbl _ _
  · rename_i vs; cases vs <;> simp only [List.foldr_cons, List.foldr_nil]
    · rfl
    · exact and3_dbl _ _
  · simp only [Value.dbl_list, List.mem_map]
    rintro w ⟨x, hx, rfl⟩; exact hp x hx
  · simp only [Value.dbl_list] at hv ⊢
    intro w hw; exact hv w (List.mem_filter.mp hw).1
  · rfl

/-- **An expression keeps doubles**: on a row of doubles, with literals of
doubles, its value holds doubles only. -/
theorem Expr.eval_dbl :
    ∀ (e : Expr) {row : Row}, e.litDbl = true → (∀ v ∈ row, v.dbl = true) → (e.eval row).dbl = true
  | .lit v, _, h, _ => h
  | .field i, _, _, hr => Value.dbl_getD hr i
  | .un f a, _, h, hr => UnFn.apply_dbl f (Expr.eval_dbl a h hr)
  | .bin f a b, _, h, hr => by
    simp only [Expr.litDbl, Bool.and_eq_true] at h
    exact BinFn.apply_dbl f (Expr.eval_dbl a h.1 hr) (Expr.eval_dbl b h.2 hr)
  | .ifThen c t e, _, h, hr => by
    simp only [Expr.litDbl, Bool.and_eq_true] at h
    simp only [Expr.eval]
    split
    · exact Expr.eval_dbl t h.1.2 hr
    · exact Expr.eval_dbl e h.2 hr
  | .hof f l b, row, h, hr => by
    simp only [Expr.litDbl, Bool.and_eq_true] at h
    have hl := Expr.eval_dbl l h.1 hr
    refine HoFn.apply_dbl f hl fun x hx => Expr.eval_dbl b h.2 ?_
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · cases hle : l.eval row <;> rw [hle] at hx hl <;> simp [Value.elems] at hx
      simp only [Value.dbl_list] at hl; exact hl _ hx
    · exact hr v hv

/-- A measure's values hold doubles on rows of doubles. -/
theorem Measure.eval_dbl (m : Measure) (hm : m.arg.litDbl = true)
    {rows : Relation} (hr : ∀ row ∈ rows, ∀ v ∈ row, v.dbl = true) : (m.eval rows).dbl = true := by
  have hin : ∀ rs : Relation, (∀ row ∈ rs, row ∈ rows) → ∀ v ∈ m.inputs rs, v.dbl = true := by
    intro rs hrs v hv
    obtain ⟨-, row, hrow, rfl⟩ := Measure.mem_inputs hv
    exact Expr.eval_dbl _ hm (hr row (hrs row hrow))
  have hsort : ∀ row ∈ rows.mergeSort (sortLe m.sort), row ∈ rows := fun _ h => List.mem_mergeSort.mp h
  unfold Measure.eval
  split <;> exact AggFn.apply_dbl _ (hin _ (by first | exact hsort | exact fun _ h => h))

/-- Every double among the window function's constants is a double's code. -/
def WinFn.litDbl : WinFn → Bool
  | .lag _ _ d | .lead _ _ d => d.dbl
  | .agg m _ _ => m.arg.litDbl
  | _ => true

omit [Boxes.Ambient] in
theorem floatRatio_dbl (a b : Nat) : (floatRatio a b).dbl = true := by
  simpa [floatRatio] using FloatCode.dbl_fdiv _ _

theorem WinFn.valueIn_dbl (f : WinFn) (hf : f.litDbl = true)
    {pb pa : List Row} {x : Row} (hr : ∀ row ∈ pb ++ x :: pa, ∀ v ∈ row, v.dbl = true) :
    (f.valueIn pb x pa).dbl = true := by
  have hx : ∀ v ∈ x, v.dbl = true := hr x (by simp)
  have hget : ∀ (o : Option Row) (d : Value) (c : Nat), d.dbl = true →
      (∀ y ∈ o, ∀ v ∈ y, v.dbl = true) → (o.elim d (·.getD c .null)).dbl = true := by
    intro o d c hd ho
    cases o with
    | none => exact hd
    | some y => exact Value.dbl_getD (ho y rfl) c
  have hframe : ∀ (fr : Frame) (sort : List SortKey), ∀ y ∈ fr.rows sort pb x pa, ∀ v ∈ y, v.dbl = true :=
    fun fr sort y hy => hr y (Frame.mem_rows hy)
  cases f <;> simp only [WinFn.valueIn, WinFn.litDbl] at hf ⊢
  case rowNumber | rank | denseRank | ntile => rfl
  case lag c k d =>
    refine hget _ d c hf fun y hy => ?_
    have := List.mem_of_getElem? hy
    rcases List.mem_cons.mp this with rfl | h
    · exact hx
    · exact hr y (by simp [List.mem_reverse.mp h])
  case lead c k d =>
    refine hget _ d c hf fun y hy => ?_
    exact hr y (by have := List.mem_of_getElem? hy; simp_all)
  case percentRank => split <;> exact floatRatio_dbl _ _
  case cumeDist => exact floatRatio_dbl _ _
  case agg m sort fr => exact Measure.eval_dbl m hf (hframe fr sort)
  case firstValue c sort fr =>
    exact hget _ _ c rfl fun y hy => hframe fr sort y (List.mem_of_mem_head? hy)
  case lastValue c sort fr =>
    exact hget _ _ c rfl fun y hy => hframe fr sort y (List.mem_of_getLast? hy)
  case nthValue c n sort fr =>
    exact hget _ _ c rfl fun y hy => hframe fr sort y (List.mem_of_getElem? hy)

/-- Every double among the plan's constants is a double's code. -/
def Rel.litDbl : Rel → Bool
  | .read _ => true
  | .values _ rows => rows.all (·.all Value.dbl)
  | .filter r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .unnest r _ => r.litDbl
  | .project r es => r.litDbl && es.all Expr.litDbl
  | .window r _ _ fns => r.litDbl && fns.all WinFn.litDbl
  | .aggregate r gs ms => r.litDbl && gs.all Expr.litDbl && ms.all (·.arg.litDbl)
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ => a.litDbl && b.litDbl

/-- Every double in the catalog's tables is a double's code. -/
def Catalog.Dbl (cat : Catalog) : Prop := ∀ t, ∀ row ∈ (cat t).rows, ∀ v ∈ row, v.dbl = true

/-- A relation of doubles. -/
abbrev Relation.Dbl (rows : Relation) : Prop := ∀ row ∈ rows, ∀ v ∈ row, v.dbl = true

/-- **The reference stays on doubles** (ruling 248, G2): on a catalog of
doubles, every double a plan with doubles for constants computes is a
double's code. -/
theorem Rel.eval_dbl {cat : Catalog} (hcat : cat.Dbl) :
    ∀ (r : Rel), r.litDbl = true → (r.eval cat).Dbl
  | .read t, _ => hcat t
  | .values _ rows, h => by
    simp only [Rel.litDbl, List.all_eq_true] at h
    intro row hrow v hv; exact h row hrow v hv
  | .filter r _, h => fun row hrow => Rel.eval_dbl hcat r h row (List.mem_filter.mp hrow).1
  | .semi r _ _ _, h => by
    simp only [Rel.litDbl, Bool.and_eq_true] at h
    exact fun row hrow => Rel.eval_dbl hcat r h.1 row (List.mem_filter.mp hrow).1
  | .project r es, h => by
    simp only [Rel.litDbl, Bool.and_eq_true, List.all_eq_true] at h
    intro row hrow
    simp only [Rel.eval, List.mem_map] at hrow
    obtain ⟨x, hx, rfl⟩ := hrow
    have hxd := Rel.eval_dbl hcat r h.1 x hx
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hxd v hv
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
      exact Expr.eval_dbl e (h.2 e he) hxd
  | .emit r m, h => by
    intro row hrow
    simp only [Rel.eval, List.mem_map] at hrow
    obtain ⟨x, hx, rfl⟩ := hrow
    intro v hv
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
    exact Value.dbl_getD (Rel.eval_dbl hcat r h x hx) i
  | .cross a b, h => by
    simp only [Rel.litDbl, Bool.and_eq_true] at h
    intro row hrow
    simp only [Rel.eval, mem_crossRows] at hrow
    obtain ⟨x, hx, y, hy, rfl⟩ := hrow
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact Rel.eval_dbl hcat a h.1 x hx v hv
    · exact Rel.eval_dbl hcat b h.2 y hy v hv
  | .join a b .inner _, h => by
    simp only [Rel.litDbl, Bool.and_eq_true] at h
    intro row hrow
    simp only [Rel.eval, List.mem_filter, mem_crossRows] at hrow
    obtain ⟨⟨x, hx, y, hy, rfl⟩, -⟩ := hrow
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact Rel.eval_dbl hcat a h.1 x hx v hv
    · exact Rel.eval_dbl hcat b h.2 y hy v hv
  | .join a b .left on, h => by
    simp only [Rel.litDbl, Bool.and_eq_true] at h
    intro row hrow
    simp only [Rel.eval, List.mem_flatMap] at hrow
    obtain ⟨x, hx, hrow⟩ := hrow
    have hxd := Rel.eval_dbl hcat a h.1 x hx
    unfold leftJoinRow at hrow
    dsimp only at hrow
    split at hrow
    · simp only [List.mem_singleton] at hrow
      subst hrow
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hxd v hv
      · rw [List.eq_of_mem_replicate hv]; rfl
    · simp only [List.mem_filter, List.mem_map] at hrow
      obtain ⟨⟨y, hy, rfl⟩, -⟩ := hrow
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hxd v hv
      · exact Rel.eval_dbl hcat b h.2 y hy v hv
  | .fetch r off cnt, h => by
    have ih := Rel.eval_dbl hcat r h
    intro row hrow
    simp only [Rel.eval] at hrow
    split at hrow
    · exact ih row (List.mem_of_mem_drop hrow)
    · exact ih row (List.mem_of_mem_drop (List.mem_of_mem_take hrow))
  | .unionAll a b, h => by
    simp only [Rel.litDbl, Bool.and_eq_true] at h
    intro row hrow
    simp only [Rel.eval] at hrow
    rcases List.mem_append.mp hrow with hrow | hrow
    · exact Rel.eval_dbl hcat a h.1 row hrow
    · exact Rel.eval_dbl hcat b h.2 row hrow
  | .window r part sort fns, h => by
    simp only [Rel.litDbl, Bool.and_eq_true, List.all_eq_true] at h
    have ih := Rel.eval_dbl hcat r h.1
    intro row hrow
    obtain ⟨b, x, a, he, hx, rfl⟩ := mem_windowEval hrow
    obtain ⟨-, -, hin⟩ := sorted_split he
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ih x hx v hv
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hv
      apply WinFn.valueIn_dbl f (h.2 f hf)
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.mem_filter] at hy
      apply ih y
      rcases hy with ⟨hy, -⟩ | rfl | ⟨hy, -⟩
      · exact hin y (.inr (.inl hy))
      · exact hx
      · exact hin y (.inr (.inr hy))
  | .orderBy r _, h => fun row hrow =>
    Rel.eval_dbl hcat r h row (List.mem_mergeSort.mp hrow)
  | .distinct r, h => fun row hrow => Rel.eval_dbl hcat r h row (canonReps_sub hrow)
  | .aggregate r gs ms, h => by
    simp only [Rel.litDbl, Bool.and_eq_true, List.all_eq_true] at h
    have ih := Rel.eval_dbl hcat r h.1.1
    have hms : ∀ (rows : Relation), (∀ row ∈ rows, row ∈ r.eval cat) →
        ∀ v ∈ ms.map (·.eval rows), v.dbl = true := by
      intro rows hrows v hv
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hv
      exact Measure.eval_dbl m (h.2 m hm) fun row hrow => ih row (hrows row hrow)
    intro row hrow
    simp only [Rel.eval, aggregateEval] at hrow
    split at hrow
    · simp only [List.mem_singleton] at hrow
      subst hrow
      exact hms _ fun _ h => h
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hrow
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (canonReps_sub hk)
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
        exact Expr.eval_dbl g (h.1.2 g hg) (ih x hx)
      · exact hms _ (fun row hrow => (List.mem_filter.mp hrow).1) v hv
  | .unnest r c, h => by
    have ih := Rel.eval_dbl hcat r h
    intro row hrow
    simp only [Rel.eval, List.mem_flatMap] at hrow
    obtain ⟨x, hx, hrow⟩ := hrow
    obtain ⟨vs, w, hl, hw, rfl⟩ := mem_unnestRow hrow
    have hxd := ih x hx
    have hld := Value.dbl_getD hxd c
    rw [hl, Value.dbl_list] at hld
    intro v hv
    rcases List.mem_or_eq_of_mem_set hv with hv | rfl
    · exact hxd v hv
    · exact hld v hw

/-- A row of doubles. -/
abbrev Row.Dbl (row : Row) : Prop := ∀ v ∈ row, v.dbl = true

/-- **Every row a plan's expressions are evaluated on is a row of doubles**,
on a catalog of doubles, with doubles for the plan's constants: what a
lowering stated on doubles needs (`Rel.evalI_mapExprs_rows`, ruling 254). -/
theorem Rel.exprRows_dbl {cat : Catalog} (hcat : cat.Dbl) :
    ∀ r : Rel, r.litDbl = true → r.ExprRows Row.Dbl cat
  | .read _, _ | .values _ _, _ => trivial
  | .filter r _, h => ⟨exprRows_dbl hcat r h, Rel.eval_dbl hcat r h⟩
  | .project r _, h => by
    simp only [Rel.litDbl, Bool.and_eq_true] at h
    exact ⟨exprRows_dbl hcat r h.1, Rel.eval_dbl hcat r h.1⟩
  | .aggregate r _ _, h => by
    simp only [Rel.litDbl, Bool.and_eq_true] at h
    exact ⟨exprRows_dbl hcat r h.1.1, Rel.eval_dbl hcat r h.1.1⟩
  | .emit r _, h | .orderBy r _, h | .distinct r, h | .unnest r _, h | .fetch r _ _, h =>
    exprRows_dbl hcat r h
  | .window r _ _ _, h => by
    simp only [Rel.litDbl, Bool.and_eq_true] at h
    exact exprRows_dbl hcat r h.1
  | .cross a b, h | .unionAll a b, h => by
    simp only [Rel.litDbl, Bool.and_eq_true] at h
    exact ⟨exprRows_dbl hcat a h.1, exprRows_dbl hcat b h.2⟩
  | .join a b _ _, h | .semi a b _ _, h => by
    simp only [Rel.litDbl, Bool.and_eq_true] at h
    refine ⟨exprRows_dbl hcat a h.1, exprRows_dbl hcat b h.2, fun x hx y hy v hv => ?_⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact Rel.eval_dbl hcat a h.1 x hx v hv
    · exact Rel.eval_dbl hcat b h.2 y hy v hv

end Substrait
