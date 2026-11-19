import Sverify.Core.AllowedNear
import Sverify.Core.NoDouble
import Sverify.Engines.Transfer

/-!
# Plans without doubles transfer to the reference (ruling 154)

A plan in which no double occurs (`Rel.mayDouble`) gives, under a profile's
table `t`, only results the reference allows, where the table that takes the
reference's choices at the options only doubles read (`floatOnlyOptions`)
and `t`'s elsewhere is within the reference at every option the plan reads
(`transferB`, decided per plan): `Rel.transfer_of_noDouble`.

The proof carries two facts through the plan together: no value holds a
double, and every call gives Lean's value. A call that gives another value
needs a behaviour the reference lacks, at an option whose scope holds
(`CallExtra`, `AggExtra`). At an option of `floatOnlyOptions` the scope needs a
double (`optionScope_floatOnly`); at any other the plan reads the option, and
`transferB` puts the behaviour in the reference's set. So neither arises, and
the plan runs on Lean's functions, which make no double from values without
one (`core/Sverify/Core/NoDouble.lean`).
-/

namespace Substrait
open Functions (Ctor)

/-- No value of the rows holds a double. -/
def NoDoubles (rows : Relation) : Prop := ∀ row ∈ rows, ∀ v ∈ row, v.hasDouble = false

theorem NoDoubles.sub {rows rows' : Relation} (h : NoDoubles rows) (hs : ∀ row ∈ rows', row ∈ rows) :
    NoDoubles rows' := fun row hr => h row (hs row hr)

theorem NoDoubles.perm {rows rows' : Relation} (h : NoDoubles rows) (hp : rows'.Perm rows) :
    NoDoubles rows' := h.sub fun _ hr => hp.mem_iff.mp hr

/-- At an option off `os`, `refAt` is `t`, so `LeAt` reads the same. -/
theorem ProfileTable.LeAt.of_refAt {t u : ProfileTable} {os : List String} {p : Read}
    (hp : p.2.1 ∉ os) (h : (t.refAt os).LeAt u p) : t.LeAt u p := by
  intro b hb
  rw [← ProfileTable.refAt_allows_of_not_mem hp] at hb
  exact h b hb

variable [Boxes.Ambient]

section
variable {t : ProfileTable}

/-- The premise of the transfer at a read: `t` with the reference's choices at
`floatOnlyOptions` is within the reference. -/
abbrev NearRef (t : ProfileTable) (p : Read) : Prop :=
  (t.refAt floatOnlyOptions).LeAt Profile.reference.table p

/-! ## No call is an extra -/

/-- **A call without doubles is the reference's**, where `t` with the
reference's choices at `floatOnlyOptions` is within the reference at the
call's options. -/
theorem CallExtra.false_of_noDouble {c : Ctor} {args : List Value}
    (hl : ∀ p ∈ ctorReads c, NearRef t p) (ha : ∀ v ∈ args, v.hasDouble = false)
    (hr : (c.result args).hasDouble = false) : ¬CallExtra t c args := by
  rintro ⟨row, hrow, os, hos, o, ho, hi, ⟨b, hb, hn⟩, hs⟩
  by_cases hf : o ∈ floatOnlyOptions
  · rw [optionScope_floatOnly hf hi ha hr] at hs; exact Bool.false_ne_true hs
  · have hp : (row.group, o, ([] : List Behaviour)) ∈ ctorReads c := by
      simp only [ctorReads, hrow, hos, Option.getD_some, List.mem_map, List.mem_filter]
      exact ⟨o, ⟨ho, optionApplies_of_scope hs⟩, rfl⟩
    exact hn ((hl _ hp).mem hi (by rw [ProfileTable.refAt_allows_of_not_mem hf]; exact hb))

theorem AggExtra.false_of_noDouble {f : AggFn} {vs : List Value}
    (hl : ∀ p ∈ ctorReads (.agg f), NearRef t p) (ha : ∀ v ∈ vs, v.hasDouble = false)
    (hr : (f.apply vs).hasDouble = false) : ¬AggExtra t f vs :=
  CallExtra.false_of_noDouble (c := .agg f) hl ha (by simpa [Functions.Ctor.result] using hr)

/-! ## Expressions and measures -/

variable {I : Impl}

/-- On a row without doubles, an expression without doubles gives Lean's value. -/
theorem Expr.evalI_noDouble (hI : I.Within t) : ∀ {e : Expr}, e.mayDouble = false →
    (∀ c ∈ e.ctors, ∀ p ∈ ctorReads c, NearRef t p) →
    ∀ {row : Row}, (∀ v ∈ row, v.hasDouble = false) → e.eval row I = e.eval row
  | .lit _, _, _, _, _ | .field _, _, _, _, _ => rfl
  | .un f a, he, hl, row, hr => by
    simp only [Expr.mayDouble, Bool.or_eq_false_iff] at he
    have ih := Expr.evalI_noDouble hI he.2 (fun c hc => hl c (List.mem_cons_of_mem _ hc)) hr
    have hv := Expr.eval_hasDouble he.2 hr
    simp only [Expr.eval, ih]
    refine (hI.1 f (a.eval row)).resolve_right (CallExtra.false_of_noDouble
      (hl _ (List.mem_cons_self ..)) (by simpa using hv) ?_)
    simpa [Functions.Ctor.result] using UnFn.apply_hasDouble he.1 hv
  | .bin f a b, he, hl, row, hr => by
    simp only [Expr.mayDouble, Bool.or_eq_false_iff] at he
    have iha := Expr.evalI_noDouble hI he.1.2
      (fun c hc => hl c (List.mem_cons_of_mem _ (List.mem_append_left _ hc))) hr
    have ihb := Expr.evalI_noDouble hI he.2
      (fun c hc => hl c (List.mem_cons_of_mem _ (List.mem_append_right _ hc))) hr
    have hva := Expr.eval_hasDouble he.1.2 hr
    have hvb := Expr.eval_hasDouble he.2 hr
    simp only [Expr.eval, iha, ihb]
    refine (hI.2 f (a.eval row) (b.eval row)).resolve_right (CallExtra.false_of_noDouble
      (hl _ (List.mem_cons_self ..)) (by simp [hva, hvb]) ?_)
    simpa [Functions.Ctor.result] using BinFn.apply_hasDouble he.1.1 hva hvb
  | .ifThen c a b, he, hl, row, hr => by
    simp only [Expr.mayDouble, Bool.or_eq_false_iff] at he
    simp only [Expr.eval,
      Expr.evalI_noDouble hI he.1.1 (fun x hx => hl x (by simp [Expr.ctors, hx])) hr,
      Expr.evalI_noDouble hI he.1.2 (fun x hx => hl x (by simp [Expr.ctors, hx])) hr,
      Expr.evalI_noDouble hI he.2 (fun x hx => hl x (by simp [Expr.ctors, hx])) hr]
  | .hof _ _ _, he, _, _, _ => by simp [Expr.mayDouble] at he

theorem evalI_noDouble_list (hI : I.Within t) {es : List Expr} (he : es.any Expr.mayDouble = false)
    (hl : ∀ c ∈ es.flatMap Expr.ctors, ∀ p ∈ ctorReads c, NearRef t p) {row : Row}
    (hr : ∀ v ∈ row, v.hasDouble = false) : es.map (·.eval row I) = es.map (·.eval row) :=
  List.map_congr_left fun e hmem => Expr.evalI_noDouble hI
    (by simp only [List.any_eq_false] at he; simpa using he e hmem)
    (fun c hc => hl c (List.mem_flatMap.mpr ⟨e, hmem, hc⟩)) hr

theorem eval_hasDouble_list {es : List Expr} (he : es.any Expr.mayDouble = false) {row : Row}
    (hr : ∀ v ∈ row, v.hasDouble = false) : ∀ v ∈ es.map (·.eval row), v.hasDouble = false := by
  intro v hv
  obtain ⟨e, hmem, rfl⟩ := List.mem_map.mp hv
  simp only [List.any_eq_false] at he
  exact Expr.eval_hasDouble (by simpa using he e hmem) hr

omit [Boxes.Ambient] in
/-- A measure's parts: no double in its function, argument and filter. -/
theorem Measure.mayDouble_parts {m : Measure} (hm : m.mayDouble = false) :
    m.fn.mayDouble = false ∧ m.arg.mayDouble = false ∧ ∀ c ∈ m.filter, c.mayDouble = false := by
  simp only [Measure.mayDouble, Bool.or_eq_false_iff] at hm
  refine ⟨hm.1.1, hm.1.2, fun c hc => ?_⟩
  have h := hm.2
  rw [hc] at h
  simpa using h

theorem Measure.inputsI_noDouble (hI : I.Within t) {m : Measure} (hm : m.mayDouble = false)
    (hl : ∀ p ∈ m.reads, NearRef t p) {rows : Relation} (hr : NoDoubles rows) :
    m.inputs rows I = m.inputs rows := by
  obtain ⟨-, ha, hf⟩ := Measure.mayDouble_parts hm
  have hla : ∀ c ∈ m.arg.ctors, ∀ p ∈ ctorReads c, NearRef t p := fun c hc p hp =>
    hl p (by simp only [Measure.reads, List.mem_append]; exact .inl (.inl (Expr.ctorReads_sub hc p hp)))
  have hk : m.kept rows I = m.kept rows := by
    unfold Measure.kept
    cases hc : m.filter with
    | none => rfl
    | some c =>
      refine List.filter_congr fun row hrow => ?_
      rw [Expr.evalI_noDouble hI (hf c hc) (fun x hx p hp => hl p (by
        simp only [Measure.reads, List.mem_append, hc, Option.map_some, Option.getD_some]
        exact .inl (.inr (Expr.ctorReads_sub hx p hp)))) (hr row hrow)]
  have hkr : NoDoubles (m.kept rows) := hr.sub fun row h => by
    unfold Measure.kept at h; split at h
    · exact h
    · exact (List.mem_filter.mp h).1
  unfold Measure.inputs
  simp only [hk, List.map_congr_left fun row hrow => Expr.evalI_noDouble hI ha hla (hkr row hrow)]

/-- An aggregate without doubles allows, under `t`, what the reference allows. -/
theorem AggFn.allowedP_noDouble {f : AggFn} (hf : f.mayDouble = false)
    (hl : ∀ p ∈ f.reads, NearRef t p) {vs : List Value} (hvs : ∀ v ∈ vs, v.hasDouble = false)
    {v : Value} (h : f.AllowedP t vs v) :
    f.AllowedP Profile.reference.table vs v ∧ v.hasDouble = false := by
  rcases h with h | h
  · have hp := (AggFn.allowedChoice_of_mayDouble hf t vs v).mp h
    exact ⟨.inl ((AggFn.allowedChoice_of_mayDouble hf _ vs v).mpr hp), hp.hasDouble hf hvs⟩
  · exact absurd h (AggExtra.false_of_noDouble (fun p hp => hl p (List.mem_append_left _ hp)) hvs
      (AggFn.apply_hasDouble hf hvs))

theorem Measure.allowedP_noDouble (hI : I.Within t) {m : Measure} (hm : m.mayDouble = false)
    (hl : ∀ p ∈ m.reads, NearRef t p) {rows : Relation} (hr : NoDoubles rows) {v : Value}
    (h : m.AllowedP t I rows v) :
    m.AllowedP Profile.reference.table Impl.lean rows v ∧ v.hasDouble = false := by
  obtain ⟨s, hs, hsort, ha⟩ := h
  have hsr := hr.perm hs
  rw [Measure.inputsI_noDouble hI hm hl hsr] at ha
  have hf := (Measure.mayDouble_parts hm).1
  obtain ⟨h1, h2⟩ := AggFn.allowedP_noDouble hf (fun p hp => hl p (List.mem_append_right _ hp))
    (Measure.inputs_hasDouble (Measure.mayDouble_parts hm).2.1 hsr) ha
  exact ⟨⟨s, hs, hsort, h1⟩, h2⟩

omit [Boxes.Ambient] in
theorem Row.canon_of_noDouble {row : Row} (h : ∀ v ∈ row, v.hasDouble = false) : row.canon = row := by
  simp only [Row.canon]
  exact (List.map_congr_left fun v hv => Value.canonV_of_hasDouble (h v hv)).trans (List.map_id _)

omit [Boxes.Ambient] in
/-- A representative of rows without doubles is one of them. -/
theorem IsReps.noDoubles {l reps : List Row} (h : IsReps Row.canon l reps) (hl : NoDoubles l) :
    NoDoubles reps := fun x hx => by
  obtain ⟨y, hy, -, hxy | hxy⟩ := h.2.1 x hx
  · exact hxy ▸ hl y hy
  · rw [hxy, Row.canon_of_noDouble (hl y hy)]; exact hl y hy

/-- Lean's own functions are within every table. -/
theorem Impl.lean_within (t : ProfileTable) : Impl.lean.Within t :=
  ⟨fun _ _ => .inl rfl, fun _ _ _ => .inl rfl⟩

/-! ## Aggregates, windows and sorts -/

theorem aggAllowedP_noDouble (hI : I.Within t) {gs : List Expr} {ms : List Measure}
    (hg : gs.any Expr.mayDouble = false) (hm : ms.any Measure.mayDouble = false)
    (hlg : ∀ c ∈ gs.flatMap Expr.ctors, ∀ p ∈ ctorReads c, NearRef t p)
    (hlm : ∀ p ∈ ms.flatMap Measure.reads, NearRef t p)
    {rows out : Relation} (hr : NoDoubles rows) (h : aggAllowedP t I gs ms rows out) :
    aggAllowedP Profile.reference.table Impl.lean gs ms rows out ∧ NoDoubles out := by
  have hk : ∀ row ∈ rows, groupKey gs row I = groupKey gs row := fun row hrow =>
    evalI_noDouble_list hI hg hlg (hr row hrow)
  have hgr : ∀ k, groupRows gs rows k I = groupRows gs rows k := fun k => by
    unfold groupRows; exact List.filter_congr fun row hrow => by rw [hk row hrow]
  have hgrn : ∀ k, NoDoubles (groupRows gs rows k) := fun k =>
    hr.sub fun _ h => (List.mem_filter.mp h).1
  have hms : ∀ {rows'}, NoDoubles rows' → ∀ m ∈ ms, ∀ v, m.AllowedP t I rows' v →
      m.AllowedP Profile.reference.table Impl.lean rows' v ∧ v.hasDouble = false :=
    fun hr' m hmem v hv => Measure.allowedP_noDouble hI
      (by simp only [List.any_eq_false] at hm; simpa using hm m hmem)
      (fun p hp => hlm p (List.mem_flatMap.mpr ⟨m, hmem, hp⟩)) hr' hv
  have hvs : ∀ {rows'} {vs : List Value}, NoDoubles rows' →
      Forall2 (fun m v => m.AllowedP t I rows' v) ms vs →
      Forall2 (fun m v => m.AllowedP Profile.reference.table Impl.lean rows' v) ms vs ∧
        ∀ v ∈ vs, v.hasDouble = false := fun hr' h2 =>
    ⟨Forall2.imp_mem (fun m hmem v hv => (hms hr' m hmem v hv).1) h2, fun v hv => by
      obtain ⟨m, hmem, hmv⟩ := Forall2.mem_right h2 hv
      exact (hms hr' m hmem v hmv).2⟩
  unfold aggAllowedP at h ⊢
  by_cases hge : gs.isEmpty = true
  · simp only [hge, ↓reduceIte] at h ⊢
    obtain ⟨vs, rfl, h2⟩ := h
    obtain ⟨h3, h4⟩ := hvs hr h2
    exact ⟨⟨vs, rfl, h3⟩, fun row hrow v hv => by
      rw [List.mem_singleton.mp hrow] at hv; exact h4 v hv⟩
  · simp only [Bool.not_eq_true] at hge
    simp only [hge, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨ks, hreps, h2⟩ := h
    rw [List.map_congr_left hk] at hreps
    have hks : NoDoubles ks := hreps.noDoubles fun row hrow v hv => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hrow
      exact eval_hasDouble_list hg (hr y hy) v hv
    refine ⟨⟨ks, hreps, Forall2.imp_mem (fun k _ row h' => ?_) h2⟩, fun row hrow => ?_⟩
    · obtain ⟨vs, hrow, hv⟩ := h'
      rw [hgr] at hv; exact ⟨vs, hrow, (hvs (hgrn k) hv).1⟩
    · obtain ⟨k, hk', vs, rfl, hv⟩ := Forall2.mem_right h2 hrow
      rw [hgr] at hv
      intro v hv'
      rcases List.mem_append.mp hv' with h | h
      · exact hks k hk' v h
      · exact (hvs (hgrn k) hv).2 v h

theorem WinFn.allowedP_noDouble {f : WinFn} (hf : f.mayDouble = false)
    (hl : ∀ p ∈ f.reads, NearRef t p) {pb pa : List Row} {x : Row}
    (hr : NoDoubles (pb ++ x :: pa)) {v : Value} (h : f.AllowedP t pb x pa v) :
    f.AllowedP Profile.reference.table pb x pa v ∧ v.hasDouble = false := by
  cases f with
  | agg m sort fr =>
    simp only [WinFn.mayDouble] at hf
    have hfr : NoDoubles (fr.rows sort pb x pa) := hr.sub fun _ h => Frame.mem_rows h
    simp only [WinFn.AllowedP] at h ⊢
    split at h
    · rename_i ho
      simp only [ho, ite_true]
      rcases h with h | ⟨hs, -⟩
      · have := Measure.allowedP_noDouble (Impl.lean_within t) hf
          (fun p hp => hl p (List.mem_append_left _ hp)) hfr h
        exact ⟨.inl this.1, this.2⟩
      · have := (Measure.mayDouble_parts hf).1
        rcases hs with hs | hs <;> simp [hs, AggFn.mayDouble] at this
    · rename_i ho
      simp only [ho]
      refine ⟨h, ?_⟩
      simp only [WinFn.Allowed] at h
      split at h
      · exact h.hasDouble (Measure.mayDouble_parts hf).1
          (Measure.inputs_hasDouble (Measure.mayDouble_parts hf).2.1 hfr)
      · rw [h]; exact WinFn.valueIn_hasDouble (f := .agg m sort fr) hf hr
  | _ => exact ⟨h, by rw [show v = _ from h]; exact WinFn.valueIn_hasDouble hf hr⟩

theorem windowRowsP_noDouble {part : List Nat} {fns : List WinFn}
    (hf : fns.any WinFn.mayDouble = false) (hl : ∀ p ∈ fns.flatMap WinFn.reads, NearRef t p) :
    ∀ {before after : List Row} {out : Relation}, NoDoubles before → NoDoubles after →
      windowRowsP t part fns before after out →
      windowRowsP Profile.reference.table part fns before after out ∧ NoDoubles out
  | _, [], out, _, _, h => by
    have h' : out = [] := h
    subst h'
    exact ⟨rfl, fun _ h => by simp at h⟩
  | before, x :: after, out, hb, ha, h => by
    obtain ⟨vs, rest, rfl, h2, h3⟩ := h
    have hx : ∀ v ∈ x, v.hasDouble = false := ha x (List.mem_cons_self ..)
    have hpart : NoDoubles (before.filter (samePart part x) ++ x :: after.filter (samePart part x)) :=
      fun row hrow => by
        simp only [List.mem_append, List.mem_cons, List.mem_filter] at hrow
        rcases hrow with ⟨h, -⟩ | rfl | ⟨h, -⟩
        · exact hb row h
        · exact hx
        · exact ha row (List.mem_cons_of_mem _ h)
    have hfn : ∀ f ∈ fns, ∀ v, WinFn.AllowedP t (before.filter (samePart part x)) x
        (after.filter (samePart part x)) f v →
        WinFn.AllowedP Profile.reference.table (before.filter (samePart part x)) x
          (after.filter (samePart part x)) f v ∧ v.hasDouble = false :=
      fun f hmem v hv => WinFn.allowedP_noDouble
        (by simp only [List.any_eq_false] at hf; simpa using hf f hmem)
        (fun p hp => hl p (List.mem_flatMap.mpr ⟨f, hmem, hp⟩)) hpart hv
    obtain ⟨h4, h5⟩ := windowRowsP_noDouble hf hl (before := before ++ [x])
      (fun row hrow => by
        rcases List.mem_append.mp hrow with h | h
        · exact hb row h
        · rw [List.mem_singleton.mp h]; exact hx)
      (fun row hrow => ha row (List.mem_cons_of_mem _ hrow)) h3
    refine ⟨⟨vs, rest, rfl, Forall2.imp_mem (fun f hmem v hv => (hfn f hmem v hv).1) h2, h4⟩, ?_⟩
    intro row hrow
    rcases List.mem_cons.mp hrow with rfl | hrow
    · intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact hx v h
      · obtain ⟨f, hmem, hfv⟩ := Forall2.mem_right h2 h
        exact (hfn f hmem v hfv).2
    · exact h5 row hrow

omit [Boxes.Ambient] in
/-- A sort reads no option of `floatOnlyOptions`. -/
theorem sortReads_not_floatOnly {keys : List SortKey} : ∀ p ∈ sortReads keys,
    p.2.1 ∉ floatOnlyOptions := by
  intro p hp
  simp only [sortReads, List.mem_append, List.mem_map] at hp
  rcases hp with ⟨k, -, rfl⟩ | hp
  · simp [floatOnlyOptions, aggInterpreted]
  · split at hp
    · rw [List.mem_singleton.mp hp]; simp [floatOnlyOptions, aggInterpreted]
    · simp at hp

omit [Boxes.Ambient] in
theorem any_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.any_cons, h a (List.mem_cons_self ..),
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

omit [Boxes.Ambient] in
theorem NoDoubles.cross {x y : Relation} (hx : NoDoubles x) (hy : NoDoubles y) :
    NoDoubles (crossRows x y) := fun row hrow v hv => by
  simp only [crossRows, List.mem_flatMap, List.mem_map] at hrow
  obtain ⟨a, ha, b, hb, rfl⟩ := hrow
  rcases List.mem_append.mp hv with h | h
  · exact hx a ha v h
  · exact hy b hb v h

end

end Substrait
