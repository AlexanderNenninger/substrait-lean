import Sverify.Engines.Sound
import SubstraitLean.MarginSound
import Sverify.Polars.Engine

/-!
# An engine's open double sums, discharged at a root aggregate (#1484, #929)

`Engine.contract_sound_runs_near` takes `Rel.FloatOpenSafeP` over the
engine's table: every result the table allows is, up to the observation, one
of the reference's orders. `transferB` gives it only where the engine's
choices are the reference's, and every engine's `sum_order` is not
(`EXACT` is the reference's alone, D25), so it held of no plan with a double
`SUM` or `AVG`.

`Rel.floatOpenSafeP_aggregate` discharges it for an aggregate at the root
whose input reads no `sum_order`: the engine's result is, column by column,
near the result of the same table with `sum_order` set to `EXACT`
(`ProfileTable.refSums`), and that table is the reference's at every
option the plan reads (`transferB`, decided). How near is the hypothesis
`Rel.SumsNear`: each double `SUM` and `AVG` the table allows, over each group
of each input the table allows, is within the observation's tolerance of the
correctly rounded one.
-/

namespace Substrait

section General
variable [Boxes.Ambient]

/-! ## The table with the reference's sums -/

/-- The options of a double `SUM` or `AVG` (group `agg.fsum`). -/
def fsumOptions : List String := (Functions.groups.lookup "agg.fsum").getD []

/-- The reference's choice at every option of a double `SUM` or `AVG`, as
rows of the group `agg.fsum`. -/
def fsumRows : List (Option String × String × Choice) :=
  fsumOptions.map fun o =>
    (some "agg.fsum", o, (Profile.reference.table.choice? "agg.fsum" o).getD (.oneOf []))

/-- `t` with the reference's choice at every option of a double `SUM` or `AVG`
(`EXACT` at `sum_order`, D25), and `t`'s own choices elsewhere. -/
def ProfileTable.refSums (t : ProfileTable) : ProfileTable :=
  { t with choices := fsumRows ++ t.choices }

omit [Boxes.Ambient] in
theorem fsumRows_find_group {g o : String} (hg : g ≠ "agg.fsum") :
    fsumRows.find? (fun x => x.1 == some g && x.2.1 == o) = none :=
  List.find?_eq_none.mpr fun x hx => by
    obtain ⟨o', _, rfl⟩ := List.mem_map.1 hx
    intro h; simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at h
    exact hg h.1.symm

omit [Boxes.Ambient] in
theorem fsumRows_find_dflt {o : String} :
    fsumRows.find? (fun x => x.1.isNone && x.2.1 == o) = none :=
  List.find?_eq_none.mpr fun x hx => by
    obtain ⟨o', _, rfl⟩ := List.mem_map.1 hx
    simp

omit [Boxes.Ambient] in
theorem ProfileTable.refSums_choice?_of_ne {t : ProfileTable} {g : String} (hg : g ≠ "agg.fsum")
    (o : String) : t.refSums.choice? g o = t.choice? g o := by
  simp only [choice?, refSums, List.find?_append, fsumRows_find_group hg, fsumRows_find_dflt,
    Option.none_or]

omit [Boxes.Ambient] in
/-- Away from the group `agg.fsum`, `refSums` allows what `t` does. -/
theorem ProfileTable.refSums_allows_of_ne {t : ProfileTable} {g : String} (hg : g ≠ "agg.fsum")
    (o : String) (ps : List Behaviour) : t.refSums.allows g o ps = t.allows g o ps := by
  simp only [allows, refSums_choice?_of_ne hg]

omit [Boxes.Ambient] in
theorem ProfileTable.refSums_allows_sum (t : ProfileTable) :
    t.refSums.allows "agg.fsum" "sum_order" [] = ["EXACT"] := rfl

omit [Boxes.Ambient] in
/-- Only `SUM` and `AVG` of doubles are in the group `agg.fsum`. -/
theorem Functions.fsum_rows : Functions.all.all (fun row => row.group != "agg.fsum" ||
    row.ctor == some (.agg .fsum) || row.ctor == some (.agg .avg)) = true := by decide +kernel

omit [Boxes.Ambient] in
open Functions in
theorem Functions.Ctor.eq_of_key_fsum {f₀ : AggFn} (hf₀ : f₀ = .fsum ∨ f₀ = .avg) {c : Ctor}
    (h : Ctor.agg f₀ = c.key) : c = .agg f₀ := by
  rcases hf₀ with rfl | rfl <;>
  · cases c with
    | agg f =>
      cases f with
      | bit b => cases b <;> simp [Ctor.key] at h
      | concat _ => simp [Ctor.key] at h
      | quantile _ _ _ => simp [Ctor.key] at h
      | _ => first | rfl | (simp only [Ctor.key, Ctor.agg.injEq] at h; exact absurd h AggFn.noConfusion)
    | _ => simp [Ctor.key] at h

omit [Boxes.Ambient] in
open Functions in
theorem Functions.group_fsum {c : Ctor} {row : Functions.FnRow} (h : Functions.rowOf c = some row)
    (hg : row.group = "agg.fsum") : c = .agg .fsum ∨ c = .agg .avg := by
  have hm := List.mem_of_find?_eq_some h
  have hc := List.find?_some h
  have hf := List.all_eq_true.mp Functions.fsum_rows row hm
  simp only [hg, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hf hc
  rcases hf with hf | hf <;> rw [hf] at hc <;> simp only [Option.some.injEq] at hc
  · exact .inl (Ctor.eq_of_key_fsum (.inl rfl) hc)
  · exact .inr (Ctor.eq_of_key_fsum (.inr rfl) hc)

theorem CallExtra.refSums {t : ProfileTable} {c : Functions.Ctor} {args : List Value}
    (hc : c ≠ .agg .fsum ∧ c ≠ .agg .avg) (h : CallExtra t c args) : CallExtra t.refSums c args :=
  let ⟨r, hr, os, hos, o, ho, hi, ⟨b, hb, hn⟩, hs⟩ := h
  ⟨r, hr, os, hos, o, ho, hi, ⟨b, by
    rwa [ProfileTable.refSums_allows_of_ne fun he => (Functions.group_fsum hr he).elim hc.1 hc.2],
    hn⟩, hs⟩

theorem AggExtra.refSums {t : ProfileTable} {f : AggFn} {vs : List Value}
    (hf : f ≠ .fsum ∧ f ≠ .avg) (h : AggExtra t f vs) : AggExtra t.refSums f vs :=
  let ⟨r, hr, os, hos, o, ho, hi, ⟨b, hb, hn⟩, hs⟩ := h
  ⟨r, hr, os, hos, o, ho, hi, ⟨b, by
    rw [ProfileTable.refSums_allows_of_ne fun he => (Functions.group_fsum hr he).elim
      (fun e => hf.1 (by injection e)) (fun e => hf.2 (by injection e))]
    exact hb, hn⟩, hs⟩

theorem Impl.Within.refSums {t : ProfileTable} {I : Impl} (h : I.Within t) :
    I.Within t.refSums :=
  ⟨fun f v => (h.1 f v).imp_right (CallExtra.refSums ⟨by simp, by simp⟩),
    fun f v w => (h.2 f v w).imp_right (CallExtra.refSums ⟨by simp, by simp⟩)⟩

/-- An aggregate other than a double `SUM` or `AVG` reads no `agg.fsum` option. -/
theorem AggFn.AllowedChoice.refSums {t : ProfileTable} {f : AggFn} {vs : List Value}
    {v : Value} (hf : f ≠ .fsum ∧ f ≠ .avg) (h : f.AllowedChoice t vs v) :
    f.AllowedChoice t.refSums vs v := by
  have e1 := ProfileTable.refSums_allows_of_ne (t := t) (g := "agg.var") (by decide) "stat_algo" []
  have e2 := ProfileTable.refSums_allows_of_ne (t := t) (g := "agg.stat") (by decide) "stat_algo" []
  have e3 := ProfileTable.refSums_allows_of_ne (t := t) (g := "agg.quant") (by decide)
    "quantile_interp" []
  cases f with
  | quantile c _ _ => cases c <;> simp_all [AggFn.AllowedChoice]
  | _ => simp_all [AggFn.AllowedChoice]

/-- Does `r` read no option of a double `SUM` or `AVG` (no double `SUM` or
`AVG` below the root aggregate)? -/
def Rel.noFsum (r : Rel) : Bool := r.reads.all fun p => p.1 != "agg.fsum"

theorem Rel.AllowedI.refSums {t : ProfileTable} {I : Impl} {cat : Catalog} {r : Rel}
    (hr : r.noFsum = true) {out : Relation} (h : r.AllowedI t I cat out) :
    r.AllowedI t.refSums I cat out := by
  refine Rel.AllowedI.monoOn (fun p hp => ?_) h
  have hne : p.1 ≠ "agg.fsum" := by simpa using List.all_eq_true.mp hr p hp
  intro b hb
  exact ⟨b, by rwa [ProfileTable.refSums_allows_of_ne hne], by simp [behaviourLe]⟩

/-! ## How near the engine's sums are -/

/-- The values a measure `m` of `aggregate r gs _` reads under `t`: those of
a group of an input `t` allows for `r` (the whole input without `GROUP BY`,
else the rows sharing some row's key), in any order, with functions `t`
allows. -/
def Rel.GroupInputs (t : ProfileTable) (cat : Catalog) (r : Rel) (gs : List Expr) (m : Measure)
    (vs : List Value) : Prop :=
  ∃ I, I.Within t ∧ ∃ i, r.AllowedI t I cat i ∧ ∃ grp, ((gs = [] ∧ grp = i) ∨ ∃ x ∈ i, grp = groupRows gs i (groupKey gs x I) I) ∧
    ∃ s, s.Perm grp ∧ vs = m.inputs s I

/-- A double `SUM` or `AVG` measure, in output column `col`, is near the
correctly rounded one, over the values it reads (`Rel.GroupInputs`): `t`
allows it no behaviour this does not model there (no NaN created, no
overflow, no empty group where `t` differs from the reference: `AggExtra`),
and every sum `t`'s `sum_order` allows is within the observation's tolerance
of `floatSumCR`, every mean of `floatAvgCR`. -/
def Measure.SumNear (q : Obs) (ctx : ObsCtx) (t : ProfileTable) (cat : Catalog) (r : Rel)
    (gs : List Expr) (col : Nat) (m : Measure) : Prop :=
  ∀ vs, r.GroupInputs t cat gs m vs → (m.fn = .fsum ∨ m.fn = .avg) →
    ¬AggExtra t m.fn vs ∧ (vs ≠ [] → ∀ b ∈ t.allows "agg.fsum" "sum_order" [], ∀ c,
      (m.fn = .fsum → SumOrder b vs c →
        Value.Equiv q ctx col (.float (floatSumCR vs)) (.float c)) ∧
      (m.fn = .avg → AvgOrder b vs c →
        Value.Equiv q ctx col (.float (floatAvgCR vs)) (.float c)))

/-- **The hypothesis of `Rel.floatOpenSafeP_aggregate`**: each measure of
`aggregate r gs ms`, the `j`-th in output column `gs.length + j`, is near
(`Measure.SumNear`). It says something only of a double `SUM` or `AVG`. -/
def Rel.SumsNear (q : Obs) (ctx : ObsCtx) (t : ProfileTable) (cat : Catalog) (r : Rel)
    (gs : List Expr) (ms : List Measure) : Prop :=
  ∀ j (m : Measure), ms[j]? = some m → m.SumNear q ctx t cat r gs (gs.length + j)

section Twin
variable {q : Obs} {ctx : ObsCtx} {t : ProfileTable} {cat : Catalog} {r : Rel} {gs : List Expr}
  {I : Impl} {i : Relation}

/-- A measure's value under `t` has a twin under `refSums`, near it. -/
theorem Measure.AllowedP.refSums (hc : ctx.ReflAt q) (hI : I.Within t) (hi : r.AllowedI t I cat i)
    {grp : Relation} (hg : (gs = [] ∧ grp = i) ∨ ∃ x ∈ i, grp = groupRows gs i (groupKey gs x I) I) {col : Nat} {m : Measure}
    (hn : m.SumNear q ctx t cat r gs col) {v : Value} (h : m.AllowedP t I grp v) :
    ∃ v₀, m.AllowedP t.refSums I grp v₀ ∧ Value.Equiv q ctx col v₀ v := by
  obtain ⟨s, hs, hsort, hv⟩ := h
  have hgi : r.GroupInputs t cat gs m (m.inputs s I) := ⟨I, hI, i, hi, grp, hg, s, hs, rfl⟩
  have hexact : "EXACT" ∈ t.refSums.allows "agg.fsum" "sum_order" [] := by
    rw [ProfileTable.refSums_allows_sum]; exact List.mem_singleton_self _
  rcases hv with hv | hx
  · by_cases hs1 : m.fn = .fsum
    · rw [hs1] at hv
      simp only [AggFn.AllowedChoice] at hv
      split at hv
      · rename_i he
        refine ⟨v, ⟨s, hs, hsort, .inl ?_⟩, .refl hc v⟩
        rw [hs1]; simp only [AggFn.AllowedChoice, he, ↓reduceIte]; exact hv
      · rename_i hne
        obtain ⟨b, hb, c, hso, rfl⟩ := hv
        refine ⟨.float (floatSumCR (m.inputs s I)), ⟨s, hs, hsort, .inl ?_⟩,
          (((hn _ hgi (.inl hs1)).2 hne b hb c).1 hs1 hso)⟩
        rw [hs1]; simp only [AggFn.AllowedChoice, hne, ↓reduceIte]
        exact ⟨"EXACT", hexact, _, by simp [SumOrder], rfl⟩
    · by_cases hs2 : m.fn = .avg
      · rw [hs2] at hv
        simp only [AggFn.AllowedChoice] at hv
        split at hv
        · rename_i he
          refine ⟨v, ⟨s, hs, hsort, .inl ?_⟩, .refl hc v⟩
          rw [hs2]; simp only [AggFn.AllowedChoice, he, ↓reduceIte]; exact hv
        · rename_i hne
          obtain ⟨b, hb, c, hso, rfl⟩ := hv
          refine ⟨.float (floatAvgCR (m.inputs s I)), ⟨s, hs, hsort, .inl ?_⟩,
            (((hn _ hgi (.inr hs2)).2 hne b hb c).2 hs2 hso)⟩
          rw [hs2]; simp only [AggFn.AllowedChoice, hne, ↓reduceIte]
          exact ⟨"EXACT", hexact, _, by simp [AvgOrder], rfl⟩
      · exact ⟨v, ⟨s, hs, hsort, .inl (AggFn.AllowedChoice.refSums ⟨hs1, hs2⟩ hv)⟩, .refl hc v⟩
  · by_cases hfa : m.fn = .fsum ∨ m.fn = .avg
    · exact ((hn _ hgi hfa).1 hx).elim
    · exact ⟨v, ⟨s, hs, hsort, .inr (hx.refSums ⟨fun e => hfa (.inl e), fun e => hfa (.inr e)⟩)⟩,
        .refl hc v⟩

/-- The measures of a group, each with its twin. -/
theorem measures_refSums (hc : ctx.ReflAt q) (hI : I.Within t) (hi : r.AllowedI t I cat i)
    {grp : Relation} (hg : (gs = [] ∧ grp = i) ∨ ∃ x ∈ i, grp = groupRows gs i (groupKey gs x I) I) :
    ∀ {col : Nat} {ms : List Measure} {vs : List Value},
      (∀ j (m : Measure), ms[j]? = some m → m.SumNear q ctx t cat r gs (col + j)) →
      Forall2 (fun m v => m.AllowedP t I grp v) ms vs →
      ∃ vs₀, Forall2 (fun m v => m.AllowedP t.refSums I grp v) ms vs₀ ∧
        Row.EquivFrom q ctx col vs₀ vs
  | _, [], [], _, .nil => ⟨[], .nil, trivial⟩
  | col, m :: ms, v :: vs, hn, .cons hm hms => by
    obtain ⟨v₀, hv₀, he⟩ := Measure.AllowedP.refSums hc hI hi hg (hn 0 m rfl) hm
    obtain ⟨vs₀, hvs₀, hes⟩ := measures_refSums hc hI hi hg (col := col + 1) (ms := ms)
      (fun j m' hj => by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hn (j + 1) m' hj) hms
    exact ⟨v₀ :: vs₀, .cons hv₀ hvs₀, he, hes⟩

end Twin

omit [Boxes.Ambient] in
theorem Row.EquivFrom.append_left {q : Obs} {ctx : ObsCtx} (hc : ctx.ReflAt q) :
    ∀ {col : Nat} (k : Row) {a b : Row}, Row.EquivFrom q ctx (col + k.length) a b →
      Row.EquivFrom q ctx col (k ++ a) (k ++ b)
  | _, [], _, _, h => by simpa using h
  | col, x :: k, _, _, h => ⟨.refl hc x, Row.EquivFrom.append_left hc (col := col + 1) k
      (by simpa [Nat.add_assoc, Nat.add_comm 1 k.length] using h)⟩

omit [Boxes.Ambient] in
theorem Forall2.exists_twin {α β γ : Type} {P : α → β → Prop} {Q : α → γ → Prop} {R : γ → β → Prop} :
    ∀ {as : List α} {bs : List β}, Forall2 P as bs →
      (∀ a ∈ as, ∀ b, P a b → ∃ c, Q a c ∧ R c b) → ∃ cs, Forall2 Q as cs ∧ Forall2 R cs bs
  | [], [], .nil, _ => ⟨[], .nil, .nil⟩
  | a :: as, b :: bs, .cons hab h, hf => by
    obtain ⟨c, hq, hr⟩ := hf a List.mem_cons_self b hab
    obtain ⟨cs, hqs, hrs⟩ := Forall2.exists_twin h fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')
    exact ⟨c :: cs, .cons hq hqs, .cons hr hrs⟩

/-- **The aggregate's twin**: a result `aggAllowedP` gives under `t` is, row
by row, near one it gives under `refSums`. -/
theorem aggAllowedP_refSums {q : Obs} {ctx : ObsCtx} {t : ProfileTable} {cat : Catalog}
    {r : Rel} {gs : List Expr} {ms : List Measure} {I : Impl} {i o : Relation}
    (hc : ctx.ReflAt q) (hI : I.Within t) (hi : r.AllowedI t I cat i)
    (hn : r.SumsNear q ctx t cat gs ms) (h : aggAllowedP t I gs ms i o) :
    ∃ o₀, aggAllowedP t.refSums I gs ms i o₀ ∧ Forall2 (Row.Equiv q ctx) o₀ o := by
  unfold aggAllowedP at h ⊢
  split
  · rename_i hge
    simp only [hge, ↓reduceIte] at h
    obtain ⟨vs, rfl, hf⟩ := h
    have hg0 : gs = [] := by simpa using hge
    obtain ⟨vs₀, hf₀, he⟩ := measures_refSums hc hI hi (.inl ⟨hg0, rfl⟩) (col := gs.length) hn hf
    have h0 : gs.length = 0 := by simp [hg0]
    exact ⟨[vs₀], ⟨vs₀, rfl, hf₀⟩, .cons (by rw [h0] at he; exact he) .nil⟩
  · rename_i hge
    simp only [hge, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨ks, hks, hf⟩ := h
    obtain ⟨o₀, hq, hr⟩ := Forall2.exists_twin (R := Row.Equiv q ctx)
      (Q := fun k row => ∃ vs, row = k ++ vs ∧
        Forall2 (fun m v => m.AllowedP t.refSums I (groupRows gs i k I) v) ms vs)
      hf fun k hk row ⟨vs, hrow, hms⟩ => by
      obtain ⟨y, hy, ey⟩ := hks.class_mem hk
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      have hgr : groupRows gs i k I = groupRows gs i (groupKey gs x I) I := by
        simp only [groupRows, ey]
      rw [hgr] at hms
      obtain ⟨vs₀, hf₀, he⟩ := measures_refSums hc hI hi (.inr ⟨x, hx, rfl⟩) (col := gs.length) hn hms
      rw [← hgr] at hf₀
      have hlen : k.length = gs.length := by
        rw [Row.length_of_canon ey]; simp [groupKey]
      refine ⟨k ++ vs₀, ⟨vs₀, rfl, hf₀⟩, ?_⟩
      rw [hrow]
      exact Row.EquivFrom.append_left hc (col := 0) k (by rw [Nat.zero_add, hlen]; exact he)
    exact ⟨o₀, ⟨ks, hks, hq⟩, hr⟩

/-- **An engine's open double sums at a root aggregate** (#1484, #929): every
result `t` allows for `aggregate r gs ms` is, up to `q` (rows as a multiset),
a result of one of the reference's orders, where

* the input `r` reads no option of a double `SUM` or `AVG` (`Rel.noFsum`: none
  below, in a window or an aggregate);
* `t` with exact sums is within the reference's choices at every option the
  plan reads (`transferB`, decided);
* the plan is closed (no open measure, `Rel.closedB`);
* each double `SUM` and `AVG` `t` allows is near the correctly rounded one
  over the groups it reads (`Rel.SumsNear`). -/
theorem Rel.floatOpenSafeP_aggregate {q : Obs} {ctx : ObsCtx} (hq : q.rows = .multiset)
    (hc : ctx.ReflAt q) {t : ProfileTable} {cat : Catalog} {r : Rel} {gs : List Expr}
    {ms : List Measure} (hr : r.noFsum = true)
    (htr : transferB (.aggregate r gs ms) Profile.reference.table t.refSums = true)
    (hcl : (Rel.aggregate r gs ms).closedB = true) (hn : r.SumsNear q ctx t cat gs ms) :
    (Rel.aggregate r gs ms).FloatOpenSafeP q ctx t cat := by
  rintro out ⟨I, hI, i, hi, o, hp, ha⟩
  obtain ⟨o₀, ha₀, he⟩ := aggAllowedP_refSums hc hI hi hn ha
  have h₀ : (Rel.aggregate r gs ms).AllowedP t.refSums cat o₀ :=
    ⟨I, hI.refSums, i, Rel.AllowedI.refSums hr hi, o₀, .refl _, ha₀⟩
  have href := Rel.allowedP_reference.mp (Rel.transfer_of_transferB htr h₀)
  refine ⟨o₀, Rel.allowed_orderAllowed hcl href, ?_⟩
  unfold Relation.Equiv; rw [hq]
  exact ⟨o, he, hp.symm⟩


end General

/-! ## An example: a double `SUM` on Polars

One table of one double, `1.0`, and `SUM(x)` over it, with the postcondition
`SUM(x) IS NULL OR NOT (SUM(x) < 0.0)`. Under Polars's table every
hypothesis of `Engine.contract_sound_runs_near` is discharged here, the side
condition by `Rel.floatOpenSafeP_aggregate`, and only D16's trusted claim
(`Engine.Runs`) stays open: Polars's `sum_order` is not the reference's, and
the sum it allows is the correctly rounded one up to its zero's sign
(`SumOrder.int_exact`). -/

section Example
attribute [local instance] Engine.exampleBoxes

def Engine.sumCat : Catalog := fun
  | "t" => ⟨1, [[.float FloatCode.one]]⟩
  | _ => ⟨0, []⟩

def Engine.sumPlan : Rel := .aggregate (.read "t") [] [{ fn := .fsum, arg := .field 0 }]

def Engine.sumA : String → List AVal := fun
  | "t" => [{ int := some ⟨some FloatCode.one, some FloatCode.one⟩, nk := some .float }]
  | _ => []

/-- `SUM(x) IS NULL OR NOT (SUM(x) < 0.0)`. -/
def Engine.sumPost : List Expr :=
  [.bin .or (.un .isNull (.field 0)) (.un .not (.bin .lt (.field 0) (.lit (.float 0))))]

/-- Rows as a multiset, values exactly. -/
def Engine.sumObs : Obs := { rows := .multiset }

def Engine.sumCtx : ObsCtx := {}

theorem Engine.sumCat_wf : Engine.sumCat.WF := by
  intro t row h
  unfold Engine.sumCat at h ⊢
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h; rfl
  · simp at h

theorem Engine.sumA_mem :
    ∀ t, ∀ row ∈ (Engine.sumCat t).rows, EnvMem (Engine.sumA t) row := by
  intro t row h i
  unfold Engine.sumCat at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    unfold Engine.sumA
    subst h; cases i <;>
      simp [AVal.Mem, AVal.MemR, AVal.MemNum, Bound.Mem, AVal.top] <;> decide +kernel
  · simp at h

theorem Engine.sumPlan_wf : Engine.sumPlan.WF Engine.sumCat := by
  simp [Engine.sumPlan, Rel.WF, Expr.refsLt, Rel.arity, Engine.sumCat, Measure.refsLt]

theorem Engine.sumCtx_reflAt : Engine.sumCtx.ReflAt Engine.sumObs :=
  ⟨fun n h => by simp [Engine.sumObs] at h, fun s h hne => absurd h.symm hne⟩

/-- Polars allows no other behaviour at the options of `SUM` of `1.0`: it
creates no NaN, does not overflow and the group is not empty. -/
theorem Engine.polars_sum_noExtra : ¬AggExtra Engine.polars.table .fsum [.float FloatCode.one] := by
  rintro ⟨r, hr, os, hos, o, ho, hi, ⟨b, hb, hn⟩, hs⟩
  have hg : (Functions.rowOf (.agg .fsum)).map (·.group) = some "agg.fsum" := by decide +kernel
  rw [hr] at hg
  simp only [Option.map_some, Option.some.injEq] at hg
  rw [hg] at hos hb hn
  have hos' : Functions.groups.lookup "agg.fsum" =
      some ["sum_order", "rounding", "nan_creation", "empty_group_aggregates", "float_overflow"] := by
    decide +kernel
  rw [hos'] at hos
  simp only [Option.some.injEq] at hos
  subst hos
  revert hs hn hb b hi
  revert o
  decide +kernel

theorem Engine.polars_sumsNear :
    (Rel.read "t").SumsNear Engine.sumObs Engine.sumCtx Engine.polars.table Engine.sumCat []
      [{ fn := .fsum, arg := .field 0 }] := by
  intro j m hj
  cases j with
  | succ j => simp at hj
  | zero =>
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
  subst hj
  rintro vs ⟨I, -, i, hi, grp, hg, s, hs, rfl⟩ -
  have hi' : i = [[.float FloatCode.one]] := List.perm_singleton.mp hi
  subst hi'
  have hg' : grp = [[.float FloatCode.one]] := by
    rcases hg with ⟨-, rfl⟩ | ⟨x, -, rfl⟩
    · rfl
    · simp [groupRows, groupKey]
  subst hg'
  have hs' : s = [[.float FloatCode.one]] := List.perm_singleton.mp hs
  subst hs'
  have hv : Measure.inputs { fn := .fsum, arg := .field 0 } [[.float FloatCode.one]] I =
      [.float FloatCode.one] := by
    simp [Measure.inputs, Measure.kept, Expr.eval]
  rw [hv]
  refine ⟨Engine.polars_sum_noExtra, fun _ b _ c => ⟨fun _ h => ?_, fun h => by cases h⟩⟩
  have hsi : SmallInts [.float FloatCode.one] := by
    refine ⟨fun v hv => ?_, by decide +kernel⟩
    simp only [List.mem_singleton] at hv
    exact ⟨_, hv, by unfold FloatCode.IsFin; decide +kernel, 1, by decide +kernel⟩
  have he := SumOrder.int_exact h hsi
  have hcr : floatSumCR [.float FloatCode.one] = FloatCode.one := by decide +kernel
  rw [hcr, show FloatCode.canon FloatCode.one = FloatCode.one by decide +kernel] at he
  have hc : c = FloatCode.one := by
    revert he; unfold FloatCode.canon FloatFormat.canon
    split
    · intro h; exact absurd h (by decide +kernel)
    · split
      · intro h; exact absurd h (by decide +kernel)
      · exact id
  show IntEquiv Engine.sumObs Engine.sumCtx 0 _ _
  simp only [IntEquiv, Engine.sumCtx, hcr, hc]

/-- **`Engine.contract_sound_runs_near` applies to a double `SUM`** (#1484):
on Polars's table, for `Engine.sumPlan`, every hypothesis is shown here but
D16's trusted claim (`Engine.Runs`), so the postcondition holds on the rows
Polars returns, whichever of its sums it computes. -/
theorem Engine.polars_sum_example {out : Relation}
    (hrun : Engine.polars.Runs Engine.sumCat Engine.sumPlan out) :
    ∀ row ∈ postRows Engine.sumPost [1] out, ∀ v ∈ row, v = .bool true :=
  Engine.contract_sound_runs_near Engine.sumCat_wf (S := Engine.sumA) (pre := fun _ => [])
    Engine.sumA_mem (by intro t row _ e he; simp at he) Engine.sumPlan_wf
    (q := Engine.sumObs) (ctx := Engine.sumCtx) rfl
    (Rel.floatOpenSafeP_aggregate rfl Engine.sumCtx_reflAt (by decide +kernel) (by decide +kernel)
      (by decide) Engine.polars_sumsNear)
    (sh := fun _ => none) (by simp) (by decide +kernel)
    (by simp [Rel.WF, Expr.refsLt, Rel.arity, Engine.sumCat, Engine.sumPlan, Engine.sumPost,
      Expr.narrow, Expr.narrowCmp, Expr.cmp?, Measure.refsLt])
    (WindowKeys.none_soundAll _) (by rw [Rel.aeval_csimp]; decide +kernel) hrun

end Example

end Substrait
