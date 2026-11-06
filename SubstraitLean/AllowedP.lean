import SubstraitLean.Allowed
import SubstraitLean.Options

/-!
# What a profile allows (#444, step 1c)

`Rel.Allowed` is the reference's relation. `Rel.AllowedP t` is the same
relation with every choice point read from a profile's table `t`
(`SubstraitLean/Options.lean`):

* a call takes the reference's value, or, where `t` allows a behaviour of
  one of its group's options that the reference does not, a value of that
  behaviour (`Impl.Within`). The values of those behaviours are not modelled
  yet, so such a call may take any value: an over-approximation that each
  engine profile narrows as its behaviours get their semantics (step 3a);
* `sum_order`, `stat_algo` and `quantile_interp` give the doubles a `SUM`,
  `AVG`, statistical aggregate or `QUANTILE_CONT` may return;
* `null_order` gives an `ORDER BY` key's NULL placement, from the key's own
  where it states one; `clustered` allows a clustered key's groups in any
  order.

Three theorems:

* `Rel.AllowedP_mono`: a table that allows no more (`ProfileTable.Le`) allows
  no more results. Its premise is decidable (`ProfileTable.le_of_leB`).
* `Rel.allowedP_reference`: under `Profile.reference.table`, `AllowedP` is
  `Rel.Allowed`, so `Rel.eval_allowed`, `Rel.allowed_perm_eval` and
  `Rel.Refines` hold of it as they are.
* `Rel.allowed_core`: hence everything the reference allows the core allows.

`Rel.RefinesP` is `⊑` on (profile, plan) pairs (`docs/core-semantics.md`,
"Translations between profiles"), on results; raise sets come with the
engine profiles of step 3. -/

namespace Substrait

/-! ## The relational options' behaviours -/

/-- The doubles a `SUM` of `vs` gives under a `sum_order` behaviour. -/
def SumOrder (b : Behaviour) (vs : List Value) (c : Int) : Prop :=
  if b = "ANY" ∨ b = "PAIRWISE" then FloatSums vs c
  else if b = "SEQUENTIAL" then ∃ ws, ws.Perm vs ∧ c = floatSum ws
  -- Not modelled here (Kahan's compensated sum, a constant run's product):
  -- any double. `float-bounds` bounds both (`StdModel.Summed`).
  else True

/-- What a statistical aggregate gives under a `stat_algo` behaviour. An
engine's own algorithm (`WELFORD_CHAN`) is not modelled here: it meets the
generic properties (`StatProps`), which is all this allows of it. -/
def StatAlgo (b : Behaviour) (f : AggFn) (vs : List Value) (v : Value) : Prop :=
  if b = "GENERIC" ∨ b = "WELFORD_CHAN" then StatProps f vs v else True

/-- What `QUANTILE_CONT` gives under a `quantile_interp` behaviour: a double
between the neighbours, which DuckDB's linear interpolation is (clamped). -/
def QuantInterp (b : Behaviour) (num scale : Nat) (vs : List Value) (v : Value) : Prop :=
  if b = "BETWEEN" ∨ b = "LINEAR" then contAllowed num scale (sortVals vs) v else True

/-- The options `AggFn.AllowedP` interprets. -/
def aggInterpreted : List String := ["sum_order", "stat_algo", "quantile_interp"]

/-- Does `t` allow an aggregate a behaviour the reference does not, at an
option `AggFn.AllowedP` does not interpret (`overflow`, `avg_int_result`,
`empty_group_aggregates`, …)? Then it may give any value, as a call may
(`CallExtra`). -/
def AggExtra (t : ProfileTable) (f : AggFn) : Prop :=
  ∃ r, Functions.rowOf (.agg f) = some r ∧ ∃ os, Functions.groups.lookup r.group = some os ∧
    ∃ o ∈ os, o ∉ aggInterpreted ∧ ∃ b ∈ t.allows r.group o [],
      b ∉ Profile.reference.table.allows r.group o []

/-! ## Aggregates -/

/-- `AggFn.Allowed` with the choices of `t` at the options it interprets. -/
def AggFn.AllowedChoice (t : ProfileTable) (f : AggFn) (vs : List Value) (v : Value) : Prop :=
  match f with
  | .fsum => if vs = [] then v = .null else
      ∃ b ∈ t.allows "agg.fsum" "sum_order" [], ∃ c, SumOrder b vs c ∧ v = .int c
  | .avg => if vs = [] then v = .null else
      ∃ b ∈ t.allows "agg.fsum" "sum_order" [], ∃ c, SumOrder b vs c ∧
        v = .int (FloatCode.lift₂ (· / ·) c (FloatCode.ofInt vs.length))
  | .var _ _ => ∃ b ∈ t.allows "agg.var" "stat_algo" [], StatAlgo b f vs v
  | .cov _ | .corr => ∃ b ∈ t.allows "agg.stat" "stat_algo" [], StatAlgo b f vs v
  | .quantile true num scale => if vs = [] then v = .null else
      ∃ b ∈ t.allows "agg.quant" "quantile_interp" [], QuantInterp b num scale vs v
  | _ => v = f.apply vs

/-- `AggFn.Allowed` with the choices of `t`, or any value where `t` allows a
behaviour this does not model (`AggExtra`). -/
def AggFn.AllowedP (t : ProfileTable) (f : AggFn) (vs : List Value) (v : Value) : Prop :=
  f.AllowedChoice t vs v ∨ AggExtra t f

/-- `Measure.Allowed` with the choices of `t` and the functions of `I`. -/
def Measure.AllowedP (t : ProfileTable) (I : Impl) (m : Measure) (rows : Relation)
    (v : Value) : Prop :=
  ∃ s, s.Perm rows ∧ (m.fn.sorts = true → s.Pairwise (sortLe m.sort · · = true)) ∧
    m.fn.AllowedP t (m.inputs s I) v

/-- `aggAllowed` with the choices of `t` and the functions of `I`. -/
def aggAllowedP (t : ProfileTable) (I : Impl) (gs : List Expr) (ms : List Measure)
    (rows out : Relation) : Prop :=
  if gs.isEmpty then ∃ vs, out = [vs] ∧ Forall2 (fun m v => m.AllowedP t I rows v) ms vs
  else Forall2 (fun k row => ∃ vs, row = k ++ vs ∧
      Forall2 (fun m v => m.AllowedP t I (groupRows gs rows k I) v) ms vs)
    (dedup (rows.map fun row => groupKey gs row I)) out

/-! ## Sorts -/

/-- The NULL placement a key asks for: none where it leaves it open. -/
def SortKey.nullPrefs (k : SortKey) : List Behaviour :=
  if k.nullsOpen then [] else [if k.nullsFirst then "NULLS_FIRST" else "NULLS_LAST"]

/-- May the key put NULLs first (`nf`) under `t`? -/
def NullOk (t : ProfileTable) (k : SortKey) (nf : Bool) : Prop :=
  (if nf then "NULLS_FIRST" else "NULLS_LAST") ∈ t.allows "rel.sort" "null_order" k.nullPrefs

/-- The orders `t` allows for an `ORDER BY` on `keys`: a NULL placement per
key that `t` allows, a clustered key's groups in any order (where `t` allows
clustering), ties in any order. -/
def SortedP (t : ProfileTable) (keys : List SortKey) (out : Relation) : Prop :=
  ∃ cmp, ValidCmp cmp ∧ ∃ nfs, Forall2 (NullOk t) keys nfs ∧
    (∀ k ∈ keys, k.clustered = true → "ADJACENT" ∈ t.allows "rel.sort" "clustered" []) ∧
    out.Pairwise (sortLeWith cmp (keys.zip nfs) · · = true)

/-! ## Calls -/

/-- Does `t` allow a call of `c` a behaviour the reference does not? Then the
call may give another value than the reference's. -/
def CallExtra (t : ProfileTable) (c : Functions.Ctor) : Prop :=
  ∃ r, Functions.rowOf c = some r ∧ ∃ os, Functions.groups.lookup r.group = some os ∧
    ∃ o ∈ os, o ∉ aggInterpreted ∧ ∃ b ∈ t.allows r.group o [],
      b ∉ Profile.reference.table.allows r.group o []

/-- The functions `I` are ones `t` allows: each call gives the reference's
value, unless `t` allows it another behaviour. -/
def Impl.Within (t : ProfileTable) (I : Impl) : Prop :=
  (∀ f v, I.un f v = f.apply v ∨ CallExtra t (.un f)) ∧
    ∀ f v w, I.bin f v w = f.apply v w ∨ CallExtra t (.bin f)

/-! ## Plans -/

/-- `Rel.Allowed` with the choices of `t` and the functions of `I`. -/
def Rel.AllowedI (t : ProfileTable) (I : Impl) (cat : Catalog) : Rel → Relation → Prop
  | .read tb, out => out.Perm (cat tb).rows
  | .values _ rows, out => out.Perm rows
  | .filter r c, out => ∃ i, r.AllowedI t I cat i ∧ out = i.filter fun row => (c.eval row I).isTrue
  | .project r es, out => ∃ i, r.AllowedI t I cat i ∧
      out = i.map fun row => row ++ es.map (·.eval row I)
  | .emit r m, out => ∃ i, r.AllowedI t I cat i ∧ out = i.map fun row => m.map (row.getD · .null)
  | .cross a b, out => ∃ x y, a.AllowedI t I cat x ∧ b.AllowedI t I cat y ∧
      out.Perm (crossRows x y)
  | .join a b .inner on, out => ∃ x y, a.AllowedI t I cat x ∧ b.AllowedI t I cat y ∧
      out.Perm ((crossRows x y).filter fun row => (on.eval row I).isTrue)
  | .join a b .left on, out => ∃ x y, a.AllowedI t I cat x ∧ b.AllowedI t I cat y ∧
      out.Perm (x.flatMap fun row => leftJoinRow on (b.arity cat) y row I)
  | .fetch r off cnt, out => ∃ i, r.AllowedI t I cat i ∧ out = match cnt with
      | none => i.drop off
      | some n => (i.drop off).take n
  | .unionAll a b, out => ∃ x y, a.AllowedI t I cat x ∧ b.AllowedI t I cat y ∧ out.Perm (x ++ y)
  | .window r part sort fns, out => ∃ i, r.AllowedI t I cat i ∧ ∃ s, s.Perm i ∧
      s.Pairwise (sortLe sort · · = true) ∧ out.Perm (windowRows part fns [] s)
  | .semi a b anti on, out => ∃ x y, a.AllowedI t I cat x ∧ b.AllowedI t I cat y ∧
      out.Perm (x.filter fun row => hasMatch on y row I != anti)
  | .orderBy r keys, out => ∃ i, r.AllowedI t I cat i ∧ out.Perm i ∧ SortedP t keys out
  | .distinct r, out => ∃ i, r.AllowedI t I cat i ∧ out.Perm (dedup i)
  | .aggregate r gs ms, out => ∃ i, r.AllowedI t I cat i ∧ ∃ o, out.Perm o ∧
      aggAllowedP t I gs ms i o
  | .unnest r c, out => ∃ i, r.AllowedI t I cat i ∧ out.Perm (i.flatMap (unnestRow c))

/-- **The results the profile `t` allows** for `r` on `cat`: those of some
functions `t` allows. -/
def Rel.AllowedP (t : ProfileTable) (cat : Catalog) (r : Rel) (out : Relation) : Prop :=
  ∃ I, I.Within t ∧ r.AllowedI t I cat out

/-! ## Monotonicity -/

theorem Forall2.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → Forall2 S l l'
  | _, _, .nil => .nil
  | _, _, .cons hab t => .cons (h _ _ hab) (Forall2.imp h t)

section Mono
variable {t u : ProfileTable} (h : t.Le u)
include h

theorem AggExtra.mono {f : AggFn} : AggExtra t f → AggExtra u f :=
  fun ⟨r, hr, os, hos, o, ho, hi, b, hb, hn⟩ => ⟨r, hr, os, hos, o, ho, hi, b, h _ _ _ _ hb, hn⟩

theorem AggFn.AllowedChoice.mono {f : AggFn} {vs : List Value} {v : Value} :
    f.AllowedChoice t vs v → f.AllowedChoice u vs v := by
  have hb : ∀ {g o : String} {P : Behaviour → Prop}, (∃ b ∈ t.allows g o [], P b) →
      ∃ b ∈ u.allows g o [], P b := fun ⟨b, hb, rest⟩ => ⟨b, h _ _ _ _ hb, rest⟩
  intro hf
  cases f
  case quantile cont num scale =>
    cases cont
    · exact hf
    · simp only [AggFn.AllowedChoice] at hf ⊢
      split at hf
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by assumption))]; exact hf
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by assumption))]; exact hb hf
  case fsum | avg =>
    simp only [AggFn.AllowedChoice] at hf ⊢
    split at hf
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by assumption))]; exact hf
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by assumption))]; exact hb hf
  case var | cov | corr => exact hb hf
  all_goals exact hf

theorem AggFn.AllowedP.mono {f : AggFn} {vs : List Value} {v : Value} :
    f.AllowedP t vs v → f.AllowedP u vs v :=
  Or.imp (AggFn.AllowedChoice.mono h) (AggExtra.mono h)

theorem Measure.AllowedP.mono {I : Impl} {m : Measure} {rows : Relation} {v : Value} :
    m.AllowedP t I rows v → m.AllowedP u I rows v := fun ⟨s, hs, hsort, hf⟩ =>
  ⟨s, hs, hsort, AggFn.AllowedP.mono h hf⟩

theorem aggAllowedP.mono {I : Impl} {gs : List Expr} {ms : List Measure} {rows out : Relation} :
    aggAllowedP t I gs ms rows out → aggAllowedP u I gs ms rows out := by
  unfold aggAllowedP
  split
  · rintro ⟨vs, rfl, hv⟩
    exact ⟨vs, rfl, Forall2.imp (fun _ _ => Measure.AllowedP.mono h) hv⟩
  · exact Forall2.imp fun _ _ ⟨vs, hrow, hv⟩ =>
      ⟨vs, hrow, Forall2.imp (fun _ _ => Measure.AllowedP.mono h) hv⟩

theorem SortedP.mono {keys : List SortKey} {out : Relation} :
    SortedP t keys out → SortedP u keys out := fun ⟨cmp, hc, nfs, hn, hcl, hs⟩ =>
  ⟨cmp, hc, nfs, Forall2.imp (fun _ _ hk => h _ _ _ _ hk) hn,
    fun k hk hck => h _ _ _ _ (hcl k hk hck), hs⟩

theorem Impl.Within.mono {I : Impl} : I.Within t → I.Within u := by
  have hx : ∀ c, CallExtra t c → CallExtra u c := fun _ ⟨r, hr, os, hos, o, ho, hi, b, hb, hn⟩ =>
    ⟨r, hr, os, hos, o, ho, hi, b, h _ _ _ _ hb, hn⟩
  exact fun ⟨hu, hb⟩ => ⟨fun f v => (hu f v).imp_right (hx _),
    fun f v w => (hb f v w).imp_right (hx _)⟩

theorem Rel.AllowedI.mono {I : Impl} {cat : Catalog} :
    ∀ {r : Rel} {out : Relation}, r.AllowedI t I cat out → r.AllowedI u I cat out
  | .read _, _, ho | .values _ _, _, ho => ho
  | .filter _ _, _, ⟨i, hi, ho⟩ | .project _ _, _, ⟨i, hi, ho⟩ | .emit _ _, _, ⟨i, hi, ho⟩
  | .fetch _ _ _, _, ⟨i, hi, ho⟩ | .distinct _, _, ⟨i, hi, ho⟩ | .unnest _ _, _, ⟨i, hi, ho⟩ =>
    ⟨i, Rel.AllowedI.mono hi, ho⟩
  | .cross _ _, _, ⟨x, y, hx, hy, ho⟩ | .unionAll _ _, _, ⟨x, y, hx, hy, ho⟩
  | .semi _ _ _ _, _, ⟨x, y, hx, hy, ho⟩ | .join _ _ .inner _, _, ⟨x, y, hx, hy, ho⟩
  | .join _ _ .left _, _, ⟨x, y, hx, hy, ho⟩ =>
    ⟨x, y, Rel.AllowedI.mono hx, Rel.AllowedI.mono hy, ho⟩
  | .window _ _ _ _, _, ⟨i, hi, ho⟩ => ⟨i, Rel.AllowedI.mono hi, ho⟩
  | .orderBy _ _, _, ⟨i, hi, hp, hs⟩ => ⟨i, Rel.AllowedI.mono hi, hp, SortedP.mono h hs⟩
  | .aggregate _ _ _, _, ⟨i, hi, o, hp, ha⟩ =>
    ⟨i, Rel.AllowedI.mono hi, o, hp, aggAllowedP.mono h ha⟩

/-- **Monotonicity**: a profile whose choices are within another's allows no
more results. -/
theorem Rel.AllowedP_mono {cat : Catalog} {r : Rel} {out : Relation} :
    r.AllowedP t cat out → r.AllowedP u cat out := fun ⟨I, hI, ho⟩ =>
  ⟨I, Impl.Within.mono h hI, Rel.AllowedI.mono h ho⟩

end Mono

/-! ## The reference -/

/-! The reference's functions are `Impl.lean`, and `Expr.eval`, `Rel.eval` and
their helpers are the `Impl.lean` instances of one definition: the agreement
lemmas below hold by `rfl`, kept for one release. -/

theorem Expr.evalI_lean (row : Row) (e : Expr) : e.eval row Impl.lean = e.eval row := rfl

theorem evalI_lean_fun :
    (fun (e : Expr) row => e.eval row Impl.lean) = fun e row => e.eval row := rfl

theorem leftJoinRowI_lean (on : Expr) (n : Nat) (ys : Relation) (x : Row) :
    leftJoinRow on n ys x Impl.lean = leftJoinRow on n ys x := rfl

theorem hasMatchI_lean (on : Expr) (ys : Relation) (x : Row) :
    hasMatch on ys x Impl.lean = hasMatch on ys x := rfl

theorem Measure.inputsI_lean (m : Measure) (rows : Relation) :
    m.inputs rows Impl.lean = m.inputs rows := rfl

theorem groupKeyI_lean (gs : List Expr) (row : Row) : groupKey gs row Impl.lean = groupKey gs row :=
  rfl

theorem groupRowsI_lean (gs : List Expr) (rows : Relation) (k : Row) :
    groupRows gs rows k Impl.lean = groupRows gs rows k := rfl

/-- The reference's choices of the relational options. -/
theorem reference_allows_sum : Profile.reference.table.allows "agg.fsum" "sum_order" [] = ["ANY"] := by
  decide +kernel
theorem reference_allows_var :
    Profile.reference.table.allows "agg.var" "stat_algo" [] = ["GENERIC"] := by decide +kernel
theorem reference_allows_stat :
    Profile.reference.table.allows "agg.stat" "stat_algo" [] = ["GENERIC"] := by decide +kernel
theorem reference_allows_quant :
    Profile.reference.table.allows "agg.quant" "quantile_interp" [] = ["BETWEEN"] := by decide +kernel
theorem reference_allows_clustered :
    Profile.reference.table.allows "rel.sort" "clustered" [] = ["ADJACENT"] := by decide +kernel

theorem AggExtra.not_reference (f : AggFn) : ¬AggExtra Profile.reference.table f :=
  fun ⟨_, _, _, _, _, _, _, _, hb, hn⟩ => hn hb

theorem AggFn.allowedP_reference (f : AggFn) (vs : List Value) (v : Value) :
    f.AllowedP Profile.reference.table vs v ↔ f.Allowed vs v := by
  rw [AggFn.AllowedP, or_iff_left (AggExtra.not_reference f)]
  cases f
  case quantile cont num scale =>
    cases cont <;> simp [AggFn.AllowedChoice, AggFn.Allowed, reference_allows_quant, QuantInterp]
  all_goals simp [AggFn.AllowedChoice, AggFn.Allowed, reference_allows_sum, reference_allows_var,
    reference_allows_stat, SumOrder, StatAlgo]

theorem Measure.allowedP_reference (m : Measure) (rows : Relation) (v : Value) :
    m.AllowedP Profile.reference.table Impl.lean rows v ↔ m.Allowed rows v := by
  simp only [Measure.AllowedP, Measure.Allowed, Measure.inputsI_lean, AggFn.allowedP_reference]

theorem forall₂_iff {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b ↔ S a b) {l : List α}
    {l' : List β} : Forall2 R l l' ↔ Forall2 S l l' :=
  ⟨Forall2.imp fun a b => (h a b).mp, Forall2.imp fun a b => (h a b).mpr⟩

theorem aggAllowedP_reference (gs : List Expr) (ms : List Measure) (rows out : Relation) :
    aggAllowedP Profile.reference.table Impl.lean gs ms rows out ↔ aggAllowed gs ms rows out := by
  unfold aggAllowedP aggAllowed
  split
  · exact exists_congr fun vs => and_congr_right fun _ =>
      forall₂_iff fun m v => Measure.allowedP_reference m rows v
  · exact forall₂_iff fun k row => exists_congr fun vs => and_congr_right fun _ =>
      forall₂_iff fun m v => Measure.allowedP_reference m _ v

theorem NullOk.reference (k : SortKey) (nf : Bool) :
    NullOk Profile.reference.table k nf ↔ nf = k.firstNulls := by
  unfold NullOk SortKey.nullPrefs SortKey.firstNulls
  cases k.nullsOpen <;> cases k.nullsFirst <;> cases nf <;> decide

theorem zip_map_self {α β : Type} (f : α → β) : ∀ l : List α, l.zip (l.map f) = l.map fun a => (a, f a)
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.zip_cons_cons, zip_map_self f l]

theorem SortedP.reference (keys : List SortKey) (out : Relation) :
    SortedP Profile.reference.table keys out ↔ SortAllowed keys out := by
  constructor
  · rintro ⟨cmp, hc, nfs, hn, _, hs⟩
    have : nfs = keys.map (·.firstNulls) :=
      eq_map_of_forall₂ (Forall2.imp (fun k nf h => (NullOk.reference k nf).mp h) hn)
    subst this
    rw [zip_map_self] at hs
    exact ⟨cmp, hc, hs⟩
  · rintro ⟨cmp, hc, hs⟩
    refine ⟨cmp, hc, keys.map (·.firstNulls),
      forall₂_map_self keys fun k _ => (NullOk.reference k _).mpr rfl,
      fun _ _ _ => by rw [reference_allows_clustered]; exact List.mem_singleton_self _, ?_⟩
    rw [zip_map_self]; exact hs

/-- Under the reference's table and Lean's functions, `AllowedI` is `Rel.Allowed`. -/
theorem Rel.allowedI_reference (cat : Catalog) :
    ∀ (r : Rel) (out : Relation), r.AllowedI Profile.reference.table Impl.lean cat out ↔ r.Allowed cat out
  | .read _, _ | .values _ _, _ => Iff.rfl
  | .filter r c, out => by
    simp only [Rel.AllowedI, Rel.Allowed, Expr.evalI_lean, Rel.allowedI_reference cat r]
  | .project r es, out => by
    simp only [Rel.AllowedI, Rel.Allowed, Expr.evalI_lean, Rel.allowedI_reference cat r]
  | .emit r _, out => by simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat r]
  | .cross a b, out => by
    simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat a, Rel.allowedI_reference cat b]
  | .join a b .inner on, out => by
    simp only [Rel.AllowedI, Rel.Allowed, Expr.evalI_lean, Rel.allowedI_reference cat a,
      Rel.allowedI_reference cat b]
  | .join a b .left on, out => by
    simp only [Rel.AllowedI, Rel.Allowed, leftJoinRowI_lean, Rel.allowedI_reference cat a,
      Rel.allowedI_reference cat b]
  | .fetch r _ _, _ => exists_congr fun i => and_congr_left' (Rel.allowedI_reference cat r i)
  | .unionAll a b, out => by
    simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat a, Rel.allowedI_reference cat b]
  | .window r _ _ _, out => by simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat r]
  | .semi a b _ _, out => by
    simp only [Rel.AllowedI, Rel.Allowed, hasMatchI_lean, Rel.allowedI_reference cat a,
      Rel.allowedI_reference cat b]
  | .orderBy r keys, out => by
    simp only [Rel.AllowedI, Rel.Allowed, SortedP.reference, Rel.allowedI_reference cat r]
  | .distinct r, out => by simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat r]
  | .aggregate r gs ms, out => by
    simp only [Rel.AllowedI, Rel.Allowed, aggAllowedP_reference, Rel.allowedI_reference cat r]
  | .unnest r _, out => by simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat r]

theorem CallExtra.not_reference (c : Functions.Ctor) : ¬CallExtra Profile.reference.table c :=
  fun ⟨_, _, _, _, _, _, _, _, hb, hn⟩ => hn hb

theorem Impl.within_reference {I : Impl} : I.Within Profile.reference.table ↔ I = Impl.lean := by
  constructor
  · rintro ⟨hu, hb⟩
    have hu' : I.un = UnFn.apply := funext fun f => funext fun v =>
      (hu f v).resolve_right (CallExtra.not_reference _)
    have hb' : I.bin = BinFn.apply := funext fun f => funext fun v => funext fun w =>
      (hb f v w).resolve_right (CallExtra.not_reference _)
    cases I; simp only at hu' hb'; subst hu' hb'; rfl
  · rintro rfl; exact ⟨fun _ _ => .inl rfl, fun _ _ _ => .inl rfl⟩

/-- **The reference's table gives `Rel.Allowed`.** -/
theorem Rel.allowedP_reference {cat : Catalog} {r : Rel} {out : Relation} :
    r.AllowedP Profile.reference.table cat out ↔ r.Allowed cat out := by
  constructor
  · rintro ⟨I, hI, ho⟩
    rw [Impl.within_reference.mp hI] at ho
    exact (Rel.allowedI_reference cat r out).mp ho
  · intro h
    exact ⟨Impl.lean, Impl.within_reference.mpr rfl, (Rel.allowedI_reference cat r out).mpr h⟩

/-- **`Allowed_reference ⊆ Allowed_core`.** -/
theorem Rel.allowed_core {cat : Catalog} {r : Rel} {out : Relation} (h : r.Allowed cat out) :
    r.AllowedP Profile.core.table cat out :=
  Rel.AllowedP_mono Profile.reference_le_core (Rel.allowedP_reference.mpr h)

/-! ## Refinement between profiles -/

/-- **`(Q, q) ⊑ (P, r)`**: every result `Q` allows for `q`, `P` allows for `r`,
up to the order of rows. -/
def Rel.RefinesP (cat : Catalog) (Q P : ProfileTable) (q r : Rel) : Prop :=
  ∀ out, q.AllowedP Q cat out → ∃ out', r.AllowedP P cat out' ∧ out.Perm out'

theorem Rel.RefinesP.refl (cat : Catalog) (P : ProfileTable) (r : Rel) : r.RefinesP cat P P r :=
  fun out h => ⟨out, h, .refl _⟩

theorem Rel.RefinesP.trans {cat : Catalog} {P Q R : ProfileTable} {p q r : Rel}
    (h₁ : p.RefinesP cat R Q q) (h₂ : q.RefinesP cat Q P r) : p.RefinesP cat R P r :=
  fun out h => by
    obtain ⟨o₁, h₁', hp₁⟩ := h₁ out h
    obtain ⟨o₂, h₂', hp₂⟩ := h₂ o₁ h₁'
    exact ⟨o₂, h₂', hp₁.trans hp₂⟩

/-- A narrower profile, the same plan: `(t, r) ⊑ (u, r)`. -/
theorem Rel.RefinesP.of_le {cat : Catalog} {t u : ProfileTable} (h : t.Le u) (r : Rel) :
    r.RefinesP cat t u r :=
  fun out ho => ⟨out, Rel.AllowedP_mono h ho, .refl _⟩

/-- `Rel.Refines` is `⊑` under the reference. -/
theorem Rel.refines_iff_refinesP {cat : Catalog} {q r : Rel} :
    q.Refines cat r ↔ q.RefinesP cat Profile.reference.table Profile.reference.table r := by
  simp only [Rel.Refines, Rel.RefinesP, Rel.allowedP_reference]

end Substrait
