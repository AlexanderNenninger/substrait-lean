import Sverify.Core.Allowed
import Sverify.Core.Options
import Sverify.Core.Scopes

/-!
# What a profile allows (#444, step 1c)

`Rel.Allowed` is the reference's relation. `Rel.AllowedP t` is the same
relation with every choice point read from a profile's table `t`
(`core/Sverify/Core/Options.lean`):

* a call takes the reference's value, or, where `t` allows a behaviour of
  one of its group's options that the reference does not and the call is in
  that option's scope (`optionScope`, D34), a value of that behaviour
  (`Impl.Within`). The values of those behaviours are not modelled yet, so
  such a call may take any value there: an over-approximation that each
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
variable [Boxes.Ambient]

/-! ## The relational options' behaviours -/

/-- The doubles an engine's `SUM` of `vs` may give when it adds in an order
of its own: the values added one by one in any order, or two such sums of a
split of `vs` added together (a two-phase or a tree sum). The reference does
not (D25); `float-bounds` bounds this set's distance from it
(`epsilon_sum_cr`). -/
inductive FloatSums : List Value → Int → Prop
  | seq {vs ws : List Value} : ws.Perm vs → FloatSums vs (floatSum ws)
  | split {vs xs ys : List Value} {a b : Int} : vs.Perm (xs ++ ys) → FloatSums xs a →
      FloatSums ys b → FloatSums vs (FloatCode.fadd a b)

/-- `Σ |xᵢ|` over the doubles among `vs`, in units of `2⁻¹⁰⁷⁴`. -/
def scaledAbsSum : List Value → Nat
  | [] => 0
  | .float c :: vs => (FloatCode.scaled c).natAbs + scaledAbsSum vs
  | _ :: vs => scaledAbsSum vs

set_option exponentiation.threshold 2100 in
/-- **The bound every engine summation order meets (D35).** On `n ≤ 2³²`
finite doubles whose `2 · Σ(|xᵢ| + 2⁻¹⁰²²)` stays below the largest double,
a sum `c` is finite and within `(γₙ + u) · Σ(|xᵢ| + 2⁻¹⁰²²)` of the exact sum,
`u = 2⁻⁵³`, `γₙ = nu / (1 − nu)`: in units of `2⁻¹⁰⁷⁴` and multiplied out,
an exact inequality on integers. `float-bounds` proves it of every order the
engines' facts record (`StdModel.Summed.near`: trees, a sequential sum,
Kahan's, a constant run's `fl(k · x)`); that the engines' algorithms meet it
is trusted (docs/proofs.md, retired by #1196). -/
def SumBound (vs : List Value) (c : Int) : Prop :=
  (∀ x, Value.float x ∈ vs → FloatCode.IsFin x) → vs.length ≤ 2 ^ 32 →
    2 * (scaledAbsSum vs + vs.length * 2 ^ 52) ≤ FloatCode.maxMag →
    FloatCode.IsFin c ∧
      (FloatCode.scaled c - exactSum vs).natAbs * (2 ^ 53 * (2 ^ 53 - vs.length)) ≤
        (vs.length * 2 ^ 53 + (2 ^ 53 - vs.length)) * (scaledAbsSum vs + vs.length * 2 ^ 52)

/-- The doubles a `SUM` of `vs` gives under a `sum_order` behaviour: the
correctly rounded exact sum for `EXACT`, the reference's (D25); for every
other behaviour a sum within `SumBound` (D35) and, where the behaviour has
one, of its shape: a tree (`ANY`, `PAIRWISE`) or a sequential sum in some
order (`SEQUENTIAL`). Kahan's compensated sum (`COMPENSATED`) and a constant
run's product (`SCALED_CONSTANT`) are the bound alone. -/
def SumOrder (b : Behaviour) (vs : List Value) (c : Int) : Prop :=
  if b = "EXACT" then c = floatSumCR vs
  else SumBound vs c ∧
    if b = "ANY" ∨ b = "PAIRWISE" then FloatSums vs c
    else if b = "SEQUENTIAL" then ∃ ws, ws.Perm vs ∧ c = floatSum ws
    else True

/-- The doubles an `AVG` of `vs` gives under a `sum_order` behaviour: the
exact mean rounded once for `EXACT`, else a sum `SumOrder` allows divided by
the count. -/
def AvgOrder (b : Behaviour) (vs : List Value) (c : Int) : Prop :=
  if b = "EXACT" then c = floatAvgCR vs
  else ∃ s, SumOrder b vs s ∧ c = FloatCode.fdiv s (FloatCode.ofInt vs.length)

/-- What a statistical aggregate gives under a `stat_algo` behaviour: the
exact moments rounded once for `EXACT`, the reference's (D30). An engine's
own algorithm (`WELFORD_CHAN`) is not modelled here: it meets the generic
properties (`StatProps`), which is all this allows of it. -/
def StatAlgo (b : Behaviour) (f : AggFn) (vs : List Value) (v : Value) : Prop :=
  if b = "EXACT" then v = f.apply vs
  else if b = "GENERIC" ∨ b = "WELFORD_CHAN" then StatProps f vs v else True

/-- What `QUANTILE_CONT` gives under a `quantile_interp` behaviour: a double
between the neighbours, which DuckDB's linear interpolation is (clamped). -/
def QuantInterp (b : Behaviour) (num scale : Nat) (vs : List Value) (v : Value) : Prop :=
  if b = "BETWEEN" ∨ b = "LINEAR" then contAllowed num scale (sortVals vs) v else True

/-- The options `AggFn.AllowedP` interprets. -/
def aggInterpreted : List String := ["sum_order", "stat_algo", "quantile_interp"]

/-- Does `t` allow an aggregate of `vs` a behaviour the reference does not,
at an option `AggFn.AllowedP` does not interpret (`overflow`, `avg_int_result`,
`empty_group_aggregates`, …), with `vs` in that option's scope (D34)? Then it
may give any value, as a call may (`CallExtra`). -/
def AggExtra (t : ProfileTable) (f : AggFn) (vs : List Value) : Prop :=
  ∃ r, Functions.rowOf (.agg f) = some r ∧ ∃ os, Functions.groups.lookup r.group = some os ∧
    ∃ o ∈ os, o ∉ aggInterpreted ∧ (∃ b ∈ t.allows r.group o [],
      b ∉ Profile.reference.table.allows r.group o []) ∧ optionScope o (.agg f) vs = true

/-! ## Aggregates -/

/-- `AggFn.Allowed` with the choices of `t` at the options it interprets. -/
def AggFn.AllowedChoice (t : ProfileTable) (f : AggFn) (vs : List Value) (v : Value) : Prop :=
  match f with
  | .fsum => if vs = [] then v = .null else
      ∃ b ∈ t.allows "agg.fsum" "sum_order" [], ∃ c, SumOrder b vs c ∧ v = .float c
  | .avg => if vs = [] then v = .null else
      ∃ b ∈ t.allows "agg.fsum" "sum_order" [], ∃ c, AvgOrder b vs c ∧ v = .float c
  | .var _ _ => ∃ b ∈ t.allows "agg.var" "stat_algo" [], StatAlgo b f vs v
  | .cov _ | .corr => ∃ b ∈ t.allows "agg.stat" "stat_algo" [], StatAlgo b f vs v
  | .quantile true num scale => if vs = [] then v = .null else
      ∃ b ∈ t.allows "agg.quant" "quantile_interp" [], QuantInterp b num scale vs v
  | _ => f.Picks vs v

/-- `AggFn.Allowed` with the choices of `t`, or any value where `t` allows a
behaviour this does not model (`AggExtra`). -/
def AggFn.AllowedP (t : ProfileTable) (f : AggFn) (vs : List Value) (v : Value) : Prop :=
  f.AllowedChoice t vs v ∨ AggExtra t f vs

/-- `Measure.Allowed` with the choices of `t` and the functions of `I`. -/
def Measure.AllowedP (t : ProfileTable) (I : Impl) (m : Measure) (rows : Relation)
    (v : Value) : Prop :=
  ∃ s, s.Perm rows ∧ (m.fn.sorts = true → s.Pairwise (sortLe m.sort · · = true)) ∧
    m.fn.AllowedP t (m.inputs s I) v

/-- `aggAllowed` with the choices of `t` and the functions of `I`. -/
def aggAllowedP (t : ProfileTable) (I : Impl) (gs : List Expr) (ms : List Measure)
    (rows out : Relation) : Prop :=
  if gs.isEmpty then ∃ vs, out = [vs] ∧ Forall2 (fun m v => m.AllowedP t I rows v) ms vs
  else ∃ ks, IsReps Row.canon (rows.map fun row => groupKey gs row I) ks ∧
    Forall2 (fun k row => ∃ vs, row = k ++ vs ∧
      Forall2 (fun m v => m.AllowedP t I (groupRows gs rows k I) v) ms vs) ks out

/-! ## Windows -/

/-- Is `m` a double `SUM` or `AVG` over a frame that `t` lets the engine keep
as a sliding sum, adding the rows entering the frame and subtracting those
leaving it (`window_sum_algo = SLIDING`, #1032)? Such a sum is no sum of the
frame's values, and may give any value. -/
def SlidingSum (t : ProfileTable) (m : Measure) : Prop :=
  (m.fn = .fsum ∨ m.fn = .avg) ∧ "SLIDING" ∈ t.allows "win.agg" "window_sum_algo" []

/-- What a window function may give at `x`, from its partition's rows before
(`pb`) and after (`pa`) it, under `t`. An order-free aggregate over the frame
takes its measure's choice (`Measure.AllowedP`), as a grouped aggregate does:
a double `SUM` or `AVG` any sum `sum_order` allows. Every other window
function gives its value. The frame's rows come from the window's own
columns, so the measure reads them with Lean's functions, as
`WinFn.valueIn` does. -/
def WinFn.AllowedP (t : ProfileTable) (pb : List Row) (x : Row) (pa : List Row) (f : WinFn)
    (v : Value) : Prop :=
  match f with
  | .agg m sort fr =>
    -- A window's `MIN` and `MAX` keep `Measure.eval`'s member of a class.
    if m.orderFree then (m.AllowedP t Impl.lean (fr.rows sort pb x pa) v ∧
        (m.fn = .min ∨ m.fn = .max → v = m.eval (fr.rows sort pb x pa))) ∨ SlidingSum t m
    else v = m.eval (fr.rows sort pb x pa)
  | _ => v = f.valueIn pb x pa

/-- `windowRows` with each function's value one `WinFn.AllowedP` allows. -/
def windowRowsP (t : ProfileTable) (part : List Nat) (fns : List WinFn) :
    List Row → List Row → Relation → Prop
  | _, [], out => out = []
  | before, x :: after, out => ∃ vs rest, out = (x ++ vs) :: rest ∧
      Forall2 (fun f v => f.AllowedP t (before.filter (samePart part x)) x
        (after.filter (samePart part x)) v) fns vs ∧
      windowRowsP t part fns (before ++ [x]) after rest

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

/-- Does `t` allow a call of `c` on `args` a behaviour the reference does
not, at an option whose scope the call is in (D34)? Then the call may give
another value than the reference's. -/
def CallExtra (t : ProfileTable) (c : Functions.Ctor) (args : List Value) : Prop :=
  ∃ r, Functions.rowOf c = some r ∧ ∃ os, Functions.groups.lookup r.group = some os ∧
    ∃ o ∈ os, o ∉ aggInterpreted ∧ (∃ b ∈ t.allows r.group o [],
      b ∉ Profile.reference.table.allows r.group o []) ∧ optionScope o c args = true

/-- The functions `I` are ones `t` allows: each call gives the reference's
value, unless `t` allows it another behaviour in whose option's scope it is. -/
def Impl.Within (t : ProfileTable) (I : Impl) : Prop :=
  (∀ f v, I.un f v = f.apply v ∨ CallExtra t (.un f) [v]) ∧
    ∀ f v w, I.bin f v w = f.apply v w ∨ CallExtra t (.bin f) [v, w]

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
      s.Pairwise (sortLe sort · · = true) ∧ ∃ o, out.Perm o ∧ windowRowsP t part fns [] s o
  | .semi a b anti on, out => ∃ x y, a.AllowedI t I cat x ∧ b.AllowedI t I cat y ∧
      out.Perm (x.filter fun row => hasMatch on y row I != anti)
  | .orderBy r keys, out => ∃ i, r.AllowedI t I cat i ∧ out.Perm i ∧ SortedP t keys out
  | .distinct r, out => ∃ i, r.AllowedI t I cat i ∧ ∃ d, IsReps Row.canon i d ∧ out.Perm d
  | .aggregate r gs ms, out => ∃ i, r.AllowedI t I cat i ∧ ∃ o, out.Perm o ∧
      aggAllowedP t I gs ms i o
  | .unnest r c, out => ∃ i, r.AllowedI t I cat i ∧ out.Perm (i.flatMap (unnestRow c))

/-- **The results the profile `t` allows** for `r` on `cat`: those of some
functions `t` allows. -/
def Rel.AllowedP (t : ProfileTable) (cat : Catalog) (r : Rel) (out : Relation) : Prop :=
  ∃ I, I.Within t ∧ r.AllowedI t I cat out

/-! ## Monotonicity -/

section Mono
variable {t u : ProfileTable} (h : t.Le u)
include h

theorem AggExtra.mono {f : AggFn} {vs : List Value} : AggExtra t f vs → AggExtra u f vs :=
  fun ⟨r, hr, os, hos, o, ho, hi, ⟨b, hb, hn⟩, hs⟩ =>
    ⟨r, hr, os, hos, o, ho, hi, ⟨b, h _ _ _ _ hb, hn⟩, hs⟩

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
  · rintro ⟨ks, hks, hk⟩
    exact ⟨ks, hks, Forall2.imp (fun _ _ ⟨vs, hrow, hv⟩ =>
      ⟨vs, hrow, Forall2.imp (fun _ _ => Measure.AllowedP.mono h) hv⟩) hk⟩

theorem WinFn.AllowedP.mono {pb : List Row} {x : Row} {pa : List Row} {f : WinFn} {v : Value} :
    f.AllowedP t pb x pa v → f.AllowedP u pb x pa v := by
  cases f <;> simp only [WinFn.AllowedP] <;> try exact id
  split
  · exact Or.imp (fun ⟨ha, hm⟩ => ⟨Measure.AllowedP.mono h ha, hm⟩) fun ⟨hf, hb⟩ => ⟨hf, h _ _ _ _ hb⟩
  · exact id

theorem windowRowsP.mono {part : List Nat} {fns : List WinFn} :
    ∀ {before s : List Row} {out : Relation},
      windowRowsP t part fns before s out → windowRowsP u part fns before s out
  | _, [], _, ho => ho
  | _, _ :: _, _, ⟨vs, rest, he, hv, hr⟩ =>
    ⟨vs, rest, he, Forall2.imp (fun _ _ => WinFn.AllowedP.mono h) hv, windowRowsP.mono hr⟩

omit [Boxes.Ambient] in
theorem SortedP.mono {keys : List SortKey} {out : Relation} :
    SortedP t keys out → SortedP u keys out := fun ⟨cmp, hc, nfs, hn, hcl, hs⟩ =>
  ⟨cmp, hc, nfs, Forall2.imp (fun _ _ hk => h _ _ _ _ hk) hn,
    fun k hk hck => h _ _ _ _ (hcl k hk hck), hs⟩

theorem Impl.Within.mono {I : Impl} : I.Within t → I.Within u := by
  have hx : ∀ c args, CallExtra t c args → CallExtra u c args :=
    fun _ _ ⟨r, hr, os, hos, o, ho, hi, ⟨b, hb, hn⟩, hs⟩ =>
      ⟨r, hr, os, hos, o, ho, hi, ⟨b, h _ _ _ _ hb, hn⟩, hs⟩
  exact fun ⟨hu, hb⟩ => ⟨fun f v => (hu f v).imp_right (hx _ _),
    fun f v w => (hb f v w).imp_right (hx _ _)⟩

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
  | .window _ _ _ _, _, ⟨i, hi, s, hs, hsort, o, hp, ho⟩ =>
    ⟨i, Rel.AllowedI.mono hi, s, hs, hsort, o, hp, windowRowsP.mono h ho⟩
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

omit [Boxes.Ambient] in
/-- The reference's choices of the relational options. -/
theorem reference_allows_sum :
    Profile.reference.table.allows "agg.fsum" "sum_order" [] = ["EXACT"] := by
  decide +kernel
omit [Boxes.Ambient] in
theorem reference_allows_var :
    Profile.reference.table.allows "agg.var" "stat_algo" [] = ["EXACT"] := by decide +kernel
omit [Boxes.Ambient] in
theorem reference_allows_stat :
    Profile.reference.table.allows "agg.stat" "stat_algo" [] = ["EXACT"] := by decide +kernel
omit [Boxes.Ambient] in
theorem reference_allows_quant :
    Profile.reference.table.allows "agg.quant" "quantile_interp" [] = ["BETWEEN"] := by decide +kernel
omit [Boxes.Ambient] in
theorem reference_allows_window_sum :
    Profile.reference.table.allows "win.agg" "window_sum_algo" [] = ["RECOMPUTE"] := by
  decide +kernel
omit [Boxes.Ambient] in
theorem reference_allows_clustered :
    Profile.reference.table.allows "rel.sort" "clustered" [] = ["ADJACENT"] := by decide +kernel

theorem AggExtra.not_reference (f : AggFn) (vs : List Value) :
    ¬AggExtra Profile.reference.table f vs :=
  fun ⟨_, _, _, _, _, _, _, ⟨_, hb, hn⟩, _⟩ => hn hb

theorem AggFn.allowedP_reference (f : AggFn) (vs : List Value) (v : Value) :
    f.AllowedP Profile.reference.table vs v ↔ f.Allowed vs v := by
  rw [AggFn.AllowedP, or_iff_left (AggExtra.not_reference f vs)]
  cases f
  case quantile cont num scale =>
    cases cont <;> simp [AggFn.AllowedChoice, AggFn.Allowed, reference_allows_quant, QuantInterp]
  case fsum | avg =>
    cases vs with
    | nil => simp [AggFn.AllowedChoice, AggFn.Allowed, AggFn.apply, AggFn.Picks]
    | cons w ws =>
      simp [AggFn.AllowedChoice, AggFn.Allowed, AggFn.apply, reference_allows_sum, SumOrder,
        AvgOrder, AggFn.Picks]
  all_goals simp [AggFn.AllowedChoice, AggFn.Allowed, reference_allows_var,
    reference_allows_stat, StatAlgo, AggFn.Picks]

theorem Measure.allowedP_reference (m : Measure) (rows : Relation) (v : Value) :
    m.AllowedP Profile.reference.table Impl.lean rows v ↔ m.Allowed rows v := by
  simp only [Measure.AllowedP, Measure.Allowed, AggFn.allowedP_reference]

omit [Boxes.Ambient] in
theorem forall₂_iff {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b ↔ S a b) {l : List α}
    {l' : List β} : Forall2 R l l' ↔ Forall2 S l l' :=
  ⟨Forall2.imp fun a b => (h a b).mp, Forall2.imp fun a b => (h a b).mpr⟩

theorem aggAllowedP_reference (gs : List Expr) (ms : List Measure) (rows out : Relation) :
    aggAllowedP Profile.reference.table Impl.lean gs ms rows out ↔ aggAllowed gs ms rows out := by
  unfold aggAllowedP aggAllowed
  split
  · exact exists_congr fun vs => and_congr_right fun _ =>
      forall₂_iff fun m v => Measure.allowedP_reference m rows v
  · exact exists_congr fun ks => and_congr_right fun _ =>
      forall₂_iff fun k row => exists_congr fun vs => and_congr_right fun _ =>
        forall₂_iff fun m v => Measure.allowedP_reference m _ v

/-- An order-free measure allows only its value, when `MIN` and `MAX` keep
`Measure.eval`'s member of a class. -/
theorem Measure.allowed_iff {m : Measure} (hm : m.orderFree = true) (rows : Relation) (v : Value) :
    (m.Allowed rows v ∧ (m.fn = .min ∨ m.fn = .max → v = m.eval rows)) ↔ v = m.eval rows := by
  refine ⟨fun ⟨h, hmm⟩ => ?_, fun h => ⟨h ▸ ?_, fun _ => h⟩⟩
  · rcases Measure.allowed_picks hm h with hv | ⟨hf, -⟩
    · rw [hv, Measure.eval_eq (AggFn.ne_collect_of_orderFree hm)]
    · exact hmm hf
  -- As `Measure.eval_allowed`, through `AggFn.allowed_iff`: no measure's axioms.
  by_cases hs : m.fn.sorts = true
  · refine ⟨rows.mergeSort (sortLe m.sort), List.mergeSort_perm _ _, fun _ =>
      List.pairwise_mergeSort (sortLe_totalPre _).trans (sortLe_totalPre _).total rows, ?_⟩
    rw [Measure.eval_sorts hs]; exact (AggFn.allowed_iff hm _ _).mpr (AggFn.picks_apply _ _)
  · refine ⟨rows, .refl _, fun h => absurd h hs, ?_⟩
    rw [Measure.eval_eq (by simpa using hs)]
    exact (AggFn.allowed_iff hm _ _).mpr (AggFn.picks_apply _ _)

theorem WinFn.allowedP_reference (pb : List Row) (x : Row) (pa : List Row) (f : WinFn)
    (v : Value) : f.AllowedP Profile.reference.table pb x pa v ↔ v = f.valueIn pb x pa := by
  have hs : ∀ m, ¬ SlidingSum Profile.reference.table m := fun _ ⟨_, h⟩ => by
    rw [reference_allows_window_sum] at h; simp at h
  cases f <;> simp only [WinFn.AllowedP, WinFn.valueIn]
  split
  · next hm => rw [or_iff_left (hs _), Measure.allowedP_reference, Measure.allowed_iff hm]
  · exact Iff.rfl

theorem windowRowsP_reference (part : List Nat) (fns : List WinFn) :
    ∀ (before s : List Row) (out : Relation),
      windowRowsP Profile.reference.table part fns before s out ↔
        out = windowRows part fns before s
  | _, [], _ => Iff.rfl
  | before, x :: after, out => by
    simp only [windowRowsP, windowRows]
    have hv : ∀ vs, Forall2 (fun f v => f.AllowedP Profile.reference.table
        (before.filter (samePart part x)) x (after.filter (samePart part x)) v) fns vs ↔
        vs = fns.map (·.value part before after x) := fun vs =>
      (forall₂_iff fun f v => WinFn.allowedP_reference _ _ _ f v).trans
        ⟨eq_map_of_forall₂, fun h => h ▸ forall₂_map_self fns fun _ _ => rfl⟩
    constructor
    · rintro ⟨vs, rest, rfl, h1, h2⟩
      rw [(hv vs).mp h1, (windowRowsP_reference part fns _ after rest).mp h2]
    · rintro rfl
      exact ⟨_, _, rfl, (hv _).mpr rfl, (windowRowsP_reference part fns _ after _).mpr rfl⟩

omit [Boxes.Ambient] in
theorem NullOk.reference (k : SortKey) (nf : Bool) :
    NullOk Profile.reference.table k nf ↔ nf = k.firstNulls := by
  unfold NullOk SortKey.nullPrefs SortKey.firstNulls
  cases k.nullsOpen <;> cases k.nullsFirst <;> cases nf <;> decide

omit [Boxes.Ambient] in
theorem zip_map_self {α β : Type} (f : α → β) : ∀ l : List α, l.zip (l.map f) = l.map fun a => (a, f a)
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.zip_cons_cons, zip_map_self f l]

omit [Boxes.Ambient] in
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
    simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat r]
  | .project r es, out => by
    simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat r]
  | .emit r _, out => by simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat r]
  | .cross a b, out => by
    simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat a, Rel.allowedI_reference cat b]
  | .join a b .inner on, out => by
    simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat a,
      Rel.allowedI_reference cat b]
  | .join a b .left on, out => by
    simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat a,
      Rel.allowedI_reference cat b]
  | .fetch r _ _, _ => exists_congr fun i => and_congr_left' (Rel.allowedI_reference cat r i)
  | .unionAll a b, out => by
    simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat a, Rel.allowedI_reference cat b]
  | .window r part _ fns, out => by
    simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat r,
      windowRowsP_reference part fns, exists_eq_right]
  | .semi a b _ _, out => by
    simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat a,
      Rel.allowedI_reference cat b]
  | .orderBy r keys, out => by
    simp only [Rel.AllowedI, Rel.Allowed, SortedP.reference, Rel.allowedI_reference cat r]
  | .distinct r, out => by simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat r]
  | .aggregate r gs ms, out => by
    simp only [Rel.AllowedI, Rel.Allowed, aggAllowedP_reference, Rel.allowedI_reference cat r]
  | .unnest r _, out => by simp only [Rel.AllowedI, Rel.Allowed, Rel.allowedI_reference cat r]

theorem CallExtra.not_reference (c : Functions.Ctor) (args : List Value) :
    ¬CallExtra Profile.reference.table c args :=
  fun ⟨_, _, _, _, _, _, _, ⟨_, hb, hn⟩, _⟩ => hn hb

theorem Impl.within_reference {I : Impl} : I.Within Profile.reference.table ↔ I = Impl.lean := by
  constructor
  · rintro ⟨hu, hb⟩
    have hu' : I.un = UnFn.apply := funext fun f => funext fun v =>
      (hu f v).resolve_right (CallExtra.not_reference _ _)
    have hb' : I.bin = BinFn.apply := funext fun f => funext fun v => funext fun w =>
      (hb f v w).resolve_right (CallExtra.not_reference _ _)
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

/-- **`(Q, q) ⊑ (P, r)` up to `o`**: every result `Q` allows for `q` is, up
to the observation `o`, one `P` allows for `r`. -/
def Rel.RefinesPUpTo (o : Obs) (ctx : ObsCtx) (cat : Catalog) (Q P : ProfileTable) (q r : Rel) :
    Prop :=
  ∀ out, q.AllowedP Q cat out → ∃ out', r.AllowedP P cat out' ∧ Relation.Equiv o ctx out out'

/-- **`(Q, q) ⊑ (P, r)`**: every result `Q` allows for `q`, `P` allows for `r`,
up to the order of rows. -/
abbrev Rel.RefinesP (cat : Catalog) (Q P : ProfileTable) (q r : Rel) : Prop :=
  Rel.RefinesPUpTo { rows := .multiset } {} cat Q P q r

theorem Rel.RefinesPUpTo.refl {o : Obs} {ctx : ObsCtx} (hc : ctx.WF) (cat : Catalog)
    (P : ProfileTable) (r : Rel) : r.RefinesPUpTo o ctx cat P P r :=
  fun out h => ⟨out, h, .refl hc out⟩

theorem Rel.RefinesPUpTo.trans {o : Obs} {c₁ c₂ c₃ : ObsCtx} (hc : ObsCtx.Comp c₁ c₂ c₃)
    {cat : Catalog} {P Q R : ProfileTable} {p q r : Rel} (h₁ : p.RefinesPUpTo o c₁ cat R Q q)
    (h₂ : q.RefinesPUpTo o c₂ cat Q P r) : p.RefinesPUpTo o c₃ cat R P r :=
  fun out h => by
    obtain ⟨o₁, h₁', e₁⟩ := h₁ out h
    obtain ⟨o₂, h₂', e₂⟩ := h₂ o₁ h₁'
    exact ⟨o₂, h₂', e₁.trans hc e₂⟩

theorem Rel.RefinesP.refl (cat : Catalog) (P : ProfileTable) (r : Rel) : r.RefinesP cat P P r :=
  Rel.RefinesPUpTo.refl .default cat P r

theorem Rel.RefinesP.trans {cat : Catalog} {P Q R : ProfileTable} {p q r : Rel}
    (h₁ : p.RefinesP cat R Q q) (h₂ : q.RefinesP cat Q P r) : p.RefinesP cat R P r :=
  Rel.RefinesPUpTo.trans (.self .default fun _ _ _ _ _ e₁ e₂ => e₁.trans e₂) h₁ h₂

end Substrait
