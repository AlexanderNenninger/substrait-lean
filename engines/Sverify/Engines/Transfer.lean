import Lean.Data.Json
import Sverify.Engines.Tables

/-!
# The options a plan meets, and the option-wise transfer check (#444, step 3c)

`Rel.AllowedP t` reads `t` only at the options the plan meets
(`Rel.reads`), each with the preferences it reads it for: its calls' groups'
options and its aggregates' (with none: the parser has resolved the plan's
own), and an `ORDER BY`'s `null_order` (with the key's placement) and
`clustered` (where a key is). So a result one profile allows
for a plan, another allows too when, at each of those options, its choices
are within the first's (`Rel.AllowedP_transfer`). Whatever is proved of every
result one profile allows then holds of every result the other allows: the
option-wise transfer check of `docs/core-semantics.md` ("Which plans run on
an engine"), decided by `transferB` for the plan at hand.

`Rel.reads` is the options a plan meets. The proof of a plan under the
reference uses at most these: an upper bound on step 3c's option dependency
report, which `verify` can narrow by checking the plan again with each of
them left open. -/

namespace Substrait

open Functions (Ctor rowOf groups)

/-! ## What a plan meets -/

/-- The calls of an expression, by constructor. -/
def Expr.ctors : Expr → List Ctor
  | .lit _ | .field _ => []
  | .un f a => .un f :: a.ctors
  | .bin f a b => .bin f :: (a.ctors ++ b.ctors)
  | .ifThen c t e => c.ctors ++ t.ctors ++ e.ctors
  | .hof _ l b => l.ctors ++ b.ctors

/-- A read of a profile's table: a group, an option and the plan's preferences. -/
abbrev Read := String × String × List Behaviour

/-- The options of a call's group that apply to it (`optionApplies`), with
the group: a `SUM` does not read `avg_int_result`. -/
def ctorReads (c : Ctor) : List Read :=
  match rowOf c with
  | some r => (((groups.lookup r.group).getD []).filter (optionApplies · c)).map (r.group, ·, [])
  | none => []

-- A `SUM` of integers reads its group's `overflow` and
-- `empty_group_aggregates`, and only an integer `AVG` reads `avg_int_result`.
#guard (ctorReads (.agg .sum)).map (·.2.1) == ["overflow", "empty_group_aggregates"]
#guard (ctorReads (.agg .iavg)).any (·.2.1 == "avg_int_result")

def Expr.reads (e : Expr) : List Read := e.ctors.flatMap ctorReads

/-- The options an aggregate meets: its group's, and those `AggFn.AllowedChoice` reads. -/
def AggFn.reads (f : AggFn) : List Read :=
  ctorReads (.agg f) ++ match f with
    | .fsum | .avg => [("agg.fsum", "sum_order", [])]
    | .var _ _ => [("agg.var", "stat_algo", [])]
    | .cov _ | .corr => [("agg.stat", "stat_algo", [])]
    | .quantile true _ _ => [("agg.quant", "quantile_interp", [])]
    | _ => []

def Measure.ctors (m : Measure) : List Ctor := m.arg.ctors ++ (m.filter.map Expr.ctors).getD []

def Measure.reads (m : Measure) : List Read :=
  m.arg.reads ++ (m.filter.map Expr.reads).getD [] ++ m.fn.reads

/-- An `ORDER BY`'s options: each key's NULL placement, and clustering where a key asks for it. -/
def sortReads (keys : List SortKey) : List Read :=
  keys.map (fun k => ("rel.sort", "null_order", k.nullPrefs)) ++
    if keys.any (·.clustered) then [("rel.sort", "clustered", [])] else []

/-- Rows compared as keys (grouping, `DISTINCT`, a join's equality): NaN and the zeros. -/
def keyReads : List Read := [("rel.keys", "nan_equality", []), ("rel.keys", "zero_sign", [])]

/-- A join's: its keys, and whether NULL keys match. -/
def joinReads : List Read := keyReads ++ [("rel.join", "null_join_keys", [])]

/-- A window function's options: its aggregate's, as a grouped aggregate meets them. -/
def WinFn.reads : WinFn → List Read
  | .agg m _ _ => m.reads ++
    if m.fn = .fsum ∨ m.fn = .avg then [("win.agg", "window_sum_algo", [])] else []
  | _ => []

/-- A window's own options: its functions', its sort keys' and, where it
partitions, the keys' comparison. -/
def windowReads (part : List Nat) (sort : List SortKey) (fns : List WinFn) : List Read :=
  fns.flatMap WinFn.reads ++ sortReads sort ++ if part.isEmpty then [] else keyReads

/-- The calls of a plan's expressions. -/
def Rel.ctors : Rel → List Ctor
  | .read _ | .values _ _ => []
  | .filter r c => r.ctors ++ c.ctors
  | .project r es => r.ctors ++ es.flatMap Expr.ctors
  | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _ | .distinct r | .unnest r _ => r.ctors
  | .cross a b | .unionAll a b => a.ctors ++ b.ctors
  | .join a b _ on | .semi a b _ on => a.ctors ++ b.ctors ++ on.ctors
  | .aggregate r gs ms => r.ctors ++ gs.flatMap Expr.ctors ++ ms.flatMap Measure.ctors

/-- **The options a plan meets**, by group. -/
def Rel.reads : Rel → List Read
  | .read _ | .values _ _ => []
  | .filter r c => r.reads ++ c.reads
  | .project r es => r.reads ++ es.flatMap Expr.reads
  | .emit r _ | .fetch r _ _ | .unnest r _ => r.reads
  | .window r part sort fns => r.reads ++ windowReads part sort fns
  | .distinct r => r.reads ++ keyReads
  | .orderBy r keys => r.reads ++ sortReads keys
  | .cross a b | .unionAll a b => a.reads ++ b.reads
  | .join a b _ on | .semi a b _ on => a.reads ++ b.reads ++ on.reads ++ joinReads
  | .aggregate r gs ms => r.reads ++ gs.flatMap Expr.reads ++ ms.flatMap Measure.reads ++
      if gs.isEmpty then [] else keyReads

theorem Expr.ctorReads_sub {e : Expr} {c : Ctor} (hc : c ∈ e.ctors) : ∀ p ∈ ctorReads c, p ∈ e.reads :=
  fun _ hp => List.mem_flatMap.mpr ⟨c, hc, hp⟩

theorem Rel.ctorReads_sub : ∀ {r : Rel} {c : Ctor}, c ∈ r.ctors → ∀ p ∈ ctorReads c, p ∈ r.reads
  | .read _, _, h, _, _ | .values _ _, _, h, _, _ => by simp [Rel.ctors] at h
  | .filter r e, c, h, p, hp => by
    simp only [Rel.ctors, List.mem_append] at h
    simp only [Rel.reads, List.mem_append]
    rcases h with h | h
    · exact .inl (Rel.ctorReads_sub h p hp)
    · exact .inr (Expr.ctorReads_sub h p hp)
  | .project r es, c, h, p, hp => by
    simp only [Rel.ctors, List.mem_append, List.mem_flatMap] at h
    simp only [Rel.reads, List.mem_append, List.mem_flatMap]
    rcases h with h | ⟨e, he, h⟩
    · exact .inl (Rel.ctorReads_sub h p hp)
    · exact .inr ⟨e, he, Expr.ctorReads_sub h p hp⟩
  | .emit r _, c, h, p, hp | .fetch r _ _, c, h, p, hp
  | .unnest r _, c, h, p, hp => by
    simp only [Rel.ctors] at h; simp only [Rel.reads]; exact Rel.ctorReads_sub h p hp
  | .window r _ _ _, c, h, p, hp => by
    simp only [Rel.ctors] at h; simp only [Rel.reads, List.mem_append]
    exact .inl (Rel.ctorReads_sub h p hp)
  | .distinct r, c, h, p, hp => by
    simp only [Rel.ctors] at h; simp only [Rel.reads, List.mem_append]
    exact .inl (Rel.ctorReads_sub h p hp)
  | .orderBy r _, c, h, p, hp => by
    simp only [Rel.ctors] at h; simp only [Rel.reads, List.mem_append]
    exact .inl (Rel.ctorReads_sub h p hp)
  | .cross a b, c, h, p, hp | .unionAll a b, c, h, p, hp => by
    simp only [Rel.ctors, List.mem_append] at h
    simp only [Rel.reads, List.mem_append]
    rcases h with h | h
    · exact .inl (Rel.ctorReads_sub h p hp)
    · exact .inr (Rel.ctorReads_sub h p hp)
  | .join a b _ on, c, h, p, hp | .semi a b _ on, c, h, p, hp => by
    simp only [Rel.ctors, List.mem_append] at h
    simp only [Rel.reads, List.mem_append]
    rcases h with (h | h) | h
    · exact .inl (.inl (.inl (Rel.ctorReads_sub h p hp)))
    · exact .inl (.inl (.inr (Rel.ctorReads_sub h p hp)))
    · exact .inl (.inr (Expr.ctorReads_sub h p hp))
  | .aggregate r gs ms, c, h, p, hp => by
    simp only [Rel.ctors, List.mem_append, List.mem_flatMap] at h
    simp only [Rel.reads, List.mem_append, List.mem_flatMap]
    rcases h with (h | ⟨e, he, h⟩) | ⟨m, hm, h⟩
    · exact .inl (.inl (.inl (Rel.ctorReads_sub h p hp)))
    · exact .inl (.inl (.inr ⟨e, he, Expr.ctorReads_sub h p hp⟩))
    · refine .inl (.inr ⟨m, hm, ?_⟩)
      simp only [Measure.ctors, List.mem_append] at h
      simp only [Measure.reads, List.mem_append]
      rcases h with h | h
      · exact .inl (.inl (Expr.ctorReads_sub h p hp))
      · refine .inl (.inr ?_)
        cases hf : m.filter with
        | none => simp [hf] at h
        | some e => simp only [hf, Option.map_some, Option.getD_some] at h ⊢
                    exact Expr.ctorReads_sub h p hp

/-! ## Functions that agree on a plan's calls -/

/-- `I` and `J` agree on the calls `cs`. -/
def Impl.AgreeOn (cs : List Ctor) (I J : Impl) : Prop :=
  (∀ f, .un f ∈ cs → ∀ v, I.un f v = J.un f v) ∧
    ∀ f, .bin f ∈ cs → ∀ v w, I.bin f v w = J.bin f v w

theorem Impl.AgreeOn.sub {cs ds : List Ctor} {I J : Impl} (h : Impl.AgreeOn ds I J)
    (hs : ∀ c ∈ cs, c ∈ ds) : Impl.AgreeOn cs I J :=
  ⟨fun f hf => h.1 f (hs _ hf), fun f hf => h.2 f (hs _ hf)⟩

variable [Boxes.Ambient]
theorem Expr.evalI_congr {I J : Impl} : ∀ {e : Expr}, Impl.AgreeOn e.ctors I J →
    ∀ row, e.eval row I = e.eval row J
  | .lit _, _, _ | .field _, _, _ => rfl
  | .un f a, h, row => by
    simp only [Expr.eval]
    rw [Expr.evalI_congr (h.sub fun c hc => List.mem_cons_of_mem _ hc) row]
    exact h.1 f (List.mem_cons_self ..) _
  | .bin f a b, h, row => by
    simp only [Expr.eval]
    rw [Expr.evalI_congr (h.sub fun c hc => List.mem_cons_of_mem _ (List.mem_append_left _ hc)) row,
      Expr.evalI_congr (h.sub fun c hc => List.mem_cons_of_mem _ (List.mem_append_right _ hc)) row]
    exact h.2 f (List.mem_cons_self ..) _ _
  | .ifThen c t e, h, row => by
    simp only [Expr.eval]
    rw [Expr.evalI_congr (h.sub fun _ hc => by simp [Expr.ctors, hc]) row,
      Expr.evalI_congr (h.sub fun _ hc => by simp [Expr.ctors, hc]) row,
      Expr.evalI_congr (h.sub fun _ hc => by simp [Expr.ctors, hc]) row]
  | .hof f l b, h, row => by
    simp only [Expr.eval]
    rw [Expr.evalI_congr (h.sub fun _ hc => by simp [Expr.ctors, hc]) row]
    congr 1; funext x
    exact Expr.evalI_congr (h.sub fun _ hc => by simp [Expr.ctors, hc]) (x :: row)

theorem evalI_congr_list {I J : Impl} {es : List Expr}
    (h : Impl.AgreeOn (es.flatMap Expr.ctors) I J) (row : Row) :
    es.map (·.eval row I) = es.map (·.eval row J) :=
  List.map_congr_left fun e he =>
    Expr.evalI_congr (h.sub fun _ hc => List.mem_flatMap.mpr ⟨e, he, hc⟩) row

theorem Measure.inputsI_congr {I J : Impl} {m : Measure} (h : Impl.AgreeOn m.ctors I J)
    (rows : Relation) : m.inputs rows I = m.inputs rows J := by
  have ha := Expr.evalI_congr (h.sub fun _ hc => List.mem_append_left _ hc)
  have hk : m.kept rows I = m.kept rows J := by
    unfold Measure.kept
    cases hf : m.filter with
    | none => rfl
    | some c =>
      have hc := Expr.evalI_congr (e := c) (h.sub fun _ hc =>
        List.mem_append_right _ (by simp [hf, hc]))
      simp only [hc]
  unfold Measure.inputs
  simp only [hk, ha]

theorem Measure.allowedP_congr {t : ProfileTable} {I J : Impl} {m : Measure}
    (h : Impl.AgreeOn m.ctors I J) : m.AllowedP t I = m.AllowedP t J := by
  funext rows v; simp only [Measure.AllowedP, Measure.inputsI_congr h]

theorem forall₂_congr_mem {α β : Type} {R S : α → β → Prop} {l : List α} {l' : List β}
    (h : ∀ a ∈ l, ∀ b, R a b ↔ S a b) : Forall2 R l l' ↔ Forall2 S l l' :=
  ⟨Forall2.imp_mem fun a ha b => (h a ha b).mp, Forall2.imp_mem fun a ha b => (h a ha b).mpr⟩

theorem aggAllowedP_congr {t : ProfileTable} {I J : Impl} {gs : List Expr} {ms : List Measure}
    (hg : Impl.AgreeOn (gs.flatMap Expr.ctors) I J) (hm : Impl.AgreeOn (ms.flatMap Measure.ctors) I J)
    (rows out : Relation) : aggAllowedP t I gs ms rows out ↔ aggAllowedP t J gs ms rows out := by
  have hk : ∀ row, groupKey gs row I = groupKey gs row J := fun row => evalI_congr_list hg row
  have hr : ∀ rows k, groupRows gs rows k I = groupRows gs rows k J := by
    intro rows k; simp only [groupRows, hk]
  have hms : ∀ m ∈ ms, m.AllowedP t I = m.AllowedP t J := fun m hmem =>
    Measure.allowedP_congr (hm.sub fun _ hc => List.mem_flatMap.mpr ⟨m, hmem, hc⟩)
  unfold aggAllowedP
  simp only [hk, hr]
  split
  · exact exists_congr fun vs => and_congr_right fun _ =>
      forall₂_congr_mem fun m hmem v => by rw [hms m hmem]
  · exact exists_congr fun _ => and_congr_right fun _ =>
      forall₂_congr_mem fun k _ row => exists_congr fun vs => and_congr_right fun _ =>
        forall₂_congr_mem fun m hmem v => by rw [hms m hmem]

/-- **`AllowedI` reads the functions only at the plan's calls.** -/
theorem Rel.allowedI_congr {t : ProfileTable} {I J : Impl} {cat : Catalog} :
    ∀ {r : Rel}, Impl.AgreeOn r.ctors I J → ∀ out, r.AllowedI t I cat out ↔ r.AllowedI t J cat out
  | .read _, _, _ | .values _ _, _, _ => Iff.rfl
  | .filter r c, h, _ => by
    have ih := Rel.allowedI_congr (t := t) (cat := cat) (r := r) (h.sub fun _ hc => List.mem_append_left _ hc)
    have hc := Expr.evalI_congr (e := c) (h.sub fun _ hc => List.mem_append_right _ hc)
    simp only [Rel.AllowedI, ih, hc]
  | .project r es, h, _ => by
    have ih := Rel.allowedI_congr (t := t) (cat := cat) (r := r) (h.sub fun _ hc => List.mem_append_left _ hc)
    have he := evalI_congr_list (es := es) (h.sub fun _ hc => List.mem_append_right _ hc)
    simp only [Rel.AllowedI, ih, he]
  | .emit r _, h, _ | .distinct r, h, _ | .unnest r _, h, _ | .window r _ _ _, h, _ => by
    simp only [Rel.AllowedI, Rel.allowedI_congr (t := t) (cat := cat) (r := r) h]
  | .fetch r _ _, h, _ => exists_congr fun i => and_congr_left' (Rel.allowedI_congr (t := t) (cat := cat) (r := r) h i)
  | .orderBy r _, h, _ => by simp only [Rel.AllowedI, Rel.allowedI_congr (t := t) (cat := cat) (r := r) h]
  | .cross a b, h, _ | .unionAll a b, h, _ => by
    simp only [Rel.AllowedI,
      Rel.allowedI_congr (t := t) (cat := cat) (r := a) (h.sub fun _ hc => List.mem_append_left _ hc),
      Rel.allowedI_congr (t := t) (cat := cat) (r := b) (h.sub fun _ hc => List.mem_append_right _ hc)]
  | .join a b .inner on, h, _ => by
    have ho := Expr.evalI_congr (e := on) (h.sub fun _ hc => List.mem_append_right _ hc)
    simp only [Rel.AllowedI, ho,
      Rel.allowedI_congr (t := t) (cat := cat) (r := a) (h.sub fun _ hc => by simp [Rel.ctors, hc]),
      Rel.allowedI_congr (t := t) (cat := cat) (r := b) (h.sub fun _ hc => by simp [Rel.ctors, hc])]
  | .join a b .left on, h, _ => by
    have ho := Expr.evalI_congr (e := on) (h.sub fun _ hc => List.mem_append_right _ hc)
    have hl : ∀ n ys x, leftJoinRow on n ys x I = leftJoinRow on n ys x J := by
      intro n ys x; simp only [leftJoinRow, ho]
    simp only [Rel.AllowedI, hl,
      Rel.allowedI_congr (t := t) (cat := cat) (r := a) (h.sub fun _ hc => by simp [Rel.ctors, hc]),
      Rel.allowedI_congr (t := t) (cat := cat) (r := b) (h.sub fun _ hc => by simp [Rel.ctors, hc])]
  | .semi a b _ on, h, _ => by
    have ho := Expr.evalI_congr (e := on) (h.sub fun _ hc => List.mem_append_right _ hc)
    have hm : ∀ ys x, hasMatch on ys x I = hasMatch on ys x J := by
      intro ys x; simp only [hasMatch, ho]
    simp only [Rel.AllowedI, hm,
      Rel.allowedI_congr (t := t) (cat := cat) (r := a) (h.sub fun _ hc => by simp [Rel.ctors, hc]),
      Rel.allowedI_congr (t := t) (cat := cat) (r := b) (h.sub fun _ hc => by simp [Rel.ctors, hc])]
  | .aggregate r gs ms, h, _ => by
    simp only [Rel.AllowedI,
      Rel.allowedI_congr (t := t) (cat := cat) (r := r)
        (h.sub fun _ hc => List.mem_append_left _ (List.mem_append_left _ hc)),
      aggAllowedP_congr (t := t) (gs := gs) (ms := ms)
        (h.sub fun _ hc => List.mem_append_left _ (List.mem_append_right _ hc))
        (h.sub fun _ hc => List.mem_append_right _ hc)]

/-! ## Choices that agree on a plan's options -/

/-! ### An order on behaviours

At the options `AggFn.AllowedP` interprets, one behaviour may allow fewer
results than another: a sequential sum is a tree of additions in some order
(`SEQUENTIAL ⊑ ANY`), and Welford's update meets the generic properties
(`WELFORD_CHAN ⊑ GENERIC`). A profile that allows the smaller one transfers
to one that allows the larger. `COMPENSATED` and `SCALED_CONSTANT` are not
below `ANY` (#633), and at every other option the order is equality. -/

/-- The pairs `b ⊑ b'` at an option, each with its lemma below. -/
def orderPairs : List (String × Behaviour × Behaviour) :=
  [("sum_order", "SEQUENTIAL", "ANY"), ("sum_order", "PAIRWISE", "ANY"),
   ("stat_algo", "WELFORD_CHAN", "GENERIC"), ("quantile_interp", "LINEAR", "BETWEEN")]

/-- `b ⊑ b'` at the option `o`. -/
def behaviourLe (o b b' : String) : Bool := b == b' || orderPairs.contains (o, b, b')

omit [Boxes.Ambient] in
theorem behaviourLe_eq {o b b' : String} (ho : o ∉ aggInterpreted) (h : behaviourLe o b b' = true) :
    b = b' := by
  simp only [behaviourLe, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  rcases h with h | h
  · exact h
  · exfalso; apply ho
    simp only [orderPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    simp only [aggInterpreted, List.mem_cons, List.not_mem_nil, or_false]
    rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp

omit [Boxes.Ambient] in
theorem SumOrder.mono {b b' : Behaviour} (h : behaviourLe "sum_order" b b' = true) {vs : List Value}
    {c : Int} (hs : SumOrder b vs c) : SumOrder b' vs c := by
  simp only [behaviourLe, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, orderPairs,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with rfl | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact hs
  · simp only [SumOrder] at hs ⊢
    obtain ⟨hb, ws, hp, rfl⟩ := hs
    exact ⟨hb, .seq hp⟩
  · simpa [SumOrder] using hs
  all_goals simp at h

omit [Boxes.Ambient] in
theorem AvgOrder.mono {b b' : Behaviour} (h : behaviourLe "sum_order" b b' = true) {vs : List Value}
    {c : Int} (hs : AvgOrder b vs c) : AvgOrder b' vs c := by
  by_cases e : b = b'
  · exact e ▸ hs
  · have hne : b ≠ "EXACT" ∧ b' ≠ "EXACT" := by
      simp only [behaviourLe, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, orderPairs,
        List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with h | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h e
      all_goals simp_all
    simp only [AvgOrder, hne.1, hne.2, ↓reduceIte] at hs ⊢
    obtain ⟨s, hs, rfl⟩ := hs
    exact ⟨s, SumOrder.mono h hs, rfl⟩

theorem StatAlgo.mono {b b' : Behaviour} (h : behaviourLe "stat_algo" b b' = true) {f : AggFn}
    {vs : List Value} {v : Value} (hs : StatAlgo b f vs v) : StatAlgo b' f vs v := by
  simp only [behaviourLe, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, orderPairs,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with rfl | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, rfl, rfl⟩ | ⟨h, -⟩
  · exact hs
  all_goals first | simp at h | simpa [StatAlgo] using hs

omit [Boxes.Ambient] in
theorem QuantInterp.mono {b b' : Behaviour} (h : behaviourLe "quantile_interp" b b' = true)
    {num scale : Nat} {vs : List Value} {v : Value} (hs : QuantInterp b num scale vs v) :
    QuantInterp b' num scale vs v := by
  simp only [behaviourLe, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, orderPairs,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with rfl | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, rfl, rfl⟩
  · exact hs
  all_goals first | simp at h | simpa [QuantInterp] using hs

example : behaviourLe "sum_order" "SEQUENTIAL" "ANY" = true := by decide
example : behaviourLe "sum_order" "COMPENSATED" "ANY" = false := by decide
example : behaviourLe "sum_order" "SCALED_CONSTANT" "ANY" = false := by decide
example : behaviourLe "null_order" "NULLS_FIRST" "NULLS_LAST" = false := by decide

/-- `t` allows no more than `u` at the read `p`, up to the order: each
behaviour `t` allows is below one `u` allows. -/
def ProfileTable.LeAt (t u : ProfileTable) (p : Read) : Prop :=
  ∀ b, b ∈ t.allows p.1 p.2.1 p.2.2 → ∃ b' ∈ u.allows p.1 p.2.1 p.2.2, behaviourLe p.2.1 b b' = true

omit [Boxes.Ambient] in
/-- At an option `AllowedP` does not interpret, `LeAt` is inclusion. -/
theorem ProfileTable.LeAt.mem {t u : ProfileTable} {p : Read} (h : t.LeAt u p)
    (ho : p.2.1 ∉ aggInterpreted) {b : Behaviour} (hb : b ∈ t.allows p.1 p.2.1 p.2.2) :
    b ∈ u.allows p.1 p.2.1 p.2.2 := by
  obtain ⟨b', hb', hle⟩ := h b hb
  rwa [behaviourLe_eq ho hle]

section MonoOn
variable {t u : ProfileTable}

theorem AggFn.AllowedP.monoOn {f : AggFn} (h : ∀ p ∈ f.reads, t.LeAt u p) {vs : List Value}
    {v : Value} : f.AllowedP t vs v → f.AllowedP u vs v := by
  have hlit : ∀ {g o : String} {P : Behaviour → Prop}, (g, o, []) ∈ f.reads →
      (∀ b b', behaviourLe o b b' = true → P b → P b') →
      (∃ b ∈ t.allows g o [], P b) → ∃ b ∈ u.allows g o [], P b :=
    fun hp hP ⟨b, hb, rest⟩ =>
      let ⟨b', hb', hle⟩ := h _ hp b hb
      ⟨b', hb', hP b b' hle rest⟩
  rintro (hc | ⟨r, hr, os, hos, o, ho, hi, ⟨b, hb, hn⟩, hsc⟩)
  · left
    cases f
    case quantile cont num scale =>
      cases cont
      · exact hc
      · simp only [AggFn.AllowedChoice] at hc ⊢
        split at hc
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (by assumption))]; exact hc
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by assumption))]
          exact hlit (by simp [AggFn.reads]) (fun _ _ hle => QuantInterp.mono hle) hc
    case fsum =>
      simp only [AggFn.AllowedChoice] at hc ⊢
      split at hc
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by assumption))]; exact hc
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by assumption))]
        exact hlit (by simp [AggFn.reads])
          (fun _ _ hle ⟨c, hs, hv⟩ => ⟨c, SumOrder.mono hle hs, hv⟩) hc
    case avg =>
      simp only [AggFn.AllowedChoice] at hc ⊢
      split at hc
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by assumption))]; exact hc
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by assumption))]
        exact hlit (by simp [AggFn.reads])
          (fun _ _ hle ⟨c, hs, hv⟩ => ⟨c, AvgOrder.mono hle hs, hv⟩) hc
    case var | cov | corr =>
      exact hlit (by simp [AggFn.reads]) (fun _ _ hle => StatAlgo.mono hle) hc
    all_goals exact hc
  · right
    have hp : (r.group, o, []) ∈ f.reads := by
      simp only [AggFn.reads, ctorReads, hr, hos, Option.getD_some, List.mem_append, List.mem_map,
        List.mem_filter]
      exact .inl ⟨o, ⟨ho, optionApplies_of_scope hsc⟩, rfl⟩
    exact ⟨r, hr, os, hos, o, ho, hi, ⟨b, ProfileTable.LeAt.mem (h _ hp) hi hb, hn⟩, hsc⟩

theorem Measure.AllowedP.monoOn {I : Impl} {m : Measure} (h : ∀ p ∈ m.reads, t.LeAt u p)
    {rows : Relation} {v : Value} : m.AllowedP t I rows v → m.AllowedP u I rows v :=
  fun ⟨s, hs, hsort, hf⟩ => ⟨s, hs, hsort, AggFn.AllowedP.monoOn
    (fun p hp => h p (List.mem_append_right _ hp)) hf⟩

theorem aggAllowedP.monoOn {I : Impl} {gs : List Expr} {ms : List Measure}
    (h : ∀ p ∈ ms.flatMap Measure.reads, t.LeAt u p) {rows out : Relation} :
    aggAllowedP t I gs ms rows out → aggAllowedP u I gs ms rows out := by
  have hm : ∀ m ∈ ms, ∀ (rows : Relation) (v : Value), m.AllowedP t I rows v → m.AllowedP u I rows v :=
    fun m hmem _ _ => Measure.AllowedP.monoOn fun p hp => h p (List.mem_flatMap.mpr ⟨m, hmem, hp⟩)
  unfold aggAllowedP
  split
  · rintro ⟨vs, rfl, hv⟩
    exact ⟨vs, rfl, Forall2.imp_mem (fun m hmem v => hm m hmem rows v) hv⟩
  · exact fun ⟨ks, hks, h'⟩ => ⟨ks, hks, h'.imp fun _ _ ⟨vs, hrow, hv⟩ =>
      ⟨vs, hrow, Forall2.imp_mem (fun m hmem v => hm m hmem _ v) hv⟩⟩

theorem WinFn.AllowedP.monoOn {f : WinFn} (h : ∀ p ∈ f.reads, t.LeAt u p) {pb : List Row} {x : Row}
    {pa : List Row} {v : Value} : f.AllowedP t pb x pa v → f.AllowedP u pb x pa v := by
  cases f with
  | agg m sort fr =>
    simp only [WinFn.AllowedP]
    split
    · refine Or.imp (fun ⟨ha, hb⟩ => ⟨Measure.AllowedP.monoOn
        (fun p hp => h p (List.mem_append_left _ hp)) ha, hb⟩) fun ⟨hf, hb⟩ => ⟨hf, ?_⟩
      · have hp : ("win.agg", "window_sum_algo", ([] : List String)) ∈ (WinFn.agg m sort fr).reads := by
          simp only [WinFn.reads, List.mem_append]
          exact .inr (by simp only [hf, ↓reduceIte]; exact List.mem_singleton_self _)
        exact ProfileTable.LeAt.mem (h _ hp) (by simp [aggInterpreted]) hb
    · exact id
  | _ => simp only [WinFn.AllowedP]; exact id

theorem windowRowsP.monoOn {part : List Nat} {fns : List WinFn}
    (h : ∀ p ∈ fns.flatMap WinFn.reads, t.LeAt u p) :
    ∀ {before s : List Row} {out : Relation},
      windowRowsP t part fns before s out → windowRowsP u part fns before s out
  | _, [], _, ho => ho
  | _, _ :: _, _, ⟨vs, rest, he, hv, hr⟩ =>
    ⟨vs, rest, he, Forall2.imp_mem (fun f hf _ => WinFn.AllowedP.monoOn fun p hp =>
      h p (List.mem_flatMap.mpr ⟨f, hf, hp⟩)) hv, windowRowsP.monoOn h hr⟩

omit [Boxes.Ambient] in
theorem SortedP.monoOn {keys : List SortKey} (h : ∀ p ∈ sortReads keys, t.LeAt u p)
    {out : Relation} : SortedP t keys out → SortedP u keys out := fun ⟨cmp, hc, nfs, hn, hcl, hs⟩ =>
  ⟨cmp, hc, nfs,
    Forall2.imp_mem (fun k hk _ hn => ProfileTable.LeAt.mem (h ("rel.sort", "null_order", k.nullPrefs)
      (List.mem_append_left _ (List.mem_map.mpr ⟨k, hk, rfl⟩))) (by simp [aggInterpreted]) hn) hn,
    fun k hk hck => ProfileTable.LeAt.mem (h ("rel.sort", "clustered", [])
      (List.mem_append_right _ (by
        rw [ite_eq_left_of_eq_true _ _ (eq_true (List.any_eq_true.mpr ⟨k, hk, hck⟩))]
        exact List.mem_singleton_self _))) (by simp [aggInterpreted]) (hcl k hk hck), hs⟩

/-- **`AllowedI` reads the choices only at the plan's options.** -/
theorem Rel.AllowedI.monoOn {I : Impl} {cat : Catalog} :
    ∀ {r : Rel}, (∀ p ∈ r.reads, t.LeAt u p) → ∀ {out : Relation},
      r.AllowedI t I cat out → r.AllowedI u I cat out
  | .read _, _, _, ho | .values _ _, _, _, ho => ho
  | .filter r _, h, _, ⟨i, hi, ho⟩ | .project r _, h, _, ⟨i, hi, ho⟩ =>
    ⟨i, Rel.AllowedI.monoOn (fun p hp => h p (List.mem_append_left _ hp)) hi, ho⟩
  | .distinct r, h, _, ⟨i, hi, ho⟩ =>
    ⟨i, Rel.AllowedI.monoOn (fun p hp => h p (List.mem_append_left _ hp)) hi, ho⟩
  | .emit r _, h, _, ⟨i, hi, ho⟩ | .fetch r _ _, h, _, ⟨i, hi, ho⟩
  | .unnest r _, h, _, ⟨i, hi, ho⟩ =>
    ⟨i, Rel.AllowedI.monoOn (r := r) (fun p hp => h p (by simp only [Rel.reads]; exact hp)) hi, ho⟩
  | .window r _ _ _, h, _, ⟨i, hi, s, hs, hsort, o, hp, ho⟩ =>
    ⟨i, Rel.AllowedI.monoOn (fun p hp => h p (List.mem_append_left _ hp)) hi, s, hs, hsort, o, hp,
      windowRowsP.monoOn (fun p hp => h p (List.mem_append_right _
        (List.mem_append_left _ (List.mem_append_left _ hp)))) ho⟩
  | .orderBy r _, h, _, ⟨i, hi, hp, hs⟩ =>
    ⟨i, Rel.AllowedI.monoOn (fun p hp => h p (List.mem_append_left _ hp)) hi, hp,
      SortedP.monoOn (fun p hp => h p (List.mem_append_right _ hp)) hs⟩
  | .cross a b, h, _, ⟨x, y, hx, hy, ho⟩ | .unionAll a b, h, _, ⟨x, y, hx, hy, ho⟩ =>
    ⟨x, y, Rel.AllowedI.monoOn (fun p hp => h p (List.mem_append_left _ hp)) hx,
      Rel.AllowedI.monoOn (fun p hp => h p (List.mem_append_right _ hp)) hy, ho⟩
  | .join a b .inner _, h, _, ⟨x, y, hx, hy, ho⟩ | .join a b .left _, h, _, ⟨x, y, hx, hy, ho⟩
  | .semi a b _ _, h, _, ⟨x, y, hx, hy, ho⟩ =>
    ⟨x, y, Rel.AllowedI.monoOn (fun p hp => h p (by simp [Rel.reads, hp])) hx,
      Rel.AllowedI.monoOn (fun p hp => h p (by simp [Rel.reads, hp])) hy, ho⟩
  | .aggregate r _ _, h, _, ⟨i, hi, o, hp, ha⟩ =>
    ⟨i, Rel.AllowedI.monoOn (fun p hp => h p (by simp [Rel.reads, hp])) hi, o, hp,
      aggAllowedP.monoOn (fun p hp => h p (by simp [Rel.reads, hp])) ha⟩

end MonoOn

/-! ## The transfer -/

open Classical in
/-- `I` at the plan's calls, Lean's own functions elsewhere. -/
noncomputable def Impl.restrict (cs : List Ctor) (I : Impl) : Impl where
  un f v := if Ctor.un f ∈ cs then I.un f v else f.apply v
  bin f v w := if Ctor.bin f ∈ cs then I.bin f v w else f.apply v w

/-- **The option-wise transfer**: a result `t` allows for `r`, `u` allows
too, when `u`'s choices are within `t`'s at every option `r` meets. -/
theorem Rel.AllowedP_transfer {t u : ProfileTable} {cat : Catalog} {r : Rel}
    (h : ∀ p ∈ r.reads, t.LeAt u p) {out : Relation} :
    r.AllowedP t cat out → r.AllowedP u cat out := by
  rintro ⟨I, ⟨hun, hbin⟩, ho⟩
  classical
  let J := Impl.restrict r.ctors I
  have hag : Impl.AgreeOn r.ctors I J :=
    ⟨fun f hf v => by simp [J, Impl.restrict, hf], fun f hf v w => by simp [J, Impl.restrict, hf]⟩
  have hx : ∀ c ∈ r.ctors, ∀ args, CallExtra t c args → CallExtra u c args :=
    fun c hc _ ⟨row, hr, os, hos, o, ho, hi, ⟨b, hb, hn⟩, hs⟩ =>
      ⟨row, hr, os, hos, o, ho, hi, ⟨b, ProfileTable.LeAt.mem (h _ (Rel.ctorReads_sub hc _ (by
        simp only [ctorReads, hr, hos, Option.getD_some, List.mem_map, List.mem_filter]
        exact ⟨o, ⟨ho, optionApplies_of_scope hs⟩, rfl⟩))) hi hb,
        hn⟩, hs⟩
  refine ⟨J, ⟨fun f v => ?_, fun f v w => ?_⟩, ?_⟩
  · by_cases hf : Ctor.un f ∈ r.ctors
    · simp only [J, Impl.restrict, hf, ite_true]; exact (hun f v).imp_right (hx _ hf _)
    · left; simp [J, Impl.restrict, hf]
  · by_cases hf : Ctor.bin f ∈ r.ctors
    · simp only [J, Impl.restrict, hf, ite_true]; exact (hbin f v w).imp_right (hx _ hf _)
    · left; simp [J, Impl.restrict, hf]
  · exact Rel.AllowedI.monoOn h ((Rel.allowedI_congr hag out).mp ho)

/-! ## Deciding it -/

/-- A decidable test of `LeAt`. -/
def ProfileTable.leAtB (t u : ProfileTable) (p : Read) : Bool :=
  (t.allows p.1 p.2.1 p.2.2).all fun b => (u.allows p.1 p.2.1 p.2.2).any (behaviourLe p.2.1 b ·)

omit [Boxes.Ambient] in
theorem ProfileTable.leAt_of_leAtB {t u : ProfileTable} {p : Read}
    (h : t.leAtB u p = true) : t.LeAt u p := fun b hb => by
  simp only [leAtB, List.all_eq_true, List.any_eq_true] at h
  exact h b hb

/-- The transfer check for `r`, from the profile `t` to `u`. -/
def transferB (r : Rel) (t u : ProfileTable) : Bool := r.reads.all (u.leAtB t ·)

/-- **What `transferB` says**: whatever holds of every result `t` allows for
`r` holds of every result `u` allows. -/
theorem Rel.transfer_of_transferB {r : Rel} {t u : ProfileTable} (h : transferB r t u = true)
    {cat : Catalog} {out : Relation} (ho : r.AllowedP u cat out) : r.AllowedP t cat out :=
  Rel.AllowedP_transfer (fun p hp => ProfileTable.leAt_of_leAtB
    (List.all_eq_true.mp h p hp)) ho

/-! ## Functions an engine lacks -/

/-- The aggregates of a plan. -/
def Rel.aggFns : Rel → List AggFn
  | .read _ | .values _ _ => []
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _
  | .distinct r | .unnest r _ => r.aggFns
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ => a.aggFns ++ b.aggFns
  | .aggregate r _ ms => r.aggFns ++ ms.map (·.fn)

/-- The Substrait names of the functions a plan calls. -/
def Rel.functions (r : Rel) : List String :=
  ((r.ctors ++ r.aggFns.map Ctor.agg).filterMap rowOf |>.map (·.name)).eraseDups

/-- The functions of `r` that `t`'s engine has no expression for, with the facts. -/
def ProfileTable.missingIn (t : ProfileTable) (fns : List String) : List (String × List String) :=
  fns.filterMap fun f => (t.missing.lookup f).map (f, ·)

/-! ## The report, for Python

The reports over the profiles (`Rel.dependenciesJson`, `transferJson`) are
with the engines' tables, in `SubstraitLean/EngineTables.lean`. -/

/-- What `t` allows at `group` (`none`: the row without a group) and `option`. -/
def ProfileTable.allowsAt (t : ProfileTable) (group : Option String) (option : String)
    (ps : List Behaviour) : List Behaviour :=
  match group with
  | some g => t.allows g option ps
  | none => match t.dflt? option, OptionSpec.find? option with
    | some c, some o => c.allows o.core ps
    | _, _ => []

def ObsTable.factsAt (obs : ObsTable) (group : Option String) (option : String) : List String :=
  let row := match group with
    | some g => obs.row? g option
    | none => (obs.find? fun (x : Option String × String × ObsRow) =>
        x.1.isNone && x.2.1 == option).map fun (x : Option String × String × ObsRow) => x.2.2
  match row with
  | some { evidence := .tested ids _, .. } | some { evidence := .proved _ ids, .. } => ids
  | some { evidence := .probed ids _, .. } => ids
  | _ => []

/-- One group and option a contract's transformation meets: the reference's
behaviours its reads there use, and whether every read states its preference
(a key's `NULLS FIRST`): an engine that gives a stated preference as stated
needs no shim there. -/
structure Dep where
  group : String
  option : String
  behaviours : List Behaviour
  stated : Bool

/-- The dependencies of `reads`, one per group and option. -/
def deps (reads : List Read) : List Dep :=
  (reads.map fun (g, o, _) => (g, o)).eraseDups.map fun (g, o) =>
    let here := reads.filter fun (g', o', _) => g' == g && o' == o
    { group := g, option := o, stated := here.all fun (_, _, ps) => !ps.isEmpty
      behaviours := (here.flatMap fun (_, _, ps) => Profile.reference.table.allows g o ps).eraseDups }

open Lean (Json toJson) in
def Dep.json (d : Dep) : Json :=
  Json.mkObj [("group", toJson d.group), ("option", toJson d.option),
    ("behaviours", toJson d.behaviours), ("stated", toJson d.stated)]

open Lean (Json toJson) in
/-- The dependency report of a contract's transformation: one row per group
and option it meets, with the reference's behaviours there (`deps`). -/
def readsJson (reads : List Read) : Json := Json.arr ((deps reads).map Dep.json).toArray

/-- The dependency report of a contract's transformation, from `Rel.reads`. -/
def Rel.dependsJson (r : Rel) : Lean.Json := readsJson r.reads

end Substrait
