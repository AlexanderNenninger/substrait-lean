import Sverify.Analysis.WSet
import Sverify.Core.Forall2

/-!
# Incremental view maintenance over Z-sets

Bags cannot express deletions, so updates are modelled as **Z-sets**: rows
with signed multiplicities (DBSP, Budiu et al., VLDB 2023). A Z-set is a
weighted relation over `Int` (`WSet Int`, `analysis/Sverify/Analysis/WSet.lean`); adding
Z-sets is list append, and a deletion is a row with negative weight.

Equivalence is `List.Perm`. It is finer than Z-set equality (it never
cancels `+1` against `-1`), so every `Perm` result below also holds for Z-sets.

`Rel.zeval` is `Rel.evalK` over `Int` with Lean's functions
(`Rel.zeval`), so `incremental_sound` and `zeval_lift` are the
`WSet` theorems at `Int`. For the incremental fragment (`Rel.Incremental`: every operator except left
join and fetch):

* `Rel.zeval_add`: evaluating on an updated database equals the old result
  plus a delta, `Q(D + ΔD) ~ Q(D) + ΔQ`.
* `Rel.delta_correct`: `Rel.delta` turns a plan into an ordinary plan that
  computes `ΔQ` from the old tables and the change tables. It can be run by
  any engine.
* `Rel.zeval_lift`: on ordinary bags (all weights 1) Z-set evaluation agrees
  with `Rel.eval`.
* `Rel.zeval_prune`: a stored table pruned to the columns the plan reads
  (`Rel.readsOnly`, decided) and consolidated gives each row of the plan's
  result its weight, and `Rel.incremental_sound_prune` carries the delta
  rule to that store (#1329, ruling 116 A2).
-/

namespace Substrait
variable [Boxes.Ambient]

abbrev ZSet := WSet Int

namespace ZSet

/-- Every row with weight `1`. -/
def lift (r : Relation) : ZSet := r.map (·, 1)

/-- Normal form: one entry per row with its total weight, zero weights
dropped. Only used to display and compare results. -/
def consolidate (z : ZSet) : ZSet :=
  let rows := (List.map (·.1) z).eraseDups
  List.filter (·.2 != 0)
    (List.map (fun r => (r, (List.map (·.2) (List.filter (·.1 == r) z)).sum)) rows)

end ZSet

/-- A catalog of Z-sets; `cat + Δ` applies a change set (`WCatalog`'s `+`). -/
abbrev ZCatalog := String → ZSet

omit [Boxes.Ambient] in
theorem ZCatalog.add_apply (cat Δ : ZCatalog) (t : String) : (cat + Δ) t = cat t ++ Δ t := rfl

/-- Z-set semantics: `Rel.evalK` over `Int` with Lean's functions. -/
def Rel.zeval (cat : ZCatalog) (r : Rel) : ZSet := r.evalK Impl.lean cat

/-! ## The delta of a plan

`r.zdelta cat Δ` is the change that `Δ` causes in `r`'s output: the delta plan
`Rel.delta` run on a catalog with the old tables under their own names and
the change tables under fresh ones (`Rel.deltaName`). Every catalog of that
shape gives the same rows (`Rel.delta_evalK_eq`). -/

/-- A name for `t`'s change table that is no table of `r`: `t` followed by a
suffix longer than all of `r`'s table names. -/
def Rel.deltaName (r : Rel) (t : String) : String :=
  t ++ String.ofList (List.replicate (r.tables.foldr (fun t n => max t.length n) 0 + 1) '+')

/-- The old tables under their own names, the changes under `Rel.deltaName`. -/
def Rel.deltaCatalog (r : Rel) (cat Δ : ZCatalog) : ZCatalog := fun s =>
  match r.tables.find? (fun t => r.deltaName t == s) with
  | some t => Δ t
  | none => cat s

/-- The change in a plan's output caused by the change set `Δ`. -/
def Rel.zdelta (cat Δ : ZCatalog) (r : Rel) : ZSet :=
  (r.delta r.deltaName).zeval (r.deltaCatalog cat Δ)

omit [Boxes.Ambient] in
theorem Rel.length_lt_deltaName {r : Rel} {t : String} (ht : t ∈ r.tables) (u : String) :
    t.length < (r.deltaName u).length := by
  have : ∀ l : List String, t ∈ l → t.length ≤ l.foldr (fun t n => max t.length n) 0 := by
    intro l; induction l with
    | nil => simp
    | cons x l ih =>
      intro h
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)
  simp only [deltaName, String.length_append, String.length_ofList, List.length_replicate]
  have := this _ ht; omega

omit [Boxes.Ambient] in
theorem Rel.deltaCatalog_old {r : Rel} {cat Δ : ZCatalog} {t : String} (ht : t ∈ r.tables) :
    r.deltaCatalog cat Δ t = cat t := by
  unfold deltaCatalog
  rw [List.find?_eq_none.mpr fun u hu => by
    simpa using (Nat.ne_of_lt (length_lt_deltaName ht u)).symm ∘ congrArg String.length]

omit [Boxes.Ambient] in
theorem Rel.deltaCatalog_new {r : Rel} {cat Δ : ZCatalog} {t : String} (ht : t ∈ r.tables) :
    r.deltaCatalog cat Δ (r.deltaName t) = Δ t := by
  unfold deltaCatalog
  cases h : r.tables.find? (fun u => r.deltaName u == r.deltaName t) with
  | none => exact absurd (List.find?_eq_none.mp h t ht) (by simp)
  | some u =>
    have := List.find?_some h
    simp only [deltaName, beq_iff_eq, String.append_left_inj] at this
    rw [this]

/-- A plan only depends on the tables it reads. -/
theorem Rel.zeval_congr {C cat : ZCatalog} {r : Rel} (h : ∀ t ∈ r.tables, C t = cat t) :
    r.zeval C = r.zeval cat :=
  evalK_congr h

/-- **Delta rule**: `Q(D + ΔD) ~ Q(D) + ΔQ`. -/
theorem Rel.zeval_add {cat Δ : ZCatalog} {r : Rel} (h : r.Incremental) :
    (r.zeval (cat + Δ)).Perm (r.zeval cat ++ r.zdelta cat Δ) :=
  incrementalK_sound h (fun _ => deltaCatalog_old) (fun _ => deltaCatalog_new)

/-- **The delta plan computes the delta.** `C` is the engine's catalog: old
tables under their own names and change tables under `δ t`. -/
theorem Rel.delta_correct {C cat Δ : ZCatalog} {δ : String → String} {r : Rel}
    (_ : r.Incremental) (hold : ∀ t ∈ r.tables, C t = cat t)
    (hδ : ∀ t ∈ r.tables, C (δ t) = Δ t) : (r.delta δ).zeval C = r.zdelta cat Δ :=
  delta_evalK_eq hold hδ (fun _ => deltaCatalog_old) (fun _ => deltaCatalog_new)

/-- **Incremental maintenance is sound**: the new result is the old result
plus the output of the delta plan. -/
theorem Rel.incremental_sound {C cat Δ : ZCatalog} {δ : String → String} {r : Rel}
    (h : r.Incremental)
    (hold : ∀ t ∈ r.tables, C t = cat t) (hδ : ∀ t ∈ r.tables, C (δ t) = Δ t) :
    (r.zeval (cat + Δ)).Perm (r.zeval cat ++ (r.delta δ).zeval C) :=
  incrementalK_sound h hold hδ

/-! ## Agreement with bag semantics -/

/-- On ordinary bags (every weight `1`), Z-set evaluation is `Rel.eval`. -/
theorem Rel.zeval_lift {cat : Catalog} {r : Rel} (h : r.Incremental) :
    r.zeval (fun t => ZSet.lift (cat t).rows) = ZSet.lift (r.eval cat) :=
  evalK_lift h

/-! ## Z-set evaluation only depends on weights -/

/-- `Σ g(row) · weight` over a Z-set. -/
def ZSet.lin (g : Row → Int) (z : ZSet) : Int := (List.map (fun x : Row × Int => g x.1 * x.2) z).sum

omit [Boxes.Ambient] in
theorem ZSet.lin_nil (g : Row → Int) : ZSet.lin g [] = 0 := rfl

omit [Boxes.Ambient] in
theorem ZSet.lin_cons (g : Row → Int) (x : Row × Int) (z : ZSet) :
    ZSet.lin g (x :: z) = g x.1 * x.2 + ZSet.lin g z := by
  simp [ZSet.lin]

omit [Boxes.Ambient] in
theorem ZSet.lin_append (g : Row → Int) (a b : ZSet) :
    ZSet.lin g (a ++ b) = ZSet.lin g a + ZSet.lin g b := by
  simp [ZSet.lin]

omit [Boxes.Ambient] in
theorem sum_map_add {L : List Row} (f h : Row → Int) :
    (L.map fun r => f r + h r).sum = (L.map f).sum + (L.map h).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; omega

omit [Boxes.Ambient] in
theorem sum_map_zero {L : List Row} : (L.map fun _ => (0 : Int)).sum = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

omit [Boxes.Ambient] in
theorem sum_indicator_out {L : List Row} {a : Row} (ha : a ∉ L) (f : Row → Int) :
    (L.map fun r => if a = r then f r else 0).sum = 0 := by
  induction L with
  | nil => rfl
  | cons b L ih =>
      simp only [List.mem_cons, not_or] at ha
      simp [ha.1, ih ha.2]

omit [Boxes.Ambient] in
theorem sum_indicator {L : List Row} (hL : L.Nodup) {a : Row} (ha : a ∈ L) (f : Row → Int) :
    (L.map fun r => if a = r then f r else 0).sum = f a := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
      rw [List.nodup_cons] at hL
      simp only [List.map_cons, List.sum_cons]
      by_cases h : a = b
      · subst h; simp [sum_indicator_out hL.1]
      · simp only [h, ite_false, Int.zero_add]
        exact ih hL.2 ((List.mem_cons.mp ha).resolve_left h)

omit [Boxes.Ambient] in
/-- `lin g z` is a sum over any duplicate-free list of rows covering `z`. -/
theorem ZSet.lin_support (g : Row → Int) :
    ∀ (z : ZSet) {L : List Row}, L.Nodup → (∀ x ∈ z, x.1 ∈ L) →
      ZSet.lin g z = (L.map fun r => g r * WSet.weight z r).sum
  | [], L, _, _ => by simp [ZSet.lin_nil, WSet.weight_nil, sum_map_zero]
  | x :: z, L, hL, hz => by
      have hrest := ZSet.lin_support g z hL (fun y hy => hz y (List.mem_cons_of_mem _ hy))
      have hsplit : (L.map fun r => g r * WSet.weight (x :: z) r) =
          L.map fun r => (if x.1 = r then g r * x.2 else 0) + g r * WSet.weight z r := by
        refine List.map_congr_left fun r _ => ?_
        rw [WSet.weight_cons]; split <;> simp [Int.mul_add]
      rw [ZSet.lin_cons, hsplit, sum_map_add, hrest,
        sum_indicator hL (hz x List.mem_cons_self) (fun r => g r * x.2)]

omit [Boxes.Ambient] in
theorem nodup_eraseDups : ∀ (l : List Row), l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.2 ⟨fun h => ?_, nodup_eraseDups _⟩
      rw [List.mem_eraseDups, List.mem_filter] at h
      simp at h
termination_by l => l.length
decreasing_by simp; exact Nat.lt_succ_of_le (List.length_filter_le _ _)

omit [Boxes.Ambient] in
/-- **Linear functionals only see weights.** -/
theorem ZSet.lin_congr (g : Row → Int) {z z' : ZSet} (h : ∀ r, z.weight r = z'.weight r) :
    ZSet.lin g z = ZSet.lin g z' := by
  let L := (List.map (·.1) z ++ List.map (·.1) z').eraseDups
  have hL : L.Nodup := nodup_eraseDups _
  have hz : ∀ x ∈ z, x.1 ∈ L := fun x hx => by
    simp only [L, List.mem_eraseDups, List.mem_append, List.mem_map]; exact .inl ⟨x, hx, rfl⟩
  have hz' : ∀ x ∈ z', x.1 ∈ L := fun x hx => by
    simp only [L, List.mem_eraseDups, List.mem_append, List.mem_map]; exact .inr ⟨x, hx, rfl⟩
  rw [ZSet.lin_support g z hL hz, ZSet.lin_support g z' hL hz']
  exact congrArg List.sum (List.map_congr_left fun r _ => by rw [h r])

omit [Boxes.Ambient] in
theorem ZSet.weight_eq_lin (z : ZSet) (r : Row) :
    z.weight r = ZSet.lin (fun s => if s = r then 1 else 0) z := by
  induction z with
  | nil => rfl
  | cons x z ih => rw [WSet.weight_cons, ZSet.lin_cons, ih]; split <;> simp

omit [Boxes.Ambient] in
theorem ZSet.weight_filter (p : Row → Bool) (z : ZSet) (r : Row) :
    (WSet.filter p z).weight r = ZSet.lin (fun s => if p s ∧ s = r then 1 else 0) z := by
  induction z with
  | nil => rfl
  | cons x z ih =>
      simp only [WSet.filter, List.filter_cons] at ih ⊢
      rw [ZSet.lin_cons, ← ih]
      by_cases hp : p x.1 <;> simp only [hp, ite_true, WSet.weight_cons] <;> split <;>
        simp_all

omit [Boxes.Ambient] in
theorem ZSet.weight_map (f : Row → Row) (z : ZSet) (r : Row) :
    (WSet.map f z).weight r = ZSet.lin (fun s => if f s = r then 1 else 0) z := by
  induction z with
  | nil => rfl
  | cons x z ih =>
      simp only [WSet.map, List.map_cons] at ih ⊢
      rw [WSet.weight_cons, ZSet.lin_cons, ← ih]; split <;> simp

omit [Boxes.Ambient] in
theorem ZSet.weight_cross (a b : ZSet) (r : Row) :
    (WSet.cross a b).weight r =
      ZSet.lin (fun xa => ZSet.lin (fun xb => if xa ++ xb = r then 1 else 0) b) a := by
  induction a with
  | nil => rfl
  | cons x a ih =>
      simp only [WSet.cross, List.flatMap_cons] at ih ⊢
      rw [WSet.weight_append, ih, ZSet.lin_cons]
      congr 1
      clear ih
      induction b with
      | nil => simp [WSet.weight_nil, ZSet.lin_nil]
      | cons y b ihb =>
          rw [List.map_cons, WSet.weight_cons, ihb, ZSet.lin_cons]
          split <;> simp [Int.mul_add, Int.mul_comm]

/-- Two Z-catalogs agree on a table when the table's rows have the same weights. -/
def ZCatalog.SameWeights (cat cat' : ZCatalog) (ts : List String) : Prop :=
  ∀ t ∈ ts, ∀ row, (cat t).weight row = (cat' t).weight row

private theorem Rel.zeval_weight_congr_aux {cat cat' : ZCatalog} :
    ∀ {r : Rel}, r.Incremental → cat.SameWeights cat' r.tables →
      ∀ row, (r.evalK Impl.lean cat).weight row = (r.evalK Impl.lean cat').weight row
  | .read t, _, h, row => h t (by simp [tables]) row
  | .values _ _, _, _, _ => rfl
  | .filter r c, hr, h, row => by
      simp only [evalK, ZSet.weight_filter]
      exact ZSet.lin_congr _ (zeval_weight_congr_aux (r := r) hr h)
  | .project r es, hr, h, row => by
      simp only [evalK, ZSet.weight_map]
      exact ZSet.lin_congr _ (zeval_weight_congr_aux (r := r) hr h)
  | .emit r m, hr, h, row => by
      simp only [evalK, ZSet.weight_map]
      exact ZSet.lin_congr _ (zeval_weight_congr_aux (r := r) hr h)
  | .orderBy r keys, hr, h, row => by
      rw [evalK, evalK, WSet.weight_mergeSort, WSet.weight_mergeSort]
      exact zeval_weight_congr_aux (r := r) hr h row
  | .unionAll a b, hr, h, row => by
      have ha : cat.SameWeights cat' a.tables := fun t ht => h t (by simp [tables, ht])
      have hb : cat.SameWeights cat' b.tables := fun t ht => h t (by simp [tables, ht])
      simp only [evalK, WSet.weight_append, zeval_weight_congr_aux hr.1 ha,
        zeval_weight_congr_aux hr.2 hb]
  | .cross a b, hr, h, row => by
      have ha : cat.SameWeights cat' a.tables := fun t ht => h t (by simp [tables, ht])
      have hb : cat.SameWeights cat' b.tables := fun t ht => h t (by simp [tables, ht])
      simp only [evalK, ZSet.weight_cross]
      rw [ZSet.lin_congr _ (zeval_weight_congr_aux hr.1 ha)]
      exact congrArg List.sum (List.map_congr_left fun x _ => by
        simp only []; rw [ZSet.lin_congr _ (zeval_weight_congr_aux hr.2 hb)])
  | .join a b .inner on, hr, h, row => by
      have ha : cat.SameWeights cat' a.tables := fun t ht => h t (by simp [tables, ht])
      have hb : cat.SameWeights cat' b.tables := fun t ht => h t (by simp [tables, ht])
      simp only [evalK, ZSet.weight_filter]
      refine ZSet.lin_congr _ fun s => ?_
      simp only [ZSet.weight_cross]
      rw [ZSet.lin_congr _ (zeval_weight_congr_aux hr.1 ha)]
      exact congrArg List.sum (List.map_congr_left fun x _ => by
        simp only []; rw [ZSet.lin_congr _ (zeval_weight_congr_aux hr.2 hb)])
  | .join _ _ .left _, hr, _, _ => hr.elim
  | .fetch _ _ _, hr, _, _ | .window _ _ _ _, hr, _, _ | .semi _ _ _ _, hr, _, _
  | .distinct _, hr, _, _ => hr.elim

/-- **Views only depend on weights.** On the incremental fragment, Z-set
evaluation on catalogs whose tables have the same weights gives results
with the same weights. -/
theorem Rel.zeval_weight_congr {cat cat' : ZCatalog} {r : Rel} (hr : r.Incremental)
    (h : cat.SameWeights cat' r.tables) (row : Row) :
    (r.zeval cat).weight row = (r.zeval cat').weight row :=
  zeval_weight_congr_aux hr h row

/-! ## Pruning a table to the columns a plan reads (#1329, ruling 116 A2) -/

/-- Two rows of one length that agree on the columns `N`. -/
def Row.AgreeOn (N : List Nat) (x y : Row) : Prop :=
  x.length = y.length ∧ ∀ i ∈ N, x.getD i .null = y.getD i .null

/-- Two Z-sets, row by row of one weight, whose rows agree on `N`. -/
def ZSet.AgreeOn (N : List Nat) (a b : ZSet) : Prop :=
  Forall2 (fun x y => Row.AgreeOn N x.1 y.1 ∧ x.2 = y.2) a b

/-- The columns `N` from `k` on, counted from `k`. -/
def shiftCols (k : Nat) (N : List Nat) : List Nat :=
  N.filterMap fun i => if k ≤ i then some (i - k) else none

/-- The columns read by the expressions at positions `k, k + 1, …` that `N` holds. -/
def colsAt (N : List Nat) : Nat → List Expr → List Nat
  | _, [] => []
  | k, e :: es => (if k ∈ N then e.cols else []) ++ colsAt N (k + 1) es

/-- The columns of table `t` that `r` reads to give the columns `N` of its
output, the schema taken from `sc`. A plan outside the incremental fragment
reads all of them. -/
def Rel.colsOf (sc : Catalog) (t : String) : Rel → List Nat → List Nat
  | .read u, N => if u = t then N.filter (· < (sc t).arity) else []
  | .values _ _, _ => []
  | .filter r c, N => r.colsOf sc t (N ++ c.cols)
  | .project r es, N => r.colsOf sc t (N ++ colsAt N (r.arity sc) es)
  | .emit r m, N => r.colsOf sc t (colsAt N 0 (m.map .field))
  | .orderBy r keys, N => r.colsOf sc t (N ++ keys.map (·.col))
  | .cross a b, N =>
      a.colsOf sc t (N.filter (· < a.arity sc)) ++ b.colsOf sc t (shiftCols (a.arity sc) N)
  | .join a b .inner on, N =>
      a.colsOf sc t ((N ++ on.cols).filter (· < a.arity sc)) ++
        b.colsOf sc t (shiftCols (a.arity sc) (N ++ on.cols))
  | .unionAll a b, N => a.colsOf sc t N ++ b.colsOf sc t N
  | .join _ _ .left _, _ | .fetch _ _ _, _ | .window _ _ _ _, _ | .semi _ _ _ _, _
  | .distinct _, _ | .aggregate _ _ _, _ | .unnest _ _, _ => List.range (sc t).arity

/-- The checker's test: `r`'s output reads only the columns `S` of table `t`. -/
def Rel.readsOnly (sc : Catalog) (t : String) (S : List Nat) (r : Rel) : Bool :=
  (r.colsOf sc t (List.range (r.arity sc))).all (· ∈ S)

/-- Every row of every table has its table's arity in `sc`. -/
def ZCatalog.HasArity (sc : Catalog) (cat : ZCatalog) : Prop :=
  ∀ u, ∀ x ∈ cat u, x.1.length = (sc u).arity

/-! ### Arities -/

theorem Rel.zeval_length {sc : Catalog} {cat : ZCatalog} (hc : cat.HasArity sc) :
    ∀ {r : Rel}, r.Incremental → r.WF sc → ∀ x ∈ r.zeval cat, x.1.length = r.arity sc
  | .read u, _, _, x, hx => hc u x hx
  | .values _ _, _, hwf, x, hx => by
      simp only [zeval, evalK, WSet.lift, List.mem_map] at hx
      obtain ⟨row, hrow, rfl⟩ := hx
      exact hwf row hrow
  | .filter r _, h, hwf, x, hx => by
      simp only [zeval, evalK, WSet.filter, List.mem_filter] at hx
      exact zeval_length hc (r := r) h hwf.1 x hx.1
  | .project r es, h, hwf, x, hx => by
      simp only [zeval, evalK, WSet.map, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp [arity, zeval_length hc (r := r) h hwf.1 y hy]
  | .emit r m, _, _, x, hx => by
      simp only [zeval, evalK, WSet.map, List.mem_map] at hx
      obtain ⟨y, _, rfl⟩ := hx
      simp [arity]
  | .orderBy r _, h, hwf, x, hx => by
      simp only [zeval, evalK, List.mem_mergeSort] at hx
      exact zeval_length hc (r := r) h hwf.1 x hx
  | .cross a b, h, hwf, x, hx => by
      simp only [zeval, evalK, WSet.cross, List.mem_flatMap, List.mem_map] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      simp [arity, zeval_length hc (r := a) h.1 hwf.1 y hy, zeval_length hc (r := b) h.2 hwf.2 z hz]
  | .join a b .inner _, h, hwf, x, hx => by
      simp only [zeval, evalK, WSet.filter, WSet.cross, List.mem_filter, List.mem_flatMap,
        List.mem_map] at hx
      obtain ⟨⟨y, hy, z, hz, rfl⟩, _⟩ := hx
      simp [arity, zeval_length hc (r := a) h.1 hwf.1 y hy,
        zeval_length hc (r := b) h.2 hwf.2.1 z hz]
  | .unionAll a b, h, hwf, x, hx => by
      simp only [zeval, evalK, List.mem_append] at hx
      rcases hx with hx | hx
      · exact zeval_length hc (r := a) h.1 hwf.1 x hx
      · rw [arity, hwf.2.2]; exact zeval_length hc (r := b) h.2 hwf.2.1 x hx
  | .join _ _ .left _, h, _, _, _ | .fetch _ _ _, h, _, _, _ | .window _ _ _ _, h, _, _, _
  | .semi _ _ _ _, h, _, _, _ | .distinct _, h, _, _, _ | .aggregate _ _ _, h, _, _, _
  | .unnest _ _, h, _, _, _ => h.elim

/-! ### Rows that agree on the columns read -/

omit [Boxes.Ambient] in
theorem Forall2.map_mem {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ}
    {g : β → δ} : ∀ {l : List α} {l' : List β}, Forall2 R l l' →
      (∀ a ∈ l, ∀ b, R a b → S (f a) (g b)) → Forall2 S (l.map f) (l'.map g)
  | _, _, .nil, _ => .nil
  | _, _, .cons hab t, h =>
    .cons (h _ (List.mem_cons_self ..) _ hab)
      (Forall2.map_mem t fun a ha => h a (List.mem_cons_of_mem _ ha))

omit [Boxes.Ambient] in
theorem Forall2.flatMap_mem {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → List γ} {g : β → List δ} : ∀ {l : List α} {l' : List β}, Forall2 R l l' →
      (∀ a ∈ l, ∀ b, R a b → Forall2 S (f a) (g b)) → Forall2 S (l.flatMap f) (l'.flatMap g)
  | _, _, .nil, _ => .nil
  | _, _, .cons hab t, h =>
    Forall2.append (h _ (List.mem_cons_self ..) _ hab)
      (Forall2.flatMap_mem t fun a ha => h a (List.mem_cons_of_mem _ ha))

omit [Boxes.Ambient] in
theorem Forall2.zip_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → ∀ p ∈ l.zip l', R p.1 p.2
  | _, _, .nil, _, hp => by simp at hp
  | _, _, .cons hab t, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hab
    · exact Forall2.zip_mem t p hp

omit [Boxes.Ambient] in
theorem Forall2.of_pairs {α β : Type} {R : α → β → Prop} :
    ∀ {L : List (α × β)}, (∀ p ∈ L, R p.1 p.2) → Forall2 R (L.map (·.1)) (L.map (·.2))
  | [], _ => .nil
  | _ :: _, h => .cons (h _ (List.mem_cons_self ..))
      (Forall2.of_pairs fun p hp => h p (List.mem_cons_of_mem _ hp))

omit [Boxes.Ambient] in
/-- Sorting keeps two related lists related, where the orders agree on related pairs. -/
theorem Forall2.mergeSort {α β : Type} {R : α → β → Prop} {le : α → α → Bool}
    {le' : β → β → Bool} {l : List α} {l' : List β} (h : Forall2 R l l')
    (hle : ∀ a ∈ l, ∀ b ∈ l, ∀ a' b', R a a' → R b b' → le a b = le' a' b') :
    Forall2 R (l.mergeSort le) (l'.mergeSort le') := by
  have hlen := h.length_eq
  have h1 : (l.zip l').map (·.1) = l := List.map_fst_zip (Nat.le_of_eq hlen)
  have h2 : (l.zip l').map (·.2) = l' := List.map_snd_zip (Nat.le_of_eq hlen.symm)
  have hz := h.zip_mem
  have e1 : l.mergeSort le = ((l.zip l').mergeSort fun p q => le p.1 q.1).map (·.1) := by
    conv => lhs; rw [← h1]
    exact (List.map_mergeSort (f := fun p : α × β => p.1) (r := fun p q : α × β => le p.1 q.1) (s := le)
      fun _ _ _ _ => rfl).symm
  have e2 : l'.mergeSort le' = ((l.zip l').mergeSort fun p q => le p.1 q.1).map (·.2) := by
    conv => lhs; rw [← h2]
    refine (List.map_mergeSort (f := fun p : α × β => p.2) (r := fun p q : α × β => le p.1 q.1) (s := le')
      fun p hp q hq => ?_).symm
    exact hle _ (List.of_mem_zip hp).1 _ (List.of_mem_zip hq).1 _ _ (hz p hp) (hz q hq)
  rw [e1, e2]
  exact Forall2.of_pairs fun p hp => hz p (List.mem_mergeSort.mp hp)

omit [Boxes.Ambient] in
theorem Row.AgreeOn.mono {N N' : List Nat} {x y : Row} (h : Row.AgreeOn N x y)
    (hN : ∀ i ∈ N', i ∈ N) : Row.AgreeOn N' x y :=
  ⟨h.1, fun i hi => h.2 i (hN i hi)⟩

omit [Boxes.Ambient] in
theorem Row.agreeOn_refl (N : List Nat) (x : Row) : Row.AgreeOn N x x := ⟨rfl, fun _ _ => rfl⟩

omit [Boxes.Ambient] in
theorem ZSet.agreeOn_refl (N : List Nat) (z : ZSet) : ZSet.AgreeOn N z z :=
  Forall2.refl fun _ _ => ⟨Row.agreeOn_refl _ _, rfl⟩

omit [Boxes.Ambient] in
theorem ZSet.AgreeOn.mono {N N' : List Nat} {a b : ZSet} (h : ZSet.AgreeOn N a b)
    (hN : ∀ i ∈ N', i ∈ N) : ZSet.AgreeOn N' a b :=
  Forall2.weaken (fun _ _ h => ⟨h.1.mono hN, h.2⟩) h

omit [Boxes.Ambient] in
theorem getD_append' {l l' : Row} {i : Nat} :
    (l ++ l').getD i .null = if i < l.length then l.getD i .null else l'.getD (i - l.length) .null := by
  simp only [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left ‹_›]
  · rw [List.getElem?_append_right (by omega)]

omit [Boxes.Ambient] in
theorem mem_shiftCols {k j : Nat} {N : List Nat} : j ∈ shiftCols k N ↔ k + j ∈ N := by
  simp only [shiftCols, List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq]
  constructor
  · rintro ⟨i, hi, hk, rfl⟩; rwa [Nat.add_sub_cancel' hk]
  · intro h; exact ⟨k + j, h, Nat.le_add_right _ _, by omega⟩

omit [Boxes.Ambient] in
/-- Rows of `k` columns that agree below `k`, followed by rows that agree on
the shifted columns, agree on `N`. -/
theorem Row.AgreeOn.append {N : List Nat} {k : Nat} {x x' y y' : Row} (hk : x.length = k)
    (ha : Row.AgreeOn (N.filter (· < k)) x x') (hb : Row.AgreeOn (shiftCols k N) y y') :
    Row.AgreeOn N (x ++ y) (x' ++ y') := by
  refine ⟨by simp [ha.1, hb.1], fun i hi => ?_⟩
  rw [getD_append', getD_append', ← ha.1, hk]
  split
  · exact ha.2 i (List.mem_filter.mpr ⟨hi, by simpa using ‹i < k›⟩)
  · exact hb.2 _ (mem_shiftCols.mpr (by rwa [Nat.add_sub_cancel' (by omega)]))

/-- The expressions at positions `k + j ∈ N` read only `colsAt N k es`. -/
theorem colsAt_eval {N : List Nat} {x y : Row} :
    ∀ {es : List Expr} {k : Nat}, (∀ i ∈ colsAt N k es, x.getD i .null = y.getD i .null) →
      ∀ j, k + j ∈ N → (es.map (·.eval x)).getD j .null = (es.map (·.eval y)).getD j .null
  | [], _, _, _, _ => rfl
  | e :: es, k, h, j, hj => by
    simp only [colsAt, List.mem_append] at h
    cases j with
    | zero =>
      simp only [List.map_cons, List.getD_cons_zero]
      refine Expr.eval_congr_cols e fun i hi => h i (.inl ?_)
      simp only [show k ∈ N by simpa using hj, ↓reduceIte]; exact hi
    | succ j =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact colsAt_eval (k := k + 1) (fun i hi => h i (.inr hi)) j (by rwa [Nat.add_right_comm])

theorem Row.agreeOn_shift_eval {N : List Nat} {k : Nat} {es : List Expr} {x y : Row}
    (h : ∀ i ∈ colsAt N k es, x.getD i .null = y.getD i .null) :
    Row.AgreeOn (shiftCols k N) (es.map (·.eval x)) (es.map (·.eval y)) :=
  ⟨by simp, fun j hj => colsAt_eval h j (mem_shiftCols.mp hj)⟩

/-- **Columns the plan does not read do not matter.** Two catalogs equal but
at `t`, whose rows there agree on the columns `S`, give rows that agree on
`N`, where `r` reads only `S` of `t` for `N`. -/
theorem Rel.zeval_agreeOn {sc : Catalog} {t : String} {S : List Nat} {C C' : ZCatalog}
    (hc : C.HasArity sc) (hu : ∀ u, u ≠ t → C' u = C u) (ht : ZSet.AgreeOn S (C t) (C' t)) :
    ∀ {r : Rel} {N : List Nat}, r.Incremental → r.WF sc → (∀ i ∈ r.colsOf sc t N, i ∈ S) →
      ZSet.AgreeOn N (r.zeval C) (r.zeval C')
  | .read u, N, _, _, hS => by
      by_cases hut : u = t
      · subst hut
        simp only [colsOf, ite_true, List.mem_filter, decide_eq_true_eq] at hS
        refine Forall2.imp_mem (fun a ha b hab => ⟨⟨hab.1.1, fun i hi => ?_⟩, hab.2⟩) ht
        by_cases hlt : i < (sc u).arity
        · exact hab.1.2 i (hS i ⟨hi, hlt⟩)
        · have h1 := hc u a ha
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by rw [← hab.1.1]; omega)]
      · show ZSet.AgreeOn N (C u) (C' u)
        rw [hu u hut]; exact ZSet.agreeOn_refl _ _
  | .values _ _, _, _, _, _ => ZSet.agreeOn_refl _ _
  | .filter r c, N, h, hwf, hS => by
      have ih := zeval_agreeOn hc hu ht (r := r) (N := N ++ c.cols) h hwf.1 hS
      refine (Forall2.filter (fun a b hab => ?_) ih).weaken fun _ _ h => ⟨h.1.mono
        fun i hi => List.mem_append_left _ hi, h.2⟩
      exact congrArg Value.isTrue (Expr.eval_congr_cols c fun i hi =>
        hab.1.2 i (List.mem_append_right _ hi))
  | .project r es, N, h, hwf, hS => by
      have ih := zeval_agreeOn hc hu ht (r := r) (N := N ++ colsAt N (r.arity sc) es) h hwf.1 hS
      refine Forall2.map_mem ih fun a ha b hab => ⟨?_, hab.2⟩
      refine Row.AgreeOn.append (zeval_length hc (r := r) h hwf.1 a ha)
        (hab.1.mono fun i hi => List.mem_append_left _ (List.mem_filter.mp hi).1)
        (Row.agreeOn_shift_eval fun i hi => hab.1.2 i (List.mem_append_right _ hi))
  | .emit r m, N, h, hwf, hS => by
      have ih := zeval_agreeOn hc hu ht (r := r) (N := colsAt N 0 (m.map .field)) h hwf.1 hS
      refine Forall2.map_mem ih fun a _ b hab => ⟨?_, hab.2⟩
      have hm : ∀ x : Row, m.map (x.getD · .null) = (m.map Expr.field).map (·.eval x) := by
        intro x; simp [Function.comp_def, Expr.eval]
      show Row.AgreeOn N (m.map (a.1.getD · .null)) (m.map (b.1.getD · .null))
      rw [hm, hm]
      exact ⟨by simp, fun i hi => colsAt_eval hab.1.2 i (by simpa using hi)⟩
  | .orderBy r keys, N, h, hwf, hS => by
      have ih := zeval_agreeOn hc hu ht (r := r) (N := N ++ keys.map (·.col)) h hwf.1 hS
      refine (Forall2.mergeSort ih fun a _ b _ a' b' ha hb => ?_).weaken
        fun _ _ h => ⟨h.1.mono fun i hi => List.mem_append_left _ hi, h.2⟩
      exact (sortLe_congr (fun k hk => (ha.1.2 _ (List.mem_append_right _
        (List.mem_map_of_mem hk))).symm) (fun k hk => (hb.1.2 _ (List.mem_append_right _
        (List.mem_map_of_mem hk))).symm)).symm
  | .cross a b, N, h, hwf, hS => by
      simp only [colsOf, List.mem_append] at hS
      have iha := zeval_agreeOn hc hu ht (r := a) h.1 hwf.1 fun i hi => hS i (.inl hi)
      have ihb := zeval_agreeOn hc hu ht (r := b) h.2 hwf.2 fun i hi => hS i (.inr hi)
      refine Forall2.flatMap_mem iha fun x hx x' hxx => Forall2.map_mem ihb fun y _ y' hyy => ?_
      exact ⟨Row.AgreeOn.append (zeval_length hc h.1 hwf.1 x hx) hxx.1 hyy.1, by rw [hxx.2, hyy.2]⟩
  | .join a b .inner on, N, h, hwf, hS => by
      simp only [colsOf, List.mem_append] at hS
      have iha := zeval_agreeOn hc hu ht (r := a) h.1 hwf.1 fun i hi => hS i (.inl hi)
      have ihb := zeval_agreeOn hc hu ht (r := b) h.2 hwf.2.1 fun i hi => hS i (.inr hi)
      have hx : ZSet.AgreeOn (N ++ on.cols) (WSet.cross (a.zeval C) (b.zeval C))
          (WSet.cross (a.zeval C') (b.zeval C')) :=
        Forall2.flatMap_mem iha fun x hx x' hxx => Forall2.map_mem ihb fun y _ y' hyy =>
          ⟨Row.AgreeOn.append (zeval_length hc h.1 hwf.1 x hx) hxx.1 hyy.1, by rw [hxx.2, hyy.2]⟩
      refine (Forall2.filter (fun p q hpq => ?_) hx).weaken fun _ _ h => ⟨h.1.mono
        fun i hi => List.mem_append_left _ hi, h.2⟩
      exact congrArg Value.isTrue (Expr.eval_congr_cols on fun i hi =>
        hpq.1.2 i (List.mem_append_right _ hi))
  | .unionAll a b, N, h, hwf, hS => by
      simp only [colsOf, List.mem_append] at hS
      exact Forall2.append (zeval_agreeOn hc hu ht (r := a) h.1 hwf.1 fun i hi => hS i (.inl hi))
        (zeval_agreeOn hc hu ht (r := b) h.2 hwf.2.1 fun i hi => hS i (.inr hi))
  | .join _ _ .left _, _, h, _, _ | .fetch _ _ _, _, h, _, _ | .window _ _ _ _, _, h, _, _
  | .semi _ _ _ _, _, h, _, _ | .distinct _, _, h, _, _ | .aggregate _ _ _, _, h, _, _
  | .unnest _ _, _, h, _, _ => h.elim

omit [Boxes.Ambient] in
/-- `consolidate` keeps every row's weight. -/
theorem ZSet.weight_consolidate (z : ZSet) (row : Row) :
    (consolidate z).weight row = z.weight row := by
  -- Dropping zero weights keeps each row's weight.
  have hdrop : ∀ l : ZSet, WSet.weight (List.filter (·.2 != 0) l) row = l.weight row := by
    intro l; induction l with
    | nil => rfl
    | cons x l ih =>
      rw [List.filter_cons, WSet.weight_cons]
      split
      · rw [WSet.weight_cons, ih]
      · rename_i hx; simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hx
        rw [ih, hx]; split <;> simp
  -- The sum of a row's entries is its weight.
  have hsum : (List.map (·.2) (List.filter (·.1 == row) z)).sum = z.weight row := by
    induction z with
    | nil => rfl
    | cons x z ih =>
      rw [List.filter_cons, WSet.weight_cons]
      by_cases hx : x.1 = row
      · simp [hx, ih]
      · simp [hx, ih]
  -- Over distinct rows, each row's entry appears once.
  have hone : ∀ L : List Row, L.Nodup → WSet.weight (L.map fun r =>
      (r, (List.map (·.2) (List.filter (·.1 == r) z)).sum)) row =
        if row ∈ L then z.weight row else 0 := by
    intro L hL
    induction L with
    | nil => rfl
    | cons r L ih =>
      rw [List.nodup_cons] at hL
      rw [List.map_cons, WSet.weight_cons, ih hL.2]
      by_cases hr : r = row
      · subst hr; simp [hL.1, ← hsum]
      · simp [hr, Ne.symm hr]
  unfold consolidate
  rw [hdrop, hone _ (nodup_eraseDups _)]
  split
  · rfl
  · exact (WSet.weight_of_not_mem fun h => ‹_ ∉ _› (List.mem_eraseDups.mpr h)).symm

omit [Boxes.Ambient] in
theorem ZSet.weight_map_congr (f : Row → Row) {z z' : ZSet} (h : ∀ r, z.weight r = z'.weight r)
    (row : Row) : (WSet.map f z).weight row = (WSet.map f z').weight row := by
  rw [ZSet.weight_map, ZSet.weight_map, ZSet.lin_congr _ h]

/-! ### The pruned store -/

/-- The columns `S` of a row, in that order. -/
def Row.project (S : List Nat) (x : Row) : Row := S.map (x.getD · .null)

/-- The first `n` columns of a row, NULL where `S` does not hold the column. -/
def Row.mask (S : List Nat) (n : Nat) (x : Row) : Row :=
  (List.range n).map fun i => if i ∈ S then x.getD i .null else .null

/-- Where each of the first `n` columns sits in a row projected to `S`: its
place in `S`, or past `S`'s end (so NULL) when `S` does not hold it. -/
def widen (S : List Nat) (n : Nat) : List Nat := (List.range n).map S.idxOf

/-- The store with table `t` pruned to the columns `S`, consolidated. -/
def ZCatalog.prune (cat : ZCatalog) (t : String) (S : List Nat) : ZCatalog := fun u =>
  if u = t then ZSet.consolidate (WSet.map (Row.project S) (cat t)) else cat u

/-- `r` with every read of `t` replaced by `q`. -/
def Rel.substRead : Rel → String → Rel → Rel
  | .read u, t, q => if u = t then q else .read u
  | .values k rows, _, _ => .values k rows
  | .filter r c, t, q => .filter (r.substRead t q) c
  | .project r es, t, q => .project (r.substRead t q) es
  | .emit r m, t, q => .emit (r.substRead t q) m
  | .cross a b, t, q => .cross (a.substRead t q) (b.substRead t q)
  | .join a b ty on, t, q => .join (a.substRead t q) (b.substRead t q) ty on
  | .unionAll a b, t, q => .unionAll (a.substRead t q) (b.substRead t q)
  | .fetch r o c, t, q => .fetch (r.substRead t q) o c
  | .window r p s f, t, q => .window (r.substRead t q) p s f
  | .orderBy r keys, t, q => .orderBy (r.substRead t q) keys
  | .semi a b anti on, t, q => .semi (a.substRead t q) (b.substRead t q) anti on
  | .distinct r, t, q => .distinct (r.substRead t q)
  | .unnest r c, t, q => .unnest (r.substRead t q) c
  | .aggregate r gs ms, t, q => .aggregate (r.substRead t q) gs ms

/-- `r` over the pruned store: each read of `t` widened back to `n` columns,
NULL in those the store dropped. -/
def Rel.pruneRead (t : String) (S : List Nat) (n : Nat) (r : Rel) : Rel :=
  r.substRead t (.emit (.read t) (widen S n))

omit [Boxes.Ambient] in
theorem Rel.Incremental.substRead {t : String} {q : Rel} (hq : q.Incremental) :
    ∀ {r : Rel}, r.Incremental → (r.substRead t q).Incremental
  | .read u, _ => by by_cases h : u = t <;> simp [Rel.substRead, h, hq, Rel.Incremental]
  | .values _ _, _ => trivial
  | .filter r _, h | .project r _, h | .emit r _, h | .orderBy r _, h =>
      Incremental.substRead hq (r := r) h
  | .cross a b, h | .unionAll a b, h | .join a b .inner _, h =>
      ⟨Incremental.substRead hq (r := a) h.1, Incremental.substRead hq (r := b) h.2⟩
  | .join _ _ .left _, h | .fetch _ _ _, h | .window _ _ _ _, h | .semi _ _ _ _, h
  | .distinct _, h | .aggregate _ _ _, h | .unnest _ _, h => h.elim

/-- Replacing the reads of `t` by `q` is reading `q`'s rows as `t`. -/
theorem Rel.zeval_substRead {C : ZCatalog} {t : String} {q : Rel} :
    ∀ {r : Rel}, r.Incremental →
      (r.substRead t q).zeval C = r.zeval fun u => if u = t then q.zeval C else C u
  | .read u, _ => by by_cases h : u = t <;> simp [Rel.substRead, zeval, evalK, h]
  | .values _ _, _ => rfl
  | .filter r _, h | .project r _, h | .emit r _, h | .orderBy r _, h => by
      have ih := zeval_substRead (C := C) (t := t) (q := q) (r := r) h
      simp only [zeval] at ih
      simp only [substRead, zeval, evalK, ih]
  | .cross a b, h | .unionAll a b, h | .join a b .inner _, h => by
      have iha := zeval_substRead (C := C) (t := t) (q := q) (r := a) h.1
      have ihb := zeval_substRead (C := C) (t := t) (q := q) (r := b) h.2
      simp only [zeval] at iha ihb
      simp only [substRead, zeval, evalK, iha, ihb]
  | .join _ _ .left _, h | .fetch _ _ _, h | .window _ _ _ _, h | .semi _ _ _ _, h
  | .distinct _, h | .aggregate _ _ _, h | .unnest _ _, h => h.elim

omit [Boxes.Ambient] in
/-- Widening a projected row gives the masked row. -/
theorem widen_project (S : List Nat) (n : Nat) (x : Row) :
    (widen S n).map ((Row.project S x).getD · .null) = Row.mask S n x := by
  simp only [widen, Row.mask, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Row.project]
  by_cases hi : i ∈ S
  · have hl := List.idxOf_lt_length_of_mem hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl, hi]
  · rw [List.idxOf_eq_length hi]
    simp [List.getD_eq_getElem?_getD, hi]

omit [Boxes.Ambient] in
/-- A row of `n` columns agrees with its mask on `S`. -/
theorem Row.agreeOn_mask {S : List Nat} {n : Nat} {x : Row} (h : x.length = n) :
    Row.AgreeOn S x (Row.mask S n x) := by
  refine ⟨by simp [Row.mask, h], fun i hi => ?_⟩
  simp only [Row.mask, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hlt : i < n
  · simp [List.getElem?_range hlt, hi]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]; rfl

omit [Boxes.Ambient] in
/-- Rows that agree on all `k` columns, the first of `k` columns, are equal. -/
theorem ZSet.AgreeOn.eq {k : Nat} :
    ∀ {a b : ZSet}, ZSet.AgreeOn (List.range k) a b → (∀ x ∈ a, x.1.length = k) → a = b
  | _, _, .nil, _ => rfl
  | x :: _, y :: _, .cons hxy t, hl => by
    have hx := hl x (List.mem_cons_self ..)
    have hy : y.1.length = k := hxy.1.1 ▸ hx
    have hrow : x.1 = y.1 := by
      refine List.ext_getElem? fun i => ?_
      by_cases hi : i < k
      · have := hxy.1.2 i (List.mem_range.mpr hi)
        simp only [List.getD_eq_getElem?_getD] at this
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this ⊢
        simpa using this
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    rw [Prod.ext hrow hxy.2, ZSet.AgreeOn.eq t fun z hz => hl z (List.mem_cons_of_mem _ hz)]

/-- **The pruned store gives the view** (ruling 116, A2). Where `r` reads only
the columns `S` of table `t` (`Rel.readsOnly`, decided), evaluating `r` with
each read of `t` widened back (`Rel.pruneRead`) over the store whose `t` holds
only those columns, consolidated (`ZCatalog.prune`), gives every row of `r`'s
result its weight. -/
theorem Rel.zeval_prune {sc : Catalog} {cat : ZCatalog} {t : String} {S : List Nat} {r : Rel}
    (hr : r.Incremental) (hwf : r.WF sc) (hc : cat.HasArity sc)
    (hS : r.readsOnly sc t S = true) (row : Row) :
    ((r.pruneRead t S (sc t).arity).zeval (cat.prune t S)).weight row =
      (r.zeval cat).weight row := by
  let n := (sc t).arity
  let C₂ : ZCatalog := fun u => if u = t then WSet.map (Row.mask S n) (cat t) else cat u
  -- The masked table gives the same rows: `r` reads none of the masked columns.
  have h₂ : r.zeval C₂ = r.zeval cat := by
    have hS' : ∀ i ∈ r.colsOf sc t (List.range (r.arity sc)), i ∈ S := by
      simpa [Rel.readsOnly, List.all_eq_true] using hS
    have hag := zeval_agreeOn (C := cat) (C' := C₂) hc
      (fun u hu => by simp [C₂, hu])
      (by simp only [C₂, ↓reduceIte]
          exact forall₂_map_self _ fun x hx => ⟨Row.agreeOn_mask (hc t x hx), rfl⟩) hr hwf hS'
    exact (ZSet.AgreeOn.eq hag (zeval_length hc hr hwf)).symm
  -- The widened reads of the pruned store are the masked table, up to weights.
  rw [← h₂, Rel.pruneRead, zeval_substRead hr]
  refine zeval_weight_congr hr (fun u _ row => ?_) row
  by_cases hu : u = t
  · subst hu
    simp only [C₂, ↓reduceIte, zeval, evalK, ZCatalog.prune]
    rw [ZSet.weight_map_congr _ (ZSet.weight_consolidate _)]
    simp only [WSet.map, List.map_map]
    congr 2; funext x
    simp only [Function.comp_apply, widen_project]; rfl
  · simp only [hu, ↓reduceIte, C₂, ZCatalog.prune]

omit [Boxes.Ambient] in
/-- Pruning a changed store is pruning the store and the change, up to weights. -/
theorem ZCatalog.weight_prune_add (cat Δ : ZCatalog) (t : String) (S : List Nat) (u : String)
    (row : Row) : ((cat.prune t S + Δ.prune t S) u).weight row =
      ((cat + Δ).prune t S u).weight row := by
  by_cases hu : u = t
  · subst hu
    simp only [ZCatalog.add_apply, ZCatalog.prune, ↓reduceIte, WSet.weight_append,
      ZSet.weight_consolidate, WSet.map, List.map_append]
  · simp only [ZCatalog.add_apply, ZCatalog.prune, hu, ↓reduceIte]

/-- **Incremental maintenance on the pruned store is sound**: the new result
is, row for row of equal weight, the old result over the pruned store plus the
delta plan's output over the pruned old tables and the pruned changes. -/
theorem Rel.incremental_sound_prune {sc : Catalog} {cat Δ C : ZCatalog} {t : String}
    {S : List Nat} {δ : String → String} {r : Rel}
    (hr : r.Incremental) (hwf : r.WF sc) (hc : (cat + Δ).HasArity sc)
    (hS : r.readsOnly sc t S = true)
    (hold : ∀ u ∈ (r.pruneRead t S (sc t).arity).tables, C u = cat.prune t S u)
    (hδ : ∀ u ∈ (r.pruneRead t S (sc t).arity).tables, C (δ u) = Δ.prune t S u) (row : Row) :
    (r.zeval (cat + Δ)).weight row = ((r.pruneRead t S (sc t).arity).zeval (cat.prune t S) ++
      ((r.pruneRead t S (sc t).arity).delta δ).zeval C).weight row := by
  have hi : (r.pruneRead t S (sc t).arity).Incremental :=
    Rel.Incremental.substRead (q := .emit (.read t) (widen S (sc t).arity)) trivial hr
  rw [← zeval_prune hr hwf hc hS, ← WSet.weight_perm (incremental_sound hi hold hδ)]
  exact zeval_weight_congr hi (fun u _ row => (ZCatalog.weight_prune_add cat Δ t S u row).symm) row

end Substrait
