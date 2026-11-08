import SubstraitLean.WSet

/-!
# Incremental view maintenance over Z-sets

Bags cannot express deletions, so updates are modelled as **Z-sets**: rows
with signed multiplicities (DBSP, Budiu et al., VLDB 2023). A Z-set is a
weighted relation over `Int` (`WSet Int`, `SubstraitLean/WSet.lean`); adding
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

end Substrait
