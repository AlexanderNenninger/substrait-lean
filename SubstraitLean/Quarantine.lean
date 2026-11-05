import SubstraitLean.Keys

/-!
# Quarantine: the rows a refresh keeps (#184)

With `on_violation="quarantine"`, a refresh sets aside the rows of a source
that break its preconditions, and the node runs on the others. Which rows it
keeps is a function of the source's rows alone (`kept`), so a refresh batch
by batch and a recompute agree:

* `passRows`: the rows on which every row condition is TRUE (a FALSE or NULL
  breaks it);
* `singletons k`: for a key `k`, the rows whose key occurs once. Every row
  of a repeated key is set aside, so the rule needs no order between rows;
* `kept`: the row conditions, then each key in turn.

`kept_pre` and `kept_keys` prove that the kept rows meet every condition, so
a catalog of kept rows satisfies the hypotheses of `contract_sound` and
`Rel.keys_sound` (`Catalog.kept_sound`): the node's proof holds on what it
reads. `sverify/_quarantine.py` computes the same rule, and its tests compare
the two on random batches.
-/

namespace Substrait

/-- The rows on which every condition of `pre` is TRUE. -/
def passRows (pre : List Expr) (rows : Relation) : Relation :=
  rows.filter fun row => pre.all fun e => (e.eval row).isTrue

theorem passRows_pre {pre : List Expr} {rows : Relation} :
    ∀ row ∈ passRows pre rows, ∀ e ∈ pre, (e.eval row).isTrue = true := by
  intro row h e he
  simp only [passRows, List.mem_filter, List.all_eq_true] at h
  exact h.2 e he

/-- The rows whose key `k` no other row shares. -/
def singletons (k : List Nat) (rows : Relation) : Relation :=
  rows.filter fun row => rows.countP (fun s => keyOf k s == keyOf k row) == 1

theorem singletons_key {k : List Nat} {rows : Relation} : KeyOn k (singletons k rows) := by
  unfold KeyOn
  rw [List.pairwise_iff_forall_sublist]
  intro a b hab heq
  have hsub : [a, b].Sublist rows := hab.trans (List.filter_sublist)
  have ha : a ∈ singletons k rows := hab.subset (by simp)
  simp only [singletons, List.mem_filter, beq_iff_eq] at ha
  have hle := hsub.countP_le (p := fun s => keyOf k s == keyOf k a)
  have h2 : [a, b].countP (fun s => keyOf k s == keyOf k a) = 2 := by
    simp [heq]
  have h1 := ha.2
  omega

/-- The rows a refresh keeps: those meeting the row conditions `pre`, then,
for each key in `keys` in turn, those whose key occurs once. -/
def kept (pre : List Expr) (keys : List (List Nat)) (rows : Relation) : Relation :=
  keys.foldl (fun acc k => singletons k acc) (passRows pre rows)

theorem foldl_singletons_sublist :
    ∀ (keys : List (List Nat)) (rows : Relation),
      (keys.foldl (fun acc k => singletons k acc) rows).Sublist rows
  | [], _ => List.Sublist.refl _
  | k :: ks, rows =>
      (foldl_singletons_sublist ks (singletons k rows)).trans List.filter_sublist

theorem kept_sublist {pre : List Expr} {keys : List (List Nat)} {rows : Relation} :
    (kept pre keys rows).Sublist rows :=
  (foldl_singletons_sublist keys _).trans List.filter_sublist

/-- Every kept row meets the row conditions. -/
theorem kept_pre {pre : List Expr} {keys : List (List Nat)} {rows : Relation} :
    ∀ row ∈ kept pre keys rows, ∀ e ∈ pre, (e.eval row).isTrue = true :=
  fun row h => passRows_pre row ((foldl_singletons_sublist keys _).subset h)

theorem foldl_singletons_key :
    ∀ (keys : List (List Nat)) (rows : Relation), ∀ k ∈ keys,
      KeyOn k (keys.foldl (fun acc k => singletons k acc) rows)
  | [], _, _, h => absurd h (List.not_mem_nil)
  | k :: ks, rows, k', h => by
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact singletons_key.sublist (foldl_singletons_sublist ks _)
      · exact foldl_singletons_key ks _ k' h

/-- Every key holds on the kept rows. -/
theorem kept_keys {pre : List Expr} {keys : List (List Nat)} {rows : Relation} :
    ∀ k ∈ keys, KeyOn k (kept pre keys rows) :=
  foldl_singletons_key keys _

/-- The catalog a node reads under quarantine: each table's kept rows. -/
def Catalog.kept (cat : Catalog) (pre : String → List Expr) (keys : String → List (List Nat)) :
    Catalog :=
  fun t => { arity := (cat t).arity, rows := Substrait.kept (pre t) (keys t) (cat t).rows }

/-- The kept catalog meets what `contract_sound` and `Rel.keys_sound` assume
of their inputs: it is well-formed (with its rows' schema, `hS`), every row
meets its table's preconditions, and every key holds. -/
theorem Catalog.kept_sound {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (pre : String → List Expr) (keys : String → List (List Nat)) :
    (cat.kept pre keys).WF ∧
      (∀ t, ∀ row ∈ (cat.kept pre keys t).rows, EnvMem (S t) row) ∧
      (∀ t, ∀ row ∈ (cat.kept pre keys t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true) ∧
      (∀ t, ∀ k ∈ keys t, KeyOn k (cat.kept pre keys t).rows) :=
  ⟨fun t row h => hcat t row (kept_sublist.subset h),
    fun t row h => hS t row (kept_sublist.subset h),
    fun _ => kept_pre,
    fun _ => kept_keys⟩

end Substrait
