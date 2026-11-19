import SubstraitLean.Choices
import Sverify.Core.OrderAllowed

/-!
# `Rel.evalChoices` accepts only what the reference allows (#1484)

`Rel.evalChoices` (`Choices.lean`) is the oracle of the public
`sverify.testing.allows_rows`: for each cell of a result, the values every order
the reference allows gives. What makes a passing `allows_rows` evidence is that
whatever it accepts is a result the reference allows:

    `Rel.evalChoices_allowed`: if `r.evalChoices cat = some cs` and `out` matches
    `cs`, some reordering of `out` is in `r.OrderAllowed cat`.

`TieChoice.Matches` is stated through the model's own `AggFn.apply`, so the
separators, `NULL` arguments and the empty case are the model's. Rows match as a
multiset: the order of an accepted result is the caller's (`orderBy` over open
cells returns the rows unsorted).

The converse (an allowed result is accepted) is false, and is not stated: a class
pick that reaches a sign-sensitive expression (`MIN` over `{-0.0, 0.0}` then
`CAST(.. AS VARCHAR)`), and a `FETCH` over an `ORDER BY` with a clustered key
(`SortAllowed` lets the groups come in any order), give allowed results the oracle
rejects. It is the oracle's known gap, a false alarm and no false assurance.

The theorem is proved for the plans `Rel.ChoicesSupported` holds of, in steps:
here every constructor but `aggregate`, `fetch` and `window`, whose open cells and
tie-free cases are proved one at a time.
-/

namespace Substrait

variable [Boxes.Ambient]

/-- What a choice allows one cell to be. -/
def TieChoice.Matches : TieChoice → Value → Prop
  | .val v, x => x = v
  | .anyOf vs, x => x ∈ vs
  | .concat sep cs, x =>
    ∃ ps, Forall2 List.Perm ps cs ∧ x = (AggFn.concat sep).apply ps.flatten
  | .collect cs, x =>
    ∃ ps, Forall2 List.Perm ps cs ∧ x = AggFn.collect.apply ps.flatten

/-- A result against rows of choices: some reordering of its rows matches them, cell
by cell. -/
def Relation.MatchesChoices (cs : List (List TieChoice)) (out : Relation) : Prop :=
  ∃ o, out.Perm o ∧ Forall2 (Forall2 TieChoice.Matches) cs o

/-- The plans whose choices are proved: so far, those without an `aggregate`, a
`fetch` or a `window`. -/
def Rel.ChoicesSupported : Rel → Bool
  | .read _ | .values _ _ => true
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ | .distinct r | .unnest r _ =>
    r.ChoicesSupported
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ =>
    a.ChoicesSupported && b.ChoicesSupported
  | .fetch .. | .window .. | .aggregate .. => false

theorem forall2_val_eq : ∀ {as bs : Row},
    Forall2 TieChoice.Matches (as.map TieChoice.val) bs → bs = as
  | [], _, .nil => rfl
  | _ :: _, _, .cons ha ht => by
    simp only [TieChoice.Matches] at ha
    rw [ha, forall2_val_eq ht]

theorem forall2_val_refl : ∀ as : Row, Forall2 TieChoice.Matches (as.map TieChoice.val) as
  | [] => .nil
  | _ :: as => .cons rfl (forall2_val_refl as)

theorem forall2_rows_eq : ∀ {vs os : Relation},
    Forall2 (Forall2 TieChoice.Matches) (toChoices vs) os → os = vs
  | [], _, .nil => rfl
  | _ :: _, _, .cons hh ht => by
    rw [forall2_val_eq hh]
    congr 1
    exact forall2_rows_eq ht

theorem forall2_rows_refl : ∀ vs : Relation,
    Forall2 (Forall2 TieChoice.Matches) (toChoices vs) vs
  | [] => .nil
  | _ :: vs => .cons (forall2_val_refl _) (forall2_rows_refl vs)

theorem matchesChoices_toChoices {vs out : Relation} :
    Relation.MatchesChoices (toChoices vs) out ↔ out.Perm vs := by
  constructor
  · rintro ⟨o, hp, h⟩
    rw [forall2_rows_eq h] at hp; exact hp
  · intro hp
    exact ⟨vs, hp, forall2_rows_refl vs⟩

omit [Boxes.Ambient] in
/-- A row of choices that are all values is the row of values. -/
theorem mapM_exact_eq : ∀ {c : List TieChoice} {row : Row},
    c.mapM TieChoice.exact? = some row → c = row.map TieChoice.val
  | [], row, h => by simp [List.mapM_nil] at h; subst h; rfl
  | .val v :: c, row, h => by
    simp only [List.mapM_cons, TieChoice.exact?, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, a, ha, hrow⟩ := h
    cases Option.some.inj hr
    simp only [Option.pure_def, Option.some.injEq] at hrow
    subst hrow
    simp only [List.map_cons]
    rw [← mapM_exact_eq ha]
  | .anyOf _ :: _, _, h => by simp [List.mapM_cons, TieChoice.exact?] at h
  | .concat _ _ :: _, _, h => by simp [List.mapM_cons, TieChoice.exact?] at h
  | .collect _ :: _, _, h => by simp [List.mapM_cons, TieChoice.exact?] at h

omit [Boxes.Ambient] in
/-- `exactRows` of rows of choices that are all values: the rows of values. -/
theorem exactRows_eq : ∀ {cs : List (List TieChoice)} {vs : Relation},
    exactRows cs = some vs → cs = toChoices vs
  | [], vs, h => by simp [exactRows, List.mapM_nil] at h; subst h; rfl
  | c :: cs, vs, h => by
    simp only [exactRows, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨row, hr, rest, hrest, hvs⟩ := h
    simp only [Option.pure_def, Option.some.injEq] at hvs
    subst hvs
    unfold toChoices at *
    simp only [List.map_cons]
    rw [← mapM_exact_eq hr]
    congr 1
    exact exactRows_eq hrest

omit [Boxes.Ambient] in
theorem mapM_exact_val : ∀ row : Row, (row.map TieChoice.val).mapM TieChoice.exact? = some row
  | [] => rfl
  | v :: row => by
    simp only [List.map_cons, List.mapM_cons, TieChoice.exact?, mapM_exact_val row,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]

omit [Boxes.Ambient] in
theorem exactRows_toChoices : ∀ vs : Relation, exactRows (toChoices vs) = some vs
  | [] => rfl
  | row :: vs => by
    have := exactRows_toChoices vs
    unfold exactRows toChoices at *
    simp only [List.map_cons, List.mapM_cons, mapM_exact_val, this, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]

omit [Boxes.Ambient] in
theorem flatMap_perm_fun {α β : Type} {xs : List α} {f g : α → List β}
    (h : ∀ x ∈ xs, (f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (ih fun y hy => h y (by simp [hy]))

omit [Boxes.Ambient] in
theorem crossRows_perm {x x' y y' : Relation} (hx : x.Perm x') (hy : y.Perm y') :
    (crossRows x y).Perm (crossRows x' y') := by
  unfold crossRows
  exact (flatMap_perm_fun fun a _ => hy.map _).trans (hx.flatMap_right _)

omit [Boxes.Ambient] in
theorem mapM_toChoices (F : List TieChoice → Option (List TieChoice)) (f : Row → Row)
    (hF : ∀ row, F (row.map TieChoice.val) = some ((f row).map TieChoice.val)) :
    ∀ vs : Relation, (toChoices vs).mapM F = some (toChoices (vs.map f))
  | [] => rfl
  | v :: vs => by
    have ih := mapM_toChoices F f hF vs
    show List.mapM F (v.map TieChoice.val :: toChoices vs) =
      some ((f v).map TieChoice.val :: toChoices (vs.map f))
    rw [List.mapM_cons, hF, ih]
    rfl

omit [Boxes.Ambient] in
theorem getD_val (row : Row) (i : Nat) :
    (row.map TieChoice.val).getD i (.val .null) = .val (row.getD i .null) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases row[i]? <;> rfl

omit [Boxes.Ambient] in
/-- The first step of each case: a child's choices are values, `vs` of them, and the
reference allows a reordering of those values. -/
theorem child_exact {cs0 : List (List TieChoice)} {vs0 : Relation} {vs : Relation}
    (hv0 : exactRows cs0 = some vs0) (hc : cs0 = toChoices vs) : vs0 = vs := by
  rw [hc, exactRows_toChoices] at hv0
  exact (Option.some.inj hv0).symm

omit [Boxes.Ambient] in
theorem ite_isEmpty_perm {α : Type} (A : List α) {ms ms' : List α} (hm : ms.Perm ms') :
    (if ms.isEmpty then A else ms).Perm (if ms'.isEmpty then A else ms') := by
  cases ms with
  | nil => have : ms' = [] := List.perm_nil.mp hm.symm; subst this; exact .refl _
  | cons m ms =>
    cases ms' with
    | nil => exact absurd (List.perm_nil.mp hm) (by simp)
    | cons m' ms' => simpa using hm

theorem leftJoinRow_perm (on : Expr) (n : Nat) {y y' : Relation} (hy : y.Perm y') (x : Row) :
    (leftJoinRow on n y x).Perm (leftJoinRow on n y' x) := by
  unfold leftJoinRow
  exact ite_isEmpty_perm _ ((hy.map _).filter _)

theorem hasMatch_perm (on : Expr) {y y' : Relation} (hy : y.Perm y') (x : Row) :
    hasMatch on y x = hasMatch on y' x := by
  unfold hasMatch
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true]
  constructor <;> rintro ⟨z, hz, h⟩
  · exact ⟨z, hy.mem_iff.mp hz, h⟩
  · exact ⟨z, hy.mem_iff.mpr hz, h⟩

/-- A supported plan's choices are values only: the rows of some result, one reordering
of which the reference allows. -/
theorem Rel.evalChoices_exact (cat : Catalog) : ∀ r : Rel, r.ChoicesSupported = true →
    ∀ cs, r.evalChoices cat = some cs →
      ∃ vs, cs = toChoices vs ∧ ∃ o, o.Perm vs ∧ r.OrderAllowed cat o
  | .read t, _, cs, h => by
    simp only [Rel.evalChoices, Option.some.injEq] at h
    exact ⟨_, h.symm, _, .refl _, .refl _⟩
  | .values n rows, _, cs, h => by
    simp only [Rel.evalChoices, Option.some.injEq] at h
    exact ⟨_, h.symm, _, .refl _, .refl _⟩
  | .filter r c, hs, cs, h => by
    simp only [Rel.ChoicesSupported] at hs
    simp only [Rel.evalChoices, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cs0, h0, vs0, hv0, hcs⟩ := h
    obtain ⟨vs, hc, o, ho, hal⟩ := Rel.evalChoices_exact cat r hs cs0 h0
    obtain rfl := child_exact hv0 hc
    exact ⟨_, hcs.symm, o.filter _, ho.filter _, o, hal, rfl⟩
  | .project r es, hs, cs, h => by
    simp only [Rel.ChoicesSupported] at hs
    simp only [Rel.evalChoices, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨cs0, h0, hcs⟩ := h
    obtain ⟨vs, hc, o, ho, hal⟩ := Rel.evalChoices_exact cat r hs cs0 h0
    subst hc
    rw [mapM_toChoices _ (fun row => row ++ es.map fun e => e.eval row) (fun row => by
      simp only [mapM_exact_val]
      simp [List.map_append, Function.comp_def])] at hcs
    obtain rfl := Option.some.inj hcs
    exact ⟨_, rfl, _, ho.map _, o, hal, rfl⟩
  | .emit r m, hs, cs, h => by
    simp only [Rel.ChoicesSupported] at hs
    simp only [Rel.evalChoices, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cs0, h0, hcs⟩ := h
    obtain ⟨vs, hc, o, ho, hal⟩ := Rel.evalChoices_exact cat r hs cs0 h0
    subst hc hcs
    refine ⟨vs.map fun row => m.map (row.getD · .null), ?_, _, ho.map _, o, hal, rfl⟩
    simp only [toChoices, List.map_map, Function.comp_def, getD_val]
  | .orderBy r keys, hs, cs, h => by
    simp only [Rel.ChoicesSupported] at hs
    simp only [Rel.evalChoices, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨cs0, h0, hcs⟩ := h
    obtain ⟨vs, hc, o, ho, hal⟩ := Rel.evalChoices_exact cat r hs cs0 h0
    subst hc
    rw [exactRows_toChoices] at hcs
    simp only [Option.some.injEq] at hcs
    subst hcs
    exact ⟨_, rfl, o.mergeSort (sortLe keys),
      ((List.mergeSort_perm _ _).trans ho).trans (List.mergeSort_perm _ _).symm,
      o, hal, List.mergeSort_perm _ _, .of_sorted (mergeSort_sorted keys _)⟩
  | .distinct r, hs, cs, h => by
    simp only [Rel.ChoicesSupported] at hs
    simp only [Rel.evalChoices, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cs0, h0, vs0, hv0, hcs⟩ := h
    obtain ⟨vs, hc, o, ho, hal⟩ := Rel.evalChoices_exact cat r hs cs0 h0
    obtain rfl := child_exact hv0 hc
    exact ⟨_, hcs.symm, distinctRows o, canonReps_perm Row.leRaw_rawOrder ho, o, hal,
      distinctRows o, canonReps_isReps Row.leRaw_rawOrder _, .refl _⟩
  | .unnest r c, hs, cs, h => by
    simp only [Rel.ChoicesSupported] at hs
    simp only [Rel.evalChoices, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cs0, h0, vs0, hv0, hcs⟩ := h
    obtain ⟨vs, hc, o, ho, hal⟩ := Rel.evalChoices_exact cat r hs cs0 h0
    obtain rfl := child_exact hv0 hc
    exact ⟨_, hcs.symm, _, ho.flatMap_right _, o, hal, .refl _⟩
  | .cross a b, hs, cs, h => by
    simp only [Rel.ChoicesSupported, Bool.and_eq_true] at hs
    simp only [Rel.evalChoices, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ca, ha, va, hva, cb, hb, vb, hvb, hcs⟩ := h
    obtain ⟨xa, hca, oa, hoa, hala⟩ := Rel.evalChoices_exact cat a hs.1 ca ha
    obtain ⟨xb, hcb, ob, hob, halb⟩ := Rel.evalChoices_exact cat b hs.2 cb hb
    obtain rfl := child_exact hva hca
    obtain rfl := child_exact hvb hcb
    exact ⟨_, hcs.symm, _, crossRows_perm hoa hob, oa, ob, hala, halb, .refl _⟩
  | .join a b .inner on, hs, cs, h => by
    simp only [Rel.ChoicesSupported, Bool.and_eq_true] at hs
    simp only [Rel.evalChoices, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ca, ha, va, hva, cb, hb, vb, hvb, hcs⟩ := h
    obtain ⟨xa, hca, oa, hoa, hala⟩ := Rel.evalChoices_exact cat a hs.1 ca ha
    obtain ⟨xb, hcb, ob, hob, halb⟩ := Rel.evalChoices_exact cat b hs.2 cb hb
    obtain rfl := child_exact hva hca
    obtain rfl := child_exact hvb hcb
    exact ⟨_, hcs.symm, _, (crossRows_perm hoa hob).filter _, oa, ob, hala, halb, .refl _⟩
  | .join a b .left on, hs, cs, h => by
    simp only [Rel.ChoicesSupported, Bool.and_eq_true] at hs
    simp only [Rel.evalChoices, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ca, ha, va, hva, cb, hb, vb, hvb, hcs⟩ := h
    obtain ⟨xa, hca, oa, hoa, hala⟩ := Rel.evalChoices_exact cat a hs.1 ca ha
    obtain ⟨xb, hcb, ob, hob, halb⟩ := Rel.evalChoices_exact cat b hs.2 cb hb
    obtain rfl := child_exact hva hca
    obtain rfl := child_exact hvb hcb
    exact ⟨_, hcs.symm, _,
      (flatMap_perm_fun fun x _ => leftJoinRow_perm on _ hob x).trans (hoa.flatMap_right _),
      oa, ob, hala, halb, .refl _⟩
  | .unionAll a b, hs, cs, h => by
    simp only [Rel.ChoicesSupported, Bool.and_eq_true] at hs
    simp only [Rel.evalChoices, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ca, ha, va, hva, cb, hb, vb, hvb, hcs⟩ := h
    obtain ⟨xa, hca, oa, hoa, hala⟩ := Rel.evalChoices_exact cat a hs.1 ca ha
    obtain ⟨xb, hcb, ob, hob, halb⟩ := Rel.evalChoices_exact cat b hs.2 cb hb
    obtain rfl := child_exact hva hca
    obtain rfl := child_exact hvb hcb
    exact ⟨_, hcs.symm, _, hoa.append hob, oa, ob, hala, halb, .refl _⟩
  | .semi a b anti on, hs, cs, h => by
    simp only [Rel.ChoicesSupported, Bool.and_eq_true] at hs
    simp only [Rel.evalChoices, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ca, ha, va, hva, cb, hb, vb, hvb, hcs⟩ := h
    obtain ⟨xa, hca, oa, hoa, hala⟩ := Rel.evalChoices_exact cat a hs.1 ca ha
    obtain ⟨xb, hcb, ob, hob, halb⟩ := Rel.evalChoices_exact cat b hs.2 cb hb
    obtain rfl := child_exact hva hca
    obtain rfl := child_exact hvb hcb
    have hf : (va.filter fun row => hasMatch on vb row != anti) =
        va.filter fun row => hasMatch on ob row != anti :=
      List.filter_congr fun x _ => by rw [← hasMatch_perm on hob x]
    refine ⟨_, hcs.symm, _, ?_, oa, ob, hala, halb, .refl _⟩
    rw [hf]
    exact hoa.filter _
  | .fetch .., hs, _, _ => by simp [Rel.ChoicesSupported] at hs
  | .window .., hs, _, _ => by simp [Rel.ChoicesSupported] at hs
  | .aggregate .., hs, _, _ => by simp [Rel.ChoicesSupported] at hs

/-- **Whatever `allows_rows` accepts is a result the reference allows**, for the plans
`Rel.ChoicesSupported` holds of: if `out` matches `r.evalChoices cat`, some reordering
of it is in `Rel.OrderAllowed`. -/
theorem Rel.evalChoices_allowed (cat : Catalog) (r : Rel) (hs : r.ChoicesSupported = true)
    (cs : List (List TieChoice)) (h : r.evalChoices cat = some cs) (out : Relation)
    (hm : Relation.MatchesChoices cs out) : ∃ o, o.Perm out ∧ r.OrderAllowed cat o := by
  obtain ⟨vs, rfl, o, ho, hal⟩ := Rel.evalChoices_exact cat r hs cs h
  exact ⟨o, ho.trans (matchesChoices_toChoices.mp hm).symm, hal⟩

end Substrait
