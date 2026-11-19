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

/-- A supported plan's choices are the rows `Rel.eval` gives, as values. -/
theorem Rel.evalChoices_eq (cat : Catalog) : ∀ r : Rel, r.ChoicesSupported = true →
    r.evalChoices cat = some (toChoices (r.eval cat))
  | .read _, _ => rfl
  | .values _ _, _ => rfl
  | .filter r c, hs => by
    have ih := Rel.evalChoices_eq cat r hs
    simp [Rel.evalChoices, ih, exactRows_toChoices, Rel.eval]
  | .project r es, hs => by
    have ih := Rel.evalChoices_eq cat r hs
    simp only [Rel.evalChoices, ih, Rel.eval, Option.bind_eq_bind, Option.bind_some]
    rw [mapM_toChoices _ (fun row => row ++ es.map fun e => e.eval row) (fun row => by
      simp only [mapM_exact_val]
      simp [List.map_append, Function.comp_def])]
  | .emit r m, hs => by
    have ih := Rel.evalChoices_eq cat r hs
    simp [Rel.evalChoices, ih, Rel.eval, toChoices, Function.comp_def]
  | .orderBy r keys, hs => by
    have ih := Rel.evalChoices_eq cat r hs
    simp [Rel.evalChoices, ih, exactRows_toChoices, Rel.eval]
  | .distinct r, hs => by
    have ih := Rel.evalChoices_eq cat r hs
    simp [Rel.evalChoices, ih, exactRows_toChoices, Rel.eval]
  | .unnest r c, hs => by
    have ih := Rel.evalChoices_eq cat r hs
    simp [Rel.evalChoices, ih, exactRows_toChoices, Rel.eval]
  | .cross a b, hs => by
    simp only [Rel.ChoicesSupported, Bool.and_eq_true] at hs
    simp [Rel.evalChoices, Rel.evalChoices_eq cat a hs.1, Rel.evalChoices_eq cat b hs.2,
      exactRows_toChoices, Rel.eval]
  | .join a b .inner on, hs => by
    simp only [Rel.ChoicesSupported, Bool.and_eq_true] at hs
    simp [Rel.evalChoices, Rel.evalChoices_eq cat a hs.1, Rel.evalChoices_eq cat b hs.2,
      exactRows_toChoices, Rel.eval]
  | .join a b .left on, hs => by
    simp only [Rel.ChoicesSupported, Bool.and_eq_true] at hs
    simp [Rel.evalChoices, Rel.evalChoices_eq cat a hs.1, Rel.evalChoices_eq cat b hs.2,
      exactRows_toChoices, Rel.eval]
  | .unionAll a b, hs => by
    simp only [Rel.ChoicesSupported, Bool.and_eq_true] at hs
    simp [Rel.evalChoices, Rel.evalChoices_eq cat a hs.1, Rel.evalChoices_eq cat b hs.2,
      exactRows_toChoices, Rel.eval]
  | .semi a b anti on, hs => by
    simp only [Rel.ChoicesSupported, Bool.and_eq_true] at hs
    simp [Rel.evalChoices, Rel.evalChoices_eq cat a hs.1, Rel.evalChoices_eq cat b hs.2,
      exactRows_toChoices, Rel.eval]
  | .fetch .., hs => by simp [Rel.ChoicesSupported] at hs
  | .window .., hs => by simp [Rel.ChoicesSupported] at hs
  | .aggregate .., hs => by simp [Rel.ChoicesSupported] at hs

/-- **Whatever `allows_rows` accepts is a result the reference allows**, for the plans
`Rel.ChoicesSupported` holds of: if `out` matches `r.evalChoices cat`, some reordering
of it is in `Rel.OrderAllowed`. -/
theorem Rel.evalChoices_allowed (cat : Catalog) (r : Rel) (hs : r.ChoicesSupported = true)
    (cs : List (List TieChoice)) (h : r.evalChoices cat = some cs) (out : Relation)
    (hm : Relation.MatchesChoices cs out) : ∃ o, o.Perm out ∧ r.OrderAllowed cat o := by
  rw [Rel.evalChoices_eq cat r hs, Option.some.injEq] at h
  subst h
  exact ⟨r.eval cat, (matchesChoices_toChoices.mp hm).symm, Rel.eval_orderAllowed cat r⟩

end Substrait
