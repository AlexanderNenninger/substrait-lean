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
here every constructor but `fetch`, `window` and an `aggregate` with a measure that
sorts its rows, whose open cells and tie-free cases are proved one at a time.
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

/-- The plans whose choices are proved: so far, those without a `fetch`, a `window` or
an `aggregate` with a measure that sorts its rows (`FIRST`, `LAST`, `STRING_AGG`,
`collect`, `MODE`), whose cells are open. -/
def Rel.ChoicesSupported : Rel → Bool
  | .read _ | .values _ _ => true
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ | .distinct r | .unnest r _ =>
    r.ChoicesSupported
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ =>
    a.ChoicesSupported && b.ChoicesSupported
  | .aggregate r _ ms => r.ChoicesSupported && ms.all (·.fn.sorts == false)
  | .fetch .. | .window .. => false

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

omit [Boxes.Ambient] in
theorem mapM_of_forall {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    have ih := mapM_of_forall (f := f) (g := g) (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.mapM_cons, h x (List.mem_cons_self ..), List.map_cons, Option.bind_eq_bind,
      Option.bind_some, ih, Option.pure_def]

/-- Measures that do not sort their rows have exact cells. -/
theorem choices_nonsorting (grp : Relation) {ms : List Measure}
    (h : ∀ m ∈ ms, m.fn.sorts = false) :
    ms.mapM (fun m => m.choice grp) = some (ms.map fun m => TieChoice.val (m.eval grp)) :=
  mapM_of_forall (g := fun m : Measure => TieChoice.val (m.eval grp)) fun m hm => by
    simp [Measure.choice, h m hm]

/-- The cells of groups whose measures do not sort their rows. -/
theorem choices_groups (G : List (Row × Relation)) {ms : List Measure}
    (h : ∀ m ∈ ms, m.fn.sorts = false) :
    G.mapM (fun x => (ms.mapM (fun m : Measure => m.choice x.2)).bind fun cells =>
        pure (x.1.map TieChoice.val ++ cells)) =
      some (toChoices (G.map fun x => x.1 ++ ms.map fun m => m.eval x.2)) := by
  rw [mapM_of_forall (g := fun x => (x.1 ++ ms.map fun m => m.eval x.2).map TieChoice.val)]
  · simp [toChoices, Function.comp_def]
  · intro x _
    simp [choices_nonsorting x.2 h, Function.comp_def]

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
  | .aggregate r gs ms, hs => by
    simp only [Rel.ChoicesSupported, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hs
    have ih := Rel.evalChoices_eq cat r hs.1
    simp only [Rel.evalChoices, ih, exactRows_toChoices, Option.bind_eq_bind, Option.bind_some,
      Rel.eval, aggregateEval]
    by_cases hg : gs.isEmpty = true
    · simp only [hg, ↓reduceIte]
      simpa using choices_groups [(([] : Row), eval cat r)] hs.2
    · simp only [hg]
      simpa [Function.comp_def] using
        choices_groups ((distinctRows (List.map (fun row => groupKey gs row) (eval cat r))).map
          fun k => (k, groupRows gs (eval cat r) k)) hs.2

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
