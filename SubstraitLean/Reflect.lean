/-!
# Boolean checks for the tables

The tables' checks (`Functions.lean`, `Options.lean`, `BlackBox.lean`, the
engine profiles) are proved by reflection: a Boolean function evaluated by the
kernel (`decide +kernel` on `check t = true`), and a lemma that turns its
`true` into the proposition. The kernel then evaluates a plain recursive
function, without unfolding a `Decidable` instance at every element and pair.
-/

namespace Substrait

/-- Whether a list's elements are pairwise distinct. -/
def nodupB {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !(x == y)) && nodupB xs

theorem nodup_of_nodupB {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List α}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne] at h
    exact List.nodup_cons.mpr ⟨fun hx => h.1 x hx rfl, nodup_of_nodupB h.2⟩

/-- A check of every element, read as the bounded quantifier. -/
theorem forall_of_all {α : Type} {p : α → Bool} {l : List α} (h : l.all p = true) :
    ∀ x ∈ l, p x = true :=
  List.all_eq_true.mp h

end Substrait
