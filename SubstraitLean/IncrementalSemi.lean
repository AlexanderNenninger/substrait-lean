import SubstraitLean.IncrementalAgg

/-!
# Delta rules for semi and anti joins (#248, stage 2)

A semi join keeps the left rows with a match on the right, an anti join
those without (`Rel.semi`). Whether a left row `x` has a match is whether
the weight of the right rows that match it (`matchCount`) is positive, and
that weight is linear in the right side: the matches in `b + Δb` are the
matches in `b` plus those in `Δb` (`matchCount_append`). So a view can keep
a match count beside its rows and maintain it from the right side's change.

The output changes in three ways (`change`):

* the left side's change `Δa`, kept where the new count says so;
* the old left rows whose count leaves 0 (a semi join emits them, an anti
  join retracts them);
* the old left rows whose count returns to 0 (the other way round).

* `semi_maintained`: the old output plus `change` has the weights of the
  new output, for any join condition.
* `matchCount_by_key`: for a condition that only compares the left row's key
  with the right row (an equi-join), the count only depends on the left
  row's key, so one count per key is enough. This is what `sverify._semi`
  keeps.

The changes only need the right weights (`ChangeFeed`): a change feed may
delete and re-insert a row.
-/

namespace Substrait
namespace SemiDelta

open LinearAgg (ind lin_lift sum_ind_one)

/-- The weight of the rows of `z` that match the left row `x`. -/
def matchCount (on : Expr) (x : Row) (z : ZSet) : Int :=
  ZSet.lin (fun y => ind (on.eval (x ++ y)).isTrue 1) z

theorem matchCount_append (on : Expr) (x : Row) (a b : ZSet) :
    matchCount on x (a ++ b) = matchCount on x a + matchCount on x b := ZSet.lin_append _ _ _

theorem matchCount_congr (on : Expr) (x : Row) {z z' : ZSet} (h : ∀ r, z.weight r = z'.weight r) :
    matchCount on x z = matchCount on x z' := ZSet.lin_congr _ h

/-- On a bag, a left row has a match when its count is positive. -/
theorem hasMatch_iff (on : Expr) (ys : Relation) (x : Row) :
    hasMatch on ys x = decide (0 < matchCount on x (ZSet.lift ys)) := by
  rw [matchCount, lin_lift, sum_ind_one]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Int.natCast_pos, List.length_pos_iff_exists_mem]
  simp [hasMatch, List.any_eq_true]

/-- A left row is in the output: a semi join keeps the rows with a match,
an anti join those without. -/
def keeps (anti : Bool) (n : Int) : Bool := decide (0 < n) != anti

/-- The change of the output: `Δa` where the new count keeps it, the old
left rows the new count keeps and the old one did not, and, retracted, the
old left rows the old count kept and the new one does not. `B` is the old
right side and `ΔB` its change. -/
def change (on : Expr) (anti : Bool) (a : Relation) (Δa B ΔB : ZSet) : ZSet :=
  ZSet.filter (fun x => keeps anti (matchCount on x B + matchCount on x ΔB)) Δa ++
    ZSet.filter (fun x => keeps anti (matchCount on x B + matchCount on x ΔB) &&
      !keeps anti (matchCount on x B)) (ZSet.lift a) ++
    ZSet.neg (ZSet.filter (fun x => keeps anti (matchCount on x B) &&
      !keeps anti (matchCount on x B + matchCount on x ΔB)) (ZSet.lift a))

theorem weight_filter (p : Row → Bool) (z : ZSet) (r : Row) :
    (ZSet.filter p z).weight r = if p r then z.weight r else 0 := by
  induction z with
  | nil => simp [ZSet.filter, ZSet.weight_nil]
  | cons x z ih =>
    simp only [ZSet.filter, List.filter_cons] at ih ⊢
    by_cases hx : x.1 = r
    · subst hx
      split <;> simp_all [ZSet.weight_cons]
    · split <;> simp_all [ZSet.weight_cons]

theorem lift_filter (p : Row → Bool) (rows : Relation) :
    ZSet.lift (rows.filter p) = ZSet.filter p (ZSet.lift rows) := by
  simp [ZSet.lift, ZSet.filter, List.filter_map, Function.comp_def]

/-- **Maintaining a semi or anti join.** The left side goes from the bag
`a` to `a'` by `Δa`, the right side from `b` to `b'` by `Δb` (each with the
right weights). Then the new output has the weights of the old output plus
`change`. -/
theorem semi_maintained {on : Expr} {anti : Bool} {a a' b b' : Relation} {Δa Δb : ZSet}
    (ha : ∀ r, (ZSet.lift a ++ Δa).weight r = (ZSet.lift a').weight r)
    (hb : ∀ r, (ZSet.lift b ++ Δb).weight r = (ZSet.lift b').weight r) (r : Row) :
    (ZSet.lift (a'.filter fun x => hasMatch on b' x != anti)).weight r =
      (ZSet.lift (a.filter fun x => hasMatch on b x != anti) ++
        change on anti a Δa (ZSet.lift b) Δb).weight r := by
  have hnew : ∀ x, (hasMatch on b' x != anti) =
      keeps anti (matchCount on x (ZSet.lift b) + matchCount on x Δb) := fun x => by
    rw [hasMatch_iff, ← matchCount_congr on x hb, matchCount_append]; rfl
  have hold : ∀ x, (hasMatch on b x != anti) = keeps anti (matchCount on x (ZSet.lift b)) :=
    fun x => by rw [hasMatch_iff]; rfl
  simp only [hnew, hold, lift_filter, change, ZSet.weight_append, ZSet.weight_neg, weight_filter,
    ← ha r]
  generalize keeps anti (matchCount on r (ZSet.lift b) + matchCount on r Δb) = p'
  generalize keeps anti (matchCount on r (ZSet.lift b)) = p
  cases p <;> cases p' <;> simp <;> omega

/-- The rows of `z` that match a left row with key `k`, by `M`. -/
def keyCount (M : Row → Row → Bool) (k : Row) (z : ZSet) : Int :=
  ZSet.lin (fun y => ind (M k y) 1) z

/-- **One count per key.** When the condition only compares the left row's
key `key x` with the right row (`M`), as an equi-join does, the left row's
count is its key's count. -/
theorem matchCount_by_key {on : Expr} {key : Row → Row} {M : Row → Row → Bool}
    (h : ∀ x y, (on.eval (x ++ y)).isTrue = M (key x) y) (x : Row) (z : ZSet) :
    matchCount on x z = keyCount M (key x) z := by
  simp only [matchCount, keyCount, h]

theorem keyCount_append (M : Row → Row → Bool) (k : Row) (a b : ZSet) :
    keyCount M k (a ++ b) = keyCount M k a + keyCount M k b := ZSet.lin_append _ _ _

end SemiDelta
end Substrait
