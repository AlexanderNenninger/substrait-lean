import SubstraitLean.Rel

/-!
# Executable well-formedness checking

`Rel.WF` is a `Prop`; `Rel.checkWF` computes it. `checkWF_iff` proves they
agree, so a `true` from the checker licenses every theorem that assumes
`Rel.WF` (type soundness and the pushdown rewrites).
-/

namespace Substrait

def Rel.checkWF (cat : Catalog) : Rel → Bool
  | .read _ => true
  | .values n rows => rows.all (·.length == n)
  | .filter r c => r.checkWF cat && c.refsLtB (r.arity cat)
  | .project r es => r.checkWF cat && es.all (·.refsLtB (r.arity cat))
  | .emit r m => r.checkWF cat && m.all (· < r.arity cat)
  | .cross a b => a.checkWF cat && b.checkWF cat
  | .join a b _ on =>
      a.checkWF cat && b.checkWF cat && on.refsLtB (a.arity cat + b.arity cat)
  | .fetch r _ _ => r.checkWF cat
  | .unionAll a b => a.checkWF cat && b.checkWF cat && a.arity cat == b.arity cat
  | .window r part sort fns =>
      r.checkWF cat && part.all (· < r.arity cat) && sort.all (·.col < r.arity cat) &&
        fns.all (·.refsLt (r.arity cat))
  | .semi a b _ on =>
      a.checkWF cat && b.checkWF cat && on.refsLtB (a.arity cat + b.arity cat)
  | .orderBy r keys => r.checkWF cat && keys.all (·.col < r.arity cat)
  | .distinct r => r.checkWF cat
  | .aggregate r gs ms =>
      r.checkWF cat && gs.all (·.refsLtB (r.arity cat)) &&
        ms.all fun m => m.arg.refsLtB (r.arity cat) && m.filter.all (·.refsLtB (r.arity cat))
  | .unnest r c => r.checkWF cat && c < r.arity cat

theorem Rel.checkWF_iff {cat : Catalog} {r : Rel} : r.checkWF cat = true ↔ r.WF cat := by
  induction r <;>
    simp_all [checkWF, WF, Expr.refsLtB_iff, Measure.refsLt, Option.all_eq_true, and_assoc]

instance (cat : Catalog) (r : Rel) : Decidable (r.WF cat) :=
  decidable_of_iff _ Rel.checkWF_iff

end Substrait
