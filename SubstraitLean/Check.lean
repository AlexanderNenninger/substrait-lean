import SubstraitLean.Rel

/-!
# Executable well-formedness checking

`Rel.WF` is a `Prop`; `Rel.checkWF` computes it. `checkWF_iff` proves they
agree, so a `true` from the checker licenses every theorem that assumes
`Rel.WF` (type soundness and the pushdown rewrites).
-/

namespace Substrait

def Expr.refsLtb (n : Nat) : Expr → Bool
  | .lit _ => true
  | .field i => decide (i < n)
  | .un _ a => a.refsLtb n
  | .bin _ a b => a.refsLtb n && b.refsLtb n
  | .ifThen c t e => c.refsLtb n && t.refsLtb n && e.refsLtb n
  | .hof _ l _ => l.refsLtb n

theorem Expr.refsLtb_iff {n : Nat} {e : Expr} : e.refsLtb n = true ↔ e.refsLt n := by
  induction e <;> simp_all [refsLtb, refsLt, and_assoc]

def Rel.checkWF (cat : Catalog) : Rel → Bool
  | .read _ => true
  | .values n rows => rows.all (·.length == n)
  | .filter r c => r.checkWF cat && c.refsLtb (r.arity cat)
  | .project r es => r.checkWF cat && es.all (·.refsLtb (r.arity cat))
  | .emit r m => r.checkWF cat && m.all (· < r.arity cat)
  | .cross a b => a.checkWF cat && b.checkWF cat
  | .join a b _ on =>
      a.checkWF cat && b.checkWF cat && on.refsLtb (a.arity cat + b.arity cat)
  | .fetch r _ _ => r.checkWF cat
  | .unionAll a b => a.checkWF cat && b.checkWF cat && a.arity cat == b.arity cat
  | .window r part sort fns =>
      r.checkWF cat && part.all (· < r.arity cat) && sort.all (·.col < r.arity cat) &&
        fns.all (·.refsLt (r.arity cat))
  | .semi a b _ on =>
      a.checkWF cat && b.checkWF cat && on.refsLtb (a.arity cat + b.arity cat)
  | .orderBy r keys => r.checkWF cat && keys.all (·.col < r.arity cat)
  | .distinct r => r.checkWF cat
  | .aggregate r gs ms =>
      r.checkWF cat && gs.all (·.refsLtb (r.arity cat)) &&
        ms.all fun m => m.arg.refsLtb (r.arity cat) && m.filter.all (·.refsLtb (r.arity cat))
  | .unnest r c => r.checkWF cat && c < r.arity cat

theorem Rel.checkWF_iff {cat : Catalog} {r : Rel} : r.checkWF cat = true ↔ r.WF cat := by
  induction r <;>
    simp_all [checkWF, WF, Expr.refsLtb_iff, Measure.refsLt, Option.all_eq_true, and_assoc]

instance (cat : Catalog) (r : Rel) : Decidable (r.WF cat) :=
  decidable_of_iff _ Rel.checkWF_iff

end Substrait
