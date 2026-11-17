import Sverify.Analysis.Keys
import Sverify.Analysis.Partition
import Sverify.Analysis.AllowedAnalysis

/-!
# The analyses read only the catalog's arities (#1088)

`substrait-check --contract` has the plans and their schemas, never the data:
it analyses a catalog with each table's arity and no rows
(`ContractCheck.tablesCatalog`). `check_proved_sound` applies the contract
theorems to the data's catalog. These lemmas carry the analysis over: on two
catalogs with the same arities, `Rel.facts`, `Rel.aeval` (with
`Rel.ratioPart`), `Rel.keys` and the window keys derived from them
(`Rel.keyedWindows`) agree, and so does `Rel.detPlan`, as `Rel.arity_congr` and `Rel.wf_congr` show for
the arity and well-formedness.
-/

namespace Substrait

variable {c cat : Catalog}

theorem Rel.facts_congr (h : ∀ t, (c t).arity = (cat t).arity) (F : String → List Fact)
    (T : WindowKeys) : ∀ r : Rel, r.facts c F T = r.facts cat F T
  | .read _ | .values _ _ | .aggregate _ _ _ | .unnest _ _ => rfl
  | .filter r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r => by
      simp only [facts, facts_congr h F T r]
  | .project r _ | .window r _ _ _ => by simp only [facts, facts_congr h F T r, arity_congr h r]
  | .semi a _ _ _ => by simp only [facts, facts_congr h F T a]
  | .cross a b | .unionAll a b => by
      simp only [facts, facts_congr h F T a, facts_congr h F T b, arity_congr h a]
  | .join a b ty _ => by
      cases ty <;> simp only [facts, facts_congr h F T a, facts_congr h F T b, arity_congr h a]

variable [Boxes.Ambient]
theorem Rel.aeval_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (T : WindowKeys) (sz : Bool) :
    ∀ r : Rel, r.aeval c A F T sz = r.aeval cat A F T sz ∧
      r.ratioPart c A F T sz = r.ratioPart cat A F T sz
  | .read t => by simp only [aeval, ratioPart, h t, and_self]
  | .values _ _ => by simp only [aeval, ratioPart, and_self]
  | .filter r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .window r _ _ _
  | .unnest r _ | .semi r _ _ _ => by
      simp only [aeval, ratioPart, (aeval_congr h A F T sz r).1, facts_congr h F T r, and_self]
  | .project r _ => by
      simp only [aeval, ratioPart, (aeval_congr h A F T sz r).1, (aeval_congr h A F T sz r).2,
        facts_congr h F T r, and_self]
  | .aggregate r _ _ => by
      simp only [aeval, ratioPart, (aeval_congr h A F T sz r).1, facts_congr h F T r, and_self]
  | .cross a b | .unionAll a b => by
      simp only [aeval, ratioPart, (aeval_congr h A F T sz a).1, (aeval_congr h A F T sz b).1,
        and_self]
  | .join a b ty _ => by
      cases ty <;> simp only [aeval, ratioPart, (aeval_congr h A F T sz a).1,
        (aeval_congr h A F T sz b).1, and_self]

theorem Rel.keys_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : String → List (List Nat)) :
    ∀ r : Rel, r.keys c A F K = r.keys cat A F K
  | .read _ | .values _ _ | .aggregate _ _ _ | .unnest _ _ => rfl
  | .filter r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .semi r _ _ _ => by
      simp only [keys, keys_congr h A F K r]
  | .distinct r | .window r _ _ _ => by simp only [keys, keys_congr h A F K r, arity_congr h r]
  | .project r _ => by
      simp only [keys, keys_congr h A F K r, arity_congr h r, (aeval_congr h A F .none false r).1]
  | .cross a b | .join a b _ _ => by
      simp only [keys, keys_congr h A F K a, keys_congr h A F K b, arity_congr h a]
  | .unionAll a b => by
      simp only [keys, keys_congr h A F K a, keys_congr h A F K b,
        (aeval_congr h A F .none false a).1, (aeval_congr h A F .none false b).1]

theorem Rel.keyedWindows_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : String → List (List Nat)) :
    Rel.keyedWindows c A F K = Rel.keyedWindows cat A F K := by
  funext r part sort
  simp only [keyedWindows, keys_congr h A F K r]

theorem Measure.detIn_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : String → List (List Nat)) (r : Rel) (gs : List Expr) :
    Measure.detIn c A F K r gs = Measure.detIn cat A F K r gs := by
  funext m
  simp only [Measure.detIn, Measure.tiesFixed, Measure.keyedIn, Rel.keys_congr h A F K r,
    (Rel.aeval_congr h A F .none false r).1]

theorem Measure.pickFixed_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (r : Rel) : Measure.pickFixed c A F r = Measure.pickFixed cat A F r := by
  funext m; simp only [Measure.pickFixed, (Rel.aeval_congr h A F .none false r).1]

theorem WinFn.pickFixed_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (r : Rel) : WinFn.pickFixed c A F r = WinFn.pickFixed cat A F r := by
  funext f; cases f <;> simp only [WinFn.pickFixed, Measure.pickFixed_congr h A F r]

theorem Rel.detPlan_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : String → List (List Nat)) :
    ∀ r : Rel, r.detPlan c A F K = r.detPlan cat A F K
  | .read _ | .values _ _ => rfl
  | .fetch (.orderBy r _) _ _ => by
      simp only [detPlan, detPlan_congr h A F K r, fetchTotalAt, keys_congr h A F K r]
  | .fetch (.read _) _ _ | .fetch (.values _ _) _ _ | .fetch (.filter _ _) _ _
  | .fetch (.project _ _) _ _ | .fetch (.emit _ _) _ _ | .fetch (.cross _ _) _ _
  | .fetch (.join _ _ _ _) _ _ | .fetch (.fetch _ _ _) _ _ | .fetch (.unionAll _ _) _ _
  | .fetch (.window _ _ _ _) _ _ | .fetch (.semi _ _ _ _) _ _ | .fetch (.distinct _) _ _
  | .fetch (.aggregate _ _ _) _ _ | .fetch (.unnest _ _) _ _ => rfl
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ | .unnest r _ => by
      simp only [detPlan, detPlan_congr h A F K r]
  | .distinct r => by
      simp only [detPlan, detPlan_congr h A F K r, (aeval_congr h A F .none false r).1]
  | .aggregate r _ _ => by
      simp only [detPlan, detPlan_congr h A F K r, (aeval_congr h A F .none false r).1,
        Measure.detIn_congr h A F K r, Measure.pickFixed_congr h A F r]
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ => by
      simp only [detPlan, detPlan_congr h A F K a, detPlan_congr h A F K b]
  | .window r _ _ _ => by
      simp only [detPlan, windowDetAt, detPlan_congr h A F K r, keys_congr h A F K r,
        arity_congr h r, (aeval_congr h A F .none false r).1, WinFn.pickFixed_congr h A F r]

end Substrait
