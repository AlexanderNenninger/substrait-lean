import Sverify.Analysis.Keys
import Sverify.Analysis.Partition

/-!
# The analyses read only the catalog's arities (#1088)

`substrait-check --contract` has the plans and their schemas, never the data:
it analyses a catalog with each table's arity and no rows
(`ContractCheck.tablesCatalog`). `check_proved_sound` applies the contract
theorems to the data's catalog. These lemmas carry the analysis over: on two
catalogs with the same arities, `Rel.facts`, `Rel.aeval` (with
`Rel.ratioPart`), `Rel.keys` and the window keys derived from them
(`Rel.keyedWindows`) agree, as `Rel.arity_congr` and `Rel.wf_congr` show for
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

end Substrait
