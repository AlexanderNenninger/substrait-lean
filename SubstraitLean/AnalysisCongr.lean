import Sverify.Analysis.Keys
import Sverify.Analysis.Partition
import Sverify.Analysis.AllowedAnalysis
import Sverify.Analysis.Rows
import SubstraitLean.Semantic

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

omit [Boxes.Ambient] in
theorem Rel.ranges_congr (h : ∀ t, (c t).arity = (cat t).arity) (K : TableCond) :
    ∀ r : Rel, r.ranges c K = r.ranges cat K
  | .read _ | .values _ _ | .cross _ _ | .join _ _ _ _ | .fetch _ _ _ | .unionAll _ _
  | .window _ _ _ _ | .semi _ _ _ _ | .distinct _ | .aggregate _ _ _ | .unnest _ _ => rfl
  | .filter r _ | .orderBy r _ | .emit r _ => by simp only [Rel.ranges, ranges_congr h K r]
  | .project r _ => by simp only [Rel.ranges, ranges_congr h K r, arity_congr h r]

theorem Rel.keys_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) :
    ∀ r : Rel, r.keys c A F K = r.keys cat A F K
  | .read _ | .values _ _ | .aggregate _ _ _ | .unnest _ _ => rfl
  | .filter r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .semi r _ _ _ => by
      simp only [keys, keys_congr h A F K r]
  | .distinct r | .window r _ _ _ => by simp only [keys, keys_congr h A F K r, arity_congr h r]
  | .project r _ => by
      simp only [keys, keys_congr h A F K r, arity_congr h r, (aeval_congr h A F .none false r).1]
  | .cross a b | .join a b _ _ => by
      simp only [keys, keys_congr h A F K a, keys_congr h A F K b, arity_congr h a,
        ranges_congr h K b]
  | .unionAll a b => by
      simp only [keys, keys_congr h A F K a, keys_congr h A F K b,
        (aeval_congr h A F .none false a).1, (aeval_congr h A F .none false b).1]

theorem Rel.keyedWindows_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) :
    Rel.keyedWindows c A F K = Rel.keyedWindows cat A F K := by
  funext r part sort
  simp only [keyedWindows, keys_congr h A F K r]

theorem Measure.detIn_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) (r : Rel) (gs : List Expr) :
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

theorem Rel.seqTotal_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) :
    ∀ r : Rel, r.seqTotal c A F K = r.seqTotal cat A F K
  | .filter r _ | .project r _ | .emit r _ => by simp only [seqTotal, seqTotal_congr h A F K r]
  | .orderBy r _ | .fetch (.orderBy r _) _ _ => by
      simp only [seqTotal, fetchTotalAt, keys_congr h A F K r]
  | .read _ | .values _ _ | .cross _ _ | .join _ _ _ _ | .unionAll _ _ | .window _ _ _ _
  | .semi _ _ _ _ | .distinct _ | .aggregate _ _ _ | .unnest _ _ | .fetch (.read _) _ _
  | .fetch (.values _ _) _ _ | .fetch (.filter _ _) _ _ | .fetch (.project _ _) _ _
  | .fetch (.emit _ _) _ _ | .fetch (.cross _ _) _ _ | .fetch (.join _ _ _ _) _ _
  | .fetch (.fetch _ _ _) _ _ | .fetch (.unionAll _ _) _ _ | .fetch (.window _ _ _ _) _ _
  | .fetch (.semi _ _ _ _) _ _ | .fetch (.distinct _) _ _ | .fetch (.aggregate _ _ _) _ _
  | .fetch (.unnest _ _) _ _ => rfl

theorem Rel.detPlan_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) :
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

theorem Rel.detClass_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) :
    ∀ r : Rel, r.detClass c A F K = r.detClass cat A F K
  | .read _ | .values _ _ => rfl
  | .filter r _ | .project r _ => by
      simp only [detClass, detClass_congr h A F K r, detPlan_congr h A F K r]
  | .emit r _ | .orderBy r _ | .distinct r => by simp only [detClass, detClass_congr h A F K r]
  | .unionAll a b => by simp only [detClass, detClass_congr h A F K a, detClass_congr h A F K b]
  | .window r _ _ _ => by
      simp only [detClass, windowDetAt, detPlan_congr h A F K r, keys_congr h A F K r,
        arity_congr h r, (aeval_congr h A F .none false r).1]
  | .aggregate r _ _ => by
      simp only [detClass, detPlan_congr h A F K r, Measure.detIn_congr h A F K r]
  | .fetch r o n => by simp only [detClass, detPlan_congr h A F K (.fetch r o n)]
  | .cross a b => by simp only [detClass, detPlan_congr h A F K (.cross a b)]
  | .join a b t on => by simp only [detClass, detPlan_congr h A F K (.join a b t on)]
  | .semi a b t on => by simp only [detClass, detPlan_congr h A F K (.semi a b t on)]
  | .unnest r i => by simp only [detClass, detPlan_congr h A F K (.unnest r i)]

/-! ### The issues (#1484, A4)

`Rel.mayIssues` and the capped issues the report lists (`Rel.issuesCapped`:
reads and joins capped, `SUM`s bounded per key) read the catalog's arities
alone too. -/

theorem Rel.keyedJoin_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) (a b : Rel) (on : Expr) :
    Rel.keyedJoin c A F K a b on = Rel.keyedJoin cat A F K a b on := by
  simp only [keyedJoin, keys_congr h A F K b, ranges_congr h K b, arity_congr h a]

theorem Rel.perKey_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) (P : String → List (List Nat × Nat)) :
    ∀ r : Rel, r.perKey c A F K P = r.perKey cat A F K P
  | .read _ | .values _ _ | .cross _ _ | .window _ _ _ _ | .aggregate _ _ _ | .unnest _ _ => rfl
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .semi r _ _ _ | .emit r _ => by
      simp only [perKey, perKey_congr h A F K P r]
  | .project r _ => by simp only [perKey, perKey_congr h A F K P r, arity_congr h r]
  | .unionAll a b => by simp only [perKey, perKey_congr h A F K P a, perKey_congr h A F K P b]
  | .join a b _ on => by
      simp only [perKey, keyedJoin_congr h A F K a b on, perKey_congr h A F K P a,
        keys_congr h A F K a, arity_congr h a]

theorem Rel.groupRows_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) (P : String → List (List Nat × Nat))
    (r : Rel) (gs : List Expr) : r.groupRows c A F K P gs = r.groupRows cat A F K P gs := by
  simp only [groupRows, perKey_congr h A F K P r, keys_congr h A F K r]

theorem Rel.capJoins_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) :
    ∀ r : Rel, r.capJoins c A F K = r.capJoins cat A F K
  | .read _ | .values _ _ => rfl
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _
  | .distinct r | .aggregate r _ _ | .unnest r _ => by simp only [capJoins, capJoins_congr h A F K r]
  | .cross a b | .unionAll a b | .semi a b _ _ => by
      simp only [capJoins, capJoins_congr h A F K a, capJoins_congr h A F K b]
  | .join a b _ _ => by
      simp only [capJoins, capJoins_congr h A F K a, capJoins_congr h A F K b, keyedJoin_congr h]

theorem Rel.sumsPer_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (T : WindowKeys) (K : TableCond)
    (P : String → List (List Nat × Nat)) :
    ∀ r : Rel, r.sumsPer c A F T K P = r.sumsPer cat A F T K P
  | .read _ | .values _ _ => rfl
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .unnest r _ | .window r _ _ _ => by simp only [sumsPer, sumsPer_congr h A F T K P r]
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ => by
      simp only [sumsPer, sumsPer_congr h A F T K P a, sumsPer_congr h A F T K P b]
  | .aggregate r _ _ => by
      simp only [sumsPer, sumsPer_congr h A F T K P r, (aeval_congr h A F T true r).1,
        facts_congr h F T r, groupRows_congr h A F K P r]

theorem Rel.viewEnv_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (T : WindowKeys) :
    ∀ (cols : List Nat) (r : Rel), r.viewEnv c A F T cols = r.viewEnv cat A F T cols
  | cols, .cross a b | cols, .join a b _ _ => by
      simp only [viewEnv, arity_congr h, viewEnv_congr h A F T _ a, viewEnv_congr h A F T _ b]
  | _, .read _ | _, .values _ _ | _, .filter _ _ | _, .project _ _ | _, .emit _ _
  | _, .fetch _ _ _ | _, .unionAll _ _ | _, .window _ _ _ _ | _, .semi _ _ _ _
  | _, .orderBy _ _ | _, .distinct _ | _, .aggregate _ _ _ | _, .unnest _ _ => by
      simp only [viewEnv, (aeval_congr h A F T true _).1]

omit [Boxes.Ambient] in
theorem Rel.viewFacts_congr (h : ∀ t, (c t).arity = (cat t).arity) (F : String → List Fact)
    (T : WindowKeys) : ∀ (cols : List Nat) (r : Rel), r.viewFacts c F T cols = r.viewFacts cat F T cols
  | cols, .cross a b | cols, .join a b _ _ => by
      simp only [viewFacts, arity_congr h, viewFacts_congr h F T _ a, viewFacts_congr h F T _ b]
  | _, .read _ | _, .values _ _ | _, .filter _ _ | _, .project _ _ | _, .emit _ _
  | _, .fetch _ _ _ | _, .unionAll _ _ | _, .window _ _ _ _ | _, .semi _ _ _ _
  | _, .orderBy _ _ | _, .distinct _ | _, .aggregate _ _ _ | _, .unnest _ _ => by
      simp only [viewFacts, facts_congr h F T]

theorem Rel.viewIssues_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (T : WindowKeys) (r : Rel) :
    r.viewIssues c A F T = r.viewIssues cat A F T := by
  funext e; simp only [viewIssues, viewEnv_congr h A F T, viewFacts_congr h F T]

theorem Rel.mayIssues_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (T : WindowKeys) :
    ∀ (u : Bool) (r : Rel), r.mayIssues c A F T u = r.mayIssues cat A F T u
  | _, .read _ | _, .values _ _ => rfl
  | _, .filter r _ => by
      simp only [mayIssues, mayIssues_congr h A F T true r, (aeval_congr h A F T true r.loose).1,
        facts_congr h F T r.loose, viewIssues_congr h A F T]
  | u, .project r _ => by
      cases u <;> simp only [mayIssues, mayIssues_congr h A F T _ r, (aeval_congr h A F T true _).1,
        facts_congr h F T, viewIssues_congr h A F T, Bool.false_eq_true, ↓reduceIte]
  | u, .emit r _ | u, .fetch r _ _ | u, .orderBy r _ | u, .distinct r | u, .unnest r _ => by
      simp only [mayIssues, mayIssues_congr h A F T u r]
  | u, .window r _ _ _ => by
      simp only [mayIssues, mayIssues_congr h A F T u r, (aeval_congr h A F T true r).1,
        facts_congr h F T r]
  | u, .cross a b | u, .unionAll a b => by
      simp only [mayIssues, mayIssues_congr h A F T u a, mayIssues_congr h A F T u b]
  | _, .join a b _ _ | _, .semi a b _ _ => by
      simp only [mayIssues, mayIssues_congr h A F T true a, mayIssues_congr h A F T true b,
        (aeval_congr h A F T true (Rel.cross a.loose b.loose)).1, facts_congr h F T,
        viewIssues_congr h A F T]
  | u, .aggregate r _ _ => by
      cases u <;> simp only [mayIssues, mayIssues_congr h A F T _ r, (aeval_congr h A F T true _).1,
        facts_congr h F T, viewIssues_congr h A F T, Bool.false_eq_true, ↓reduceIte]

theorem Rel.issuesCapped_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (T : WindowKeys) (K : TableCond)
    (caps : String → Option Nat) (P : String → List (List Nat × Nat)) (r : Rel) :
    r.issuesCapped c A F T K caps P = r.issuesCapped cat A F T K caps P := by
  unfold issuesCapped capped
  rw [capJoins_congr h, sumsPer_congr h, mayIssues_congr h, mayIssues_congr h]

/-! ### The rewrites (#1484, A4)

`Rel.optimize`, the rewriting the report writes as `optimized`, reads the
catalog's arities alone too. -/

omit [Boxes.Ambient] in
theorem Rel.origin_congr (h : ∀ t, (c t).arity = (cat t).arity) :
    ∀ (r : Rel) (i : Nat), r.origin c i = r.origin cat i
  | .read _, _ | .values _ _, _ | .unnest _ _, _ => rfl
  | .filter r _, i | .fetch r _ _, i | .orderBy r _, i | .distinct r, i | .semi r _ _ _, i =>
      origin_congr h r i
  | .project r _, i | .window r _ _ _, i => by
      simp only [origin, arity_congr h r, origin_congr h r]
  | .emit r _, i => by
      have : r.origin c = r.origin cat := funext (origin_congr h r)
      simp only [origin, this]
  | .cross a b, i | .join a b _ _, i => by
      simp only [origin, arity_congr h a, origin_congr h a, origin_congr h b]
  | .unionAll a b, i => by simp only [origin, origin_congr h a, origin_congr h b]
  | .aggregate r _ _, i => by simp only [origin, origin_congr h r]

omit [Boxes.Ambient] in
theorem Rel.cover_congr (h : ∀ t, (c t).arity = (cat t).arity) :
    ∀ (r : Rel) (j : Nat), r.cover c j = r.cover cat j
  | .read _, _ | .values _ _, _ | .unnest _ _, _ | .filter _ _, _ | .fetch _ _ _, _
  | .semi _ _ _ _, _ | .window _ _ _ _, _ | .cross _ _, _ | .join _ _ _ _, _ | .unionAll _ _, _
  | .aggregate _ _ _, _ => rfl
  | .orderBy r _, j | .distinct r, j => cover_congr h r j
  | .project r _, j => by simp only [cover, arity_congr h r, cover_congr h r]
  | .emit r _, j => by
      have : r.cover c = r.cover cat := funext (cover_congr h r)
      simp only [cover, this]

theorem Rel.fkMatch_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) (R : ForeignKeys) (a b : Rel)
    (on : Expr) : Rel.fkMatch c A F K R a b on = Rel.fkMatch cat A F K R a b on := by
  simp only [fkMatch, arity_congr h a, origin_congr h a, cover_congr h b,
    keyedWindows_congr h, (aeval_congr h A F _ false a).1]

theorem Rel.joinElim_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) (R : ForeignKeys) :
    ∀ r : Rel, r.joinElim c A F K R = r.joinElim cat A F K R
  | .join a b _ on => by
      simp only [joinElim, keys_congr h A F K b, arity_congr h a, arity_congr h b,
        fkMatch_congr h A F K R a b on]
  | .read _ | .values _ _ | .filter _ _ | .project _ _ | .emit _ _ | .cross _ _ | .fetch _ _ _
  | .unionAll _ _ | .window _ _ _ _ | .semi _ _ _ _ | .orderBy _ _ | .distinct _
  | .aggregate _ _ _ | .unnest _ _ => rfl

theorem Rel.condVal_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) (r : Rel) (e : Expr) :
    r.condVal c A F K e = r.condVal cat A F K e := by
  simp only [condVal, keyedWindows_congr h, (aeval_congr h A F _ false r).1, facts_congr h F]

omit [Boxes.Ambient] in
theorem Rel.fds_congr (h : ∀ t, (c t).arity = (cat t).arity) (K : TableCond) :
    ∀ r : Rel, r.fds c K = r.fds cat K
  | .read t => by simp only [fds, h t]
  | .aggregate _ _ _ | .unnest _ _ | .values _ _ | .unionAll _ _ => rfl
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .semi r _ _ _ | .emit r _ => by
      simp only [fds, fds_congr h K r]
  | .project r _ | .window r _ _ _ => by simp only [fds, fds_congr h K r, arity_congr h r]
  | .cross a b => by simp only [fds, fds_congr h K a, fds_congr h K b, arity_congr h a]
  | .join a b ty _ => by
      cases ty <;> simp only [fds, fds_congr h K a, fds_congr h K b, arity_congr h a]

theorem Rel.fdAgg_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) (r : Rel) (gs : List Expr)
    (ms : List Measure) : Rel.fdAgg c A F K r gs ms = Rel.fdAgg cat A F K r gs ms := by
  simp only [fdAgg, fds_congr h K r, keys_congr h A F K r, arity_congr h r,
    (aeval_congr h A F .none false r).1]

theorem Rel.eagerAgg_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) (r : Rel) (gs : List Expr)
    (ms : List Measure) : Rel.eagerAgg c A F K r gs ms = Rel.eagerAgg cat A F K r gs ms := by
  unfold eagerAgg
  split
  · rename_i a b on
    simp only [arity_congr h a, arity_congr h b, keys_congr h A F K b,
      (aeval_congr h A F .none false a).1]
  · rfl

theorem Rel.aeval_congr₁ (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (T : WindowKeys) (sz : Bool) (r : Rel) :
    r.aeval c A F T sz = r.aeval cat A F T sz :=
  (aeval_congr h A F T sz r).1

theorem Rel.rule_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) (R : ForeignKeys) (r : Rel) :
    r.rule c A F K R = r.rule cat A F K R := by
  cases r <;> simp only [rule, condVal_congr h A F K, arity_congr h, keyedWindows_congr h,
    aeval_congr₁ h, keys_congr h A F K, joinElim_congr h A F K R, fdAgg_congr h A F K,
    eagerAgg_congr h A F K, fkMatch_congr h A F K R]

theorem Rel.stepN_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) (R : ForeignKeys) (use : Rule → Bool) :
    ∀ (fuel : Nat) (r : Rel) (log : List Rule),
      r.stepN c A F K R use fuel log = r.stepN cat A F K R use fuel log
  | 0, _, _ => rfl
  | fuel + 1, r, log => by
      simp only [stepN, rule_congr h A F K R r]
      split <;> try rfl
      split <;> try rfl
      exact stepN_congr h A F K R use fuel _ _

theorem Rel.optimize_congr (h : ∀ t, (c t).arity = (cat t).arity) (A : String → List AVal)
    (F : String → List Fact) (K : TableCond) (R : ForeignKeys) (use : Rule → Bool) :
    ∀ r : Rel, r.optimize c A F K R use = r.optimize cat A F K R use
  | .read _ | .values _ _ | .unnest _ _ => rfl
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _
  | .distinct r | .aggregate r _ _ => by
      simp only [optimize, step, optimize_congr h A F K R use r, stepN_congr h A F K R use]
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ => by
      simp only [optimize, step, optimize_congr h A F K R use a, optimize_congr h A F K R use b,
        stepN_congr h A F K R use]

end Substrait
