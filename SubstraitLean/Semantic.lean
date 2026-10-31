import SubstraitLean.Keys

/-!
# Semantic rewrites from contracts

Rewrites that hold only on data meeting a contract's preconditions: the
facts and keys that `Rel.aeval` and `Rel.keys` derive from them justify each
one. Engines apply such rewrites only for constraints they enforce, or that
the user asserts unchecked (`RELY`); ours are checked at ingestion or proved
through composition (`docs/optimizations.md` §3).

`Rel.optimize` rewrites bottom-up. At each node it decides from the analyses
of the already rewritten inputs, so one rewrite can enable the next.

* **`DISTINCT` on a key** (#76). If the input has a key, its rows are
  pairwise distinct and `dedup` keeps them all (`dedup_of_nodup`).
* **`GROUP BY` a key, without measures** (#76). Every group has one row, so
  the aggregate is the projection of its grouping expressions.
* **`fn(DISTINCT x)` with `x` a key** (#76). The values are distinct within
  every group, so `DISTINCT` changes nothing: `COUNT(DISTINCT id)` is
  `COUNT(id)`.

`Rel.optimize_sound`: on every catalog meeting the preconditions, the
rewritten plan is well-formed, has the same arity, and gives the same list of
rows. As elsewhere (`Rel.guardFree_sound`, `Rel.shardSplit_sound`), the
checker runs the analyses on the schema-only catalog: they read only arities.
-/

namespace Substrait

theorem dedupN_of_nodup {α : Type} [DecidableEq α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.Nodup → dedupN n l = l
  | _, [], _, _ => by cases ‹Nat› <;> simp [dedupN]
  | 0, _ :: _, h, _ => by simp at h
  | n + 1, x :: xs, h, hnd => by
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hnd
    have hf : xs.filter (· != x) = xs :=
      List.filter_eq_self.2 fun y hy => by simpa using fun h : y = x => hx (h ▸ hy)
    simp only [dedupN, hf]
    rw [dedupN_of_nodup n xs (by simp at h; omega) hxs]

theorem dedup_of_nodup {α : Type} [DecidableEq α] {l : List α} (h : l.Nodup) : dedup l = l :=
  dedupN_of_nodup _ l (Nat.le_refl _) h

/-- Values that a key's columns determine are distinct across the rows. -/
theorem KeyOn.map_pairwise {β : Type} {k : List Nat} {rows : Relation} (h : KeyOn k rows)
    {f : Row → β} (hf : ∀ x y, f x = f y → keyOf k x = keyOf k y) :
    (rows.map f).Pairwise (· ≠ ·) :=
  List.pairwise_map.mpr (h.imp fun hne heq => hne (hf _ _ heq))

/-! ## The rewrites -/

/-- Is `e` a column `c` that is a key by itself (`[c]`, `[c, c]` or `[]`)? -/
def keyCol (ks : List (List Nat)) : Expr → Bool
  | .field c => ks.any (·.all (· == c))
  | _ => false

def Measure.dropDistinct (ks : List (List Nat)) (m : Measure) : Measure :=
  if m.distinct && keyCol ks m.arg then { m with distinct := false } else m

/-- Do the grouping expressions include the columns of a key? -/
def groupsKey (ks : List (List Nat)) (gs : List Expr) : Bool :=
  ks.any (·.all fun c => gs.contains (.field c))

/-- One rewrite at the root, and its name for the report. -/
def Rel.rule (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) : Rel → Option (String × Rel)
  | .distinct r => if (r.keys cat A F K).isEmpty then none else some ("DISTINCT on a key", r)
  | .aggregate r gs ms =>
    let ks := r.keys cat A F K
    if ms.isEmpty && !gs.isEmpty && groupsKey ks gs then
      some ("GROUP BY a key", .emit (.project r gs) ((List.range gs.length).map (r.arity cat + ·)))
    else if ms.any fun m => m.distinct && keyCol ks m.arg then
      some ("DISTINCT aggregate of a key", .aggregate r gs (ms.map (Measure.dropDistinct ks)))
    else none
  | _ => none

/-- Apply `rule` at the root, logging its name. -/
def Rel.step (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (r : Rel) (log : List String) : Rel × List String :=
  match r.rule cat A F K with
  | some (name, s) => (s, log ++ [name])
  | none => (r, log)

/-- Rewrite bottom-up; also return the names of the rewrites applied. -/
def Rel.optimize (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) : Rel → Rel × List String
  | .read t => (.read t, [])
  | .values n rows => (.values n rows, [])
  | .filter r c => step cat A F K (.filter (r.optimize cat A F K).1 c) (r.optimize cat A F K).2
  | .project r es => step cat A F K (.project (r.optimize cat A F K).1 es) (r.optimize cat A F K).2
  | .emit r m => step cat A F K (.emit (r.optimize cat A F K).1 m) (r.optimize cat A F K).2
  | .cross a b => step cat A F K (.cross (a.optimize cat A F K).1 (b.optimize cat A F K).1)
      ((a.optimize cat A F K).2 ++ (b.optimize cat A F K).2)
  | .join a b ty on => step cat A F K (.join (a.optimize cat A F K).1 (b.optimize cat A F K).1 ty on)
      ((a.optimize cat A F K).2 ++ (b.optimize cat A F K).2)
  | .fetch r off cnt => step cat A F K (.fetch (r.optimize cat A F K).1 off cnt) (r.optimize cat A F K).2
  | .unionAll a b => step cat A F K (.unionAll (a.optimize cat A F K).1 (b.optimize cat A F K).1)
      ((a.optimize cat A F K).2 ++ (b.optimize cat A F K).2)
  | .window r part sort fns =>
      step cat A F K (.window (r.optimize cat A F K).1 part sort fns) (r.optimize cat A F K).2
  | .semi a b anti on => step cat A F K (.semi (a.optimize cat A F K).1 (b.optimize cat A F K).1 anti on)
      ((a.optimize cat A F K).2 ++ (b.optimize cat A F K).2)
  | .orderBy r keys => step cat A F K (.orderBy (r.optimize cat A F K).1 keys) (r.optimize cat A F K).2
  | .distinct r => step cat A F K (.distinct (r.optimize cat A F K).1) (r.optimize cat A F K).2
  | .aggregate r gs ms =>
      step cat A F K (.aggregate (r.optimize cat A F K).1 gs ms) (r.optimize cat A F K).2

/-! ## Soundness -/

/-- `s` can replace `r`: well-formed, the same arity, the same rows. -/
structure Same (cat : Catalog) (r s : Rel) : Prop where
  wf : s.WF cat
  arity : s.arity cat = r.arity cat
  eval : s.eval cat = r.eval cat

theorem Same.trans {cat : Catalog} {r s t : Rel} (h : Same cat r s) (h' : Same cat s t) :
    Same cat r t := ⟨h'.wf, h'.arity.trans h.arity, h'.eval.trans h.eval⟩

theorem Measure.kept_sublist (m : Measure) (rows : Relation) : (m.kept rows).Sublist rows := by
  unfold kept; split
  · exact List.Sublist.refl _
  · exact List.filter_sublist

theorem Measure.eval_dropDistinct {ks : List (List Nat)} {rows : Relation}
    (hk : ∀ k ∈ ks, KeyOn k rows) (m : Measure) : (m.dropDistinct ks).eval rows = m.eval rows := by
  unfold dropDistinct
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hd, hc⟩ := h
    unfold keyCol at hc
    split at hc
    · rename_i c heq
      obtain ⟨k, hkm, hkc⟩ := List.any_eq_true.mp hc
      have hp := (hk k hkm).map_pairwise (f := m.arg.eval) fun x y he => by
        simp only [keyOf, List.map_inj_left]
        intro c' hc'
        have := List.all_eq_true.mp hkc c' hc'
        simp only [beq_iff_eq] at this
        subst this
        simpa [heq, Expr.eval] using he
      have hnd : (((m.kept rows).map m.arg.eval).filter (· != .null)).Nodup :=
        ((hp.sublist ((m.kept_sublist rows).map _)).filter _)
      simp only [Measure.eval, inputs, hd, ↓reduceIte, dedup_of_nodup hnd]
      rfl
    · simp at hc
  · rfl

theorem Measure.refsLt_dropDistinct {ks : List (List Nat)} {n : Nat} {m : Measure}
    (h : m.refsLt n) : (m.dropDistinct ks).refsLt n := by
  unfold dropDistinct; split <;> exact h

theorem aggregateEval_congr_ms {gs : List Expr} {ms ms' : List Measure} {rows : Relation}
    (h : ∀ grp, grp.Sublist rows → ms'.map (·.eval grp) = ms.map (·.eval grp)) :
    aggregateEval gs ms' rows = aggregateEval gs ms rows := by
  unfold aggregateEval
  split
  · rw [h rows (List.Sublist.refl _)]
  · exact List.map_congr_left fun k _ => by rw [h (groupRows gs rows k) List.filter_sublist]

section
variable {cat : Catalog} (hcat : cat.WF) {A : String → List AVal} {F : String → List Fact}
  (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
  (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
  (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows)
include hcat hA hF hK

theorem Rel.rule_sound {r s : Rel} {name : String} (hwf : r.WF cat)
    (h : r.rule cat A F K = some (name, s)) : Same cat r s := by
  have keys := fun {r : Rel} (hr : r.WF cat) => keys_sound hcat hA hF hK hr
  match r, hwf, h with
  | .distinct r, hwf, h =>
    simp only [rule] at h
    split at h
    · simp at h
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ (by simpa using hne)
      exact ⟨hwf, rfl, by simp only [eval, dedup_of_nodup (keys (r := r) hwf k hk).nodup]⟩
  | .aggregate r gs ms, hwf, h =>
    simp only [rule] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        groupsKey, List.any_eq_true, List.all_eq_true, List.contains_iff_mem] at hc
      obtain ⟨⟨rfl, hgs⟩, k, hk, hkg⟩ := hc
      have hlen := eval_arity hcat hwf.1
      refine ⟨⟨⟨hwf.1, hwf.2.1⟩, by simp [arity]⟩, by simp [arity], ?_⟩
      -- The groups are distinct, so each has one row.
      have hp := (keys hwf.1 k hk).map_pairwise (f := groupKey gs) fun x y he => by
        simp only [keyOf, List.map_inj_left]
        intro c hc
        simpa [Expr.eval] using List.map_inj_left.mp he _ (hkg c hc)
      simp only [eval, aggregateEval, List.isEmpty_iff, hgs, ↓reduceIte, dedup_of_nodup hp,
        List.map_map]
      refine List.map_congr_left fun row hrow => ?_
      have h1 : keyOf ((List.range gs.length).map (r.arity cat + ·)) (row ++ groupKey gs row) =
          groupKey gs row := by
        rw [← hlen row hrow, keyOf_shift, keyOf_range (by simp [groupKey])]
      simpa [keyOf, List.map_map, groupKey] using h1
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨⟨hwf.1, hwf.2.1, ?_⟩, by simp [arity], ?_⟩
        · simp only [List.mem_map]
          rintro _ ⟨m, hm, rfl⟩
          exact Measure.refsLt_dropDistinct (hwf.2.2 m hm)
        · simp only [eval]
          refine aggregateEval_congr_ms fun grp hg => ?_
          rw [List.map_map]
          exact List.map_congr_left fun m _ =>
            Measure.eval_dropDistinct (fun k hk => (keys hwf.1 k hk).sublist hg) m
      · simp at h

theorem Rel.step_sound {r : Rel} {log : List String} (hwf : r.WF cat) :
    Same cat r (r.step cat A F K log).1 := by
  unfold step
  split
  · exact rule_sound hcat hA hF hK hwf ‹_›
  · exact ⟨hwf, rfl, rfl⟩

/-- **Soundness of the rewrites**: on data meeting the preconditions, the
rewritten plan gives the same rows. -/
theorem Rel.optimize_sound : ∀ {r : Rel}, r.WF cat → Same cat r (r.optimize cat A F K).1
  | .read _, hwf | .values _ _, hwf => ⟨hwf, rfl, rfl⟩
  | .filter r c, hwf => by
    have ih := optimize_sound hwf.1
    refine Same.trans ?_ (step_sound hcat hA hF hK ?_)
    · exact ⟨⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩, ih.arity, by simp [eval, ih.eval]⟩
    · exact ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
  | .project r es, hwf => by
    have ih := optimize_sound hwf.1
    have hw : (Rel.project (r.optimize cat A F K).1 es).WF cat := ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
    exact Same.trans ⟨hw, by simp [arity, ih.arity], by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hw)
  | .emit r m, hwf => by
    have ih := optimize_sound hwf.1
    have hw : (Rel.emit (r.optimize cat A F K).1 m).WF cat := ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
    exact Same.trans ⟨hw, rfl, by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hw)
  | .cross a b, hwf => by
    have iha := optimize_sound hwf.1
    have ihb := optimize_sound hwf.2
    have hw : (Rel.cross (a.optimize cat A F K).1 (b.optimize cat A F K).1).WF cat := ⟨iha.wf, ihb.wf⟩
    exact Same.trans ⟨hw, by simp [arity, iha.arity, ihb.arity], by simp [eval, iha.eval, ihb.eval]⟩
      (step_sound hcat hA hF hK hw)
  | .join a b ty on, hwf => by
    have iha := optimize_sound hwf.1
    have ihb := optimize_sound hwf.2.1
    have hw : (Rel.join (a.optimize cat A F K).1 (b.optimize cat A F K).1 ty on).WF cat :=
      ⟨iha.wf, ihb.wf, by rw [iha.arity, ihb.arity]; exact hwf.2.2⟩
    refine Same.trans ⟨hw, by simp [arity, iha.arity, ihb.arity], ?_⟩ (step_sound hcat hA hF hK hw)
    cases ty <;> simp [eval, iha.eval, ihb.eval, ihb.arity]
  | .fetch r off cnt, hwf => by
    have ih := optimize_sound (r := r) hwf
    have hw : (Rel.fetch (r.optimize cat A F K).1 off cnt).WF cat := ih.wf
    exact Same.trans ⟨hw, by simp [arity, ih.arity], by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hw)
  | .unionAll a b, hwf => by
    have iha := optimize_sound hwf.1
    have ihb := optimize_sound hwf.2.1
    have hw : (Rel.unionAll (a.optimize cat A F K).1 (b.optimize cat A F K).1).WF cat :=
      ⟨iha.wf, ihb.wf, by rw [iha.arity, ihb.arity]; exact hwf.2.2⟩
    exact Same.trans ⟨hw, by simp [arity, iha.arity], by simp [eval, iha.eval, ihb.eval]⟩
      (step_sound hcat hA hF hK hw)
  | .window r part sort fns, hwf => by
    have ih := optimize_sound hwf.1
    have hw : (Rel.window (r.optimize cat A F K).1 part sort fns).WF cat :=
      ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
    exact Same.trans ⟨hw, by simp [arity, ih.arity], by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hw)
  | .semi a b anti on, hwf => by
    have iha := optimize_sound hwf.1
    have ihb := optimize_sound hwf.2.1
    have hw : (Rel.semi (a.optimize cat A F K).1 (b.optimize cat A F K).1 anti on).WF cat :=
      ⟨iha.wf, ihb.wf, by rw [iha.arity, ihb.arity]; exact hwf.2.2⟩
    exact Same.trans ⟨hw, by simp [arity, iha.arity], by simp [eval, iha.eval, ihb.eval]⟩
      (step_sound hcat hA hF hK hw)
  | .orderBy r keys, hwf => by
    have ih := optimize_sound hwf.1
    have hw : (Rel.orderBy (r.optimize cat A F K).1 keys).WF cat := ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
    exact Same.trans ⟨hw, by simp [arity, ih.arity], by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hw)
  | .distinct r, hwf => by
    have ih := optimize_sound (r := r) hwf
    have hw : (Rel.distinct (r.optimize cat A F K).1).WF cat := ih.wf
    exact Same.trans ⟨hw, by simp [arity, ih.arity], by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hw)
  | .aggregate r gs ms, hwf => by
    have ih := optimize_sound hwf.1
    have hw : (Rel.aggregate (r.optimize cat A F K).1 gs ms).WF cat :=
      ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
    exact Same.trans ⟨hw, rfl, by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hw)

end

end Substrait
