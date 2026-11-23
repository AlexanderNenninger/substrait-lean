import Sverify.Analysis.AsofSite
import Sverify.Core.AllowedNear

/-!
# A left as-of join keeps one row per left row (#1992, ruling 194 D5)

`sv.asof_join(how="left")` (`python/src/sverify/asof.py`) numbers the left
rows, joins each with the right rows at or before it (a LEFT join), ranks
each left row's matches with `ROW_NUMBER` partitioned by that number, and
keeps the first. `AsofSite.leftExact` recognises that shape on a site
(`Rel.asofSite`); `AsofSite.left_exactly_one` proves that every result the
reference allows has as many rows as the numbered left input it was built
from: no left row is dropped and none is repeated.

The proof rests on three facts, each about one operator:

* `windowRows_rowNumber_count`: `ROW_NUMBER` gives 1 to one row of each
  partition, so the rows with 1 are as many as the partitions;
* `keyOf_leftJoin_iff`: a LEFT join gives every left row at least one row,
  and each row it gives starts with its left row, so the join's values of a
  left column are the left input's;
* `windowRows_rowNumber_whole`: `ROW_NUMBER` over the whole input numbers its
  rows `1, 2, …`, so the left row numbers are a key of the left input.

At most one row per left row was proved before, as a key of the output
(`Rel.keys`, #2220); this module adds that at least one is kept. Nothing in the
checker reads the count: it is a guarantee `asof.py` states, with this
theorem behind it.
-/

namespace Substrait

variable [Boxes.Ambient]

/-! ## Lists -/

omit [Boxes.Ambient] in
theorem dedup_length_append_one {α : Type} [DecidableEq α] (l : List α) (a : α) :
    (dedup (l ++ [a])).length = (dedup l).length + if a ∈ l then 0 else 1 := by
  by_cases ha : a ∈ l
  · simp only [ha, ite_true, Nat.add_zero]
    refine (dedup_perm_of_mem fun y => ?_).length_eq
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | rfl) <;> assumption
    · exact Or.inl
  · simp only [ha, ite_false]
    have hnd : (dedup l ++ [a]).Nodup := by
      rw [List.nodup_append]
      exact ⟨nodup_dedup l, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun x hx y hy => by
        rw [List.mem_singleton] at hy; subst hy; rintro rfl; exact ha (mem_dedup.mp hx)⟩
    have hp := dedup_perm_of_mem (l := l ++ [a]) (l' := dedup l ++ [a]) fun y => by
      simp [mem_dedup]
    rw [dedup_of_nodup hnd] at hp
    simp [hp.length_eq]

/-! ## `ROW_NUMBER` -/

omit [Boxes.Ambient] in
/-- Rows in one partition agree on its columns' `keyOf`. -/
theorem samePart_eq_keyOf (part : List Nat) (x y : Row) :
    samePart part x y = decide (keyOf part x = keyOf part y) := rfl

/-- **`ROW_NUMBER` gives 1 to one row of each partition**: the rows it gives 1
are as many as the partitions, counted after the rows `pre` before. -/
theorem windowRows_rowNumber_count (part : List Nat) :
    ∀ (pre s : List Row),
      ((windowRows part [.rowNumber] pre s).filter fun r => r.getLast? == some (.int 1)).length +
        (dedup (pre.map (keyOf part))).length = (dedup ((pre ++ s).map (keyOf part))).length
  | pre, [] => by simp [windowRows]
  | pre, x :: s => by
    have ih := windowRows_rowNumber_count part (pre ++ [x]) s
    have hd := dedup_length_append_one (pre.map (keyOf part)) (keyOf part x)
    simp only [List.map_append, List.map_cons, List.map_nil] at hd ih
    simp only [List.append_assoc, List.singleton_append] at ih
    simp only [windowRows, List.map_cons, List.map_nil, List.filter_cons, List.getLast?_append,
      List.getLast?_singleton, Option.some_or, WinFn.value, WinFn.valueIn, List.map_append]
    have hiff : (List.filter (samePart part x) pre).length = 0 ↔ keyOf part x ∉ pre.map (keyOf part) := by
      simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, samePart_eq_keyOf,
        decide_eq_true_eq, List.mem_map, not_exists, not_and]
      exact ⟨fun h y hy he => h y hy he.symm, fun h y hy he => h y hy he.symm⟩
    by_cases hk : keyOf part x ∈ pre.map (keyOf part)
    · have h0 : (List.filter (samePart part x) pre).length ≠ 0 := fun h => hiff.mp h hk
      simp only [hk, ite_true, Nat.add_zero] at hd
      have hne : (some (Value.int (↑(List.filter (samePart part x) pre).length + 1)) ==
          some (Value.int 1)) = false := by
        rw [beq_eq_false_iff_ne]; simp only [ne_eq, Option.some.injEq, Value.int.injEq]; omega
      rw [hne]
      simp only [Bool.false_eq_true, ite_false]
      omega
    · have h0 := hiff.mpr hk
      simp only [hk, ite_false] at hd
      simp only [h0, show ((0 : Nat) : Int) + 1 = 1 from rfl, beq_self_eq_true, ite_true,
        List.length_cons]
      omega

/-- **`ROW_NUMBER` over the whole input numbers its rows**: each row gets a
number after `pre`'s rows, a different one from every later row's. -/
theorem windowRows_rowNumber_whole (sort : List SortKey) :
    ∀ (pre s : List Row),
      (∀ r ∈ windowRows [] [.rowNumber] pre s, ∃ x ∈ s, ∃ k : Nat, pre.length < k ∧
        r = x ++ [.int k]) ∧
      (windowRows [] [.rowNumber] pre s).Pairwise fun r r' => r.getLast? ≠ r'.getLast?
  | pre, [] => by simp [windowRows]
  | pre, x :: s => by
    obtain ⟨ih1, ih2⟩ := windowRows_rowNumber_whole sort (pre ++ [x]) s
    have hall : ∀ y : Row, samePart [] x y = true := fun _ => rfl
    have hv : WinFn.value [] pre s x .rowNumber = .int (pre.length + 1) := by
      simp [WinFn.value, WinFn.valueIn, List.filter_eq_self.mpr fun y _ => hall y]
    simp only [windowRows, List.map_cons, List.map_nil, hv]
    refine ⟨fun r hr => ?_, List.pairwise_cons.mpr ⟨fun r' hr' => ?_, ih2⟩⟩
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨x, List.mem_cons_self, pre.length + 1, by omega, by simp⟩
      · obtain ⟨y, hy, k, hk, rfl⟩ := ih1 r hr
        exact ⟨y, List.mem_cons_of_mem _ hy, k, by simp at hk; omega, rfl⟩
    · obtain ⟨y, -, k, hk, rfl⟩ := ih1 r' hr'
      simp only [List.length_append, List.length_singleton] at hk
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, ne_eq,
        Option.some.injEq, Value.int.injEq]
      omega

/-- The reference allows only `windowRows` for `ROW_NUMBER`. -/
theorem windowRowsA_rowNumber {part : List Nat} {before s : List Row} {o : Relation}
    (h : windowRowsA part [.rowNumber] before s o) : o = windowRows part [.rowNumber] before s :=
  windowRowsA_eq (fun f hf m _ _ he => by simp at hf; subst hf; cases he) h

/-- Each row `ROW_NUMBER` gives is an input row and its number. -/
theorem windowRows_rowNumber_mem (part : List Nat) :
    ∀ {pre s : List Row} {r : Row}, r ∈ windowRows part [.rowNumber] pre s →
      ∃ z ∈ s, ∃ t : Nat, r = z ++ [.int t]
  | _, [], _, h => by simp [windowRows] at h
  | pre, x :: s, r, h => by
    simp only [windowRows, List.map_cons, List.map_nil, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨x, List.mem_cons_self, (pre.filter (samePart part x)).length + 1,
        by simp [WinFn.value, WinFn.valueIn]⟩
    · obtain ⟨z, hz, t, rfl⟩ := windowRows_rowNumber_mem part h
      exact ⟨z, List.mem_cons_of_mem _ hz, t, rfl⟩

/-! ## LEFT joins -/

omit [Boxes.Ambient] in
theorem keyOf_append_left {k : List Nat} {x y : Row} (hk : ∀ c ∈ k, c < x.length) :
    keyOf k (x ++ y) = keyOf k x := by
  simp only [keyOf, List.map_inj_left]
  intro c hc
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (hk c hc)]

/-- Each row a LEFT join gives a left row starts with it, and it gives one at
least. -/
theorem leftJoinRow_spec (on : Expr) (n : Nat) (ys : Relation) (x : Row) :
    leftJoinRow on n ys x ≠ [] ∧ ∀ r ∈ leftJoinRow on n ys x, ∃ y, r = x ++ y := by
  dsimp only [leftJoinRow]
  split
  · exact ⟨by simp, fun r hr => ⟨_, List.mem_singleton.mp hr⟩⟩
  · rename_i h
    refine ⟨fun he => by simp [he] at h, fun r hr => ?_⟩
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hr).1
    exact ⟨y, rfl⟩

/-- **A LEFT join keeps every left row's values of a left column**, and
gives no others. -/
theorem keyOf_leftJoin_iff {k : List Nat} {on : Expr} {n : Nat} {xs ys : Relation}
    (hk : ∀ x ∈ xs, ∀ c ∈ k, c < x.length) (v : List Value) :
    v ∈ (xs.flatMap (leftJoinRow on n ys)).map (keyOf k) ↔ v ∈ xs.map (keyOf k) := by
  simp only [List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨r, ⟨x, hx, hr⟩, rfl⟩
    obtain ⟨y, rfl⟩ := (leftJoinRow_spec on n ys x).2 r hr
    exact ⟨x, hx, (keyOf_append_left (hk x hx)).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ (leftJoinRow_spec on n ys x).1
    obtain ⟨y, rfl⟩ := (leftJoinRow_spec on n ys x).2 _ hr
    exact ⟨_, ⟨x, hx, hr⟩, keyOf_append_left (hk x hx)⟩

/-! ## The shape -/

/-- `ROW_NUMBER() - 1` of the `ROW_NUMBER` in column `n`: the number from 0
Ibis writes. -/
def Expr.rowNum0 (n : Nat) : Expr := .bin .sub (.field n) (.lit (.int 1))

/-- An emit `em` over a projection `ps` of rows of `n + 1` columns puts
`rowNum0 n` at its column `k`. -/
def emitsRowNum0 (n k : Nat) (em : List Nat) (ps : List Expr) : Bool :=
  match em[k]? with
  | some e => decide (n + 1 ≤ e) && decide (ps[e - (n + 1)]? = some (Expr.rowNum0 n))
  | none => false

omit [Boxes.Ambient] in
theorem getD_map_getD {em : List Nat} {k e : Nat} {row : Row} (h : em[k]? = some e) :
    (em.map (row.getD · .null)).getD k .null = row.getD e .null := by
  simp [List.getD_eq_getElem?_getD, h]

/-- What column `k` of such an emit holds: `ROW_NUMBER - 1` of the row. -/
theorem emitsRowNum0_spec {n k : Nat} {em : List Nat} {ps : List Expr}
    (h : emitsRowNum0 n k em ps = true) {x : Row} (hx : x.length = n) (t : Nat) :
    ((em.map ((x ++ [Value.int t] ++ ps.map (·.eval (x ++ [Value.int t]))).getD · .null)).getD k
      .null) = Value.int ((t : Int) - 1) := by
  unfold emitsRowNum0 at h
  split at h
  · rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hle, hp⟩ := h
    rw [getD_map_getD he, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, hx, List.length_singleton, List.getElem?_map, hp,
      Option.map_some, Option.getD_some]
    simp [Expr.rowNum0, Expr.eval, List.getD_eq_getElem?_getD, hx, BinFn.apply]
  · cases h

/-- The parts of a numbered left input: the left rows, the order of the
`ROW_NUMBER` over all of them, the projection over it and the emit. -/
def Rel.numberedParts : Rel → Option (Rel × List SortKey × List Expr × List Nat)
  | .emit (.project (.window l [] sort [.rowNumber]) les) lm => some (l, sort, les, lm)
  | _ => none

omit [Boxes.Ambient] in
theorem Rel.numberedParts_eq {r l : Rel} {sort : List SortKey} {les : List Expr} {lm : List Nat}
    (h : r.numberedParts = some (l, sort, les, lm)) :
    r = .emit (.project (.window l [] sort [.rowNumber]) les) lm := by
  unfold Rel.numberedParts at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  · cases h

/-- The left input as `asof.py` numbers it: the left rows `l`, `ROW_NUMBER`
over all of them, and its number from 0 in column `c`. -/
def Rel.numberedAt (cat : Catalog) (c : Nat) (r : Rel) : Bool :=
  match r.numberedParts with
  | some (l, _, les, lm) => emitsRowNum0 (l.arity cat) c lm les
  | none => false

/-- The layers above the ranking that keep the row count: emits and
projections. -/
def AsofLayer.keepsRows : AsofLayer → Bool
  | .emit _ | .project _ => true
  | _ => false

/-- **The shape of `sv.asof_join(how="left")`**: a LEFT join of the numbered
left rows (the number from 0 in column `c`, `Rel.numberedAt`), `ROW_NUMBER`
partitioned by `c`, its number from 0 in column `k` of an emit over a
projection, a filter that keeps 0 there, and above it emits and projections
only. -/
def AsofSite.leftExact (cat : Catalog) (s : AsofSite) : Bool :=
  match s.type, s.layers.reverse with
  | .left, .window [c] _ [.rowNumber] :: .project ps :: .emit em ::
      .filter (.bin .eq (.field k) (.lit (.int 0))) :: rest =>
    decide (c < s.numbered.arity cat) && s.numbered.numberedAt cat c &&
      emitsRowNum0 (s.numbered.arity cat + s.right.arity cat) k em ps && rest.all (·.keepsRows)
  | _, _ => false

/-! ## The count -/

omit [Boxes.Ambient] in
theorem AsofLayer.apply_append (ls ms : List AsofLayer) (r : Rel) :
    AsofLayer.apply (ls ++ ms) r = AsofLayer.apply ls (AsofLayer.apply ms r) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => cases l <;> simp [AsofLayer.apply, ih]

/-- Emits and projections keep the row count. -/
theorem AsofLayer.allowed_length {cat : Catalog} :
    ∀ {ls : List AsofLayer}, ls.all (·.keepsRows) = true → ∀ {r : Rel} {out : Relation},
      (AsofLayer.apply ls r).Allowed cat out → ∃ i, r.Allowed cat i ∧ out.length = i.length
  | [], _, _, _, h => ⟨_, h, rfl⟩
  | .emit _ :: ls, hl, r, out, h | .project _ :: ls, hl, r, out, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨j, hj, hlen⟩ := AsofLayer.allowed_length hl.2 hi
    exact ⟨j, hj, by simp [hlen]⟩
  | .window .. :: _, hl, _, _, _ | .filter _ :: _, hl, _, _, _ => by
    simp [AsofLayer.keepsRows] at hl

omit [Boxes.Ambient] in
theorem AsofLayer.apply_wf {cat : Catalog} {r : Rel} :
    ∀ {ls : List AsofLayer}, (AsofLayer.apply ls r).WF cat → r.WF cat
  | [], h => h
  | l :: ls, h => by
    cases l <;> exact AsofLayer.apply_wf (ls := ls) h.1

omit [Boxes.Ambient] in
theorem AsofLayer.apply_closedB {r : Rel} :
    ∀ {ls : List AsofLayer}, (AsofLayer.apply ls r).closedB = true → r.closedB = true
  | [], h => h
  | l :: ls, h => by
    cases l <;> exact AsofLayer.apply_closedB (ls := ls) h

/-- **The numbered left rows have a key**: the number from 0 that
`Rel.numberedAt` names. -/
theorem Rel.numberedAt_key {cat : Catalog} (hcat : cat.WF) {c : Nat} {r : Rel}
    (hn : r.numberedAt cat c = true) (hwf : r.WF cat) (hcl : r.closedB = true) {x : Relation}
    (hx : r.Allowed cat x) : KeyOn [c] x := by
  unfold Rel.numberedAt at hn
  split at hn
  · rename_i l sort les lm hp
    obtain rfl := Rel.numberedParts_eq hp
    obtain ⟨i, ⟨i', ⟨w, hw, s, hs, -, o, hpo, ho⟩, rfl⟩, rfl⟩ := hx
    rw [windowRowsA_rowNumber ho] at hpo
    have hl := hwf.1.1.1
    have hlen : ∀ y ∈ s, y.length = l.arity cat := fun y hy =>
      Rel.orderAllowed_arity hcat hl
        (Rel.allowed_orderAllowed (by simpa [Rel.closedB] using hcl) hw) y (hs.mem_iff.mp hy)
    obtain ⟨h1, h2⟩ := windowRows_rowNumber_whole sort [] s
    -- The key of a row of the window: its number from 0.
    have hkey : ∀ r ∈ windowRows [] [.rowNumber] [] s, ∃ k : Nat, 0 < k ∧
        r.getLast? = some (.int k) ∧
        keyOf [c] (lm.map ((r ++ les.map (·.eval r)).getD · .null)) = [.int (k - 1)] := by
      intro r hr
      obtain ⟨y, hy, k, hk, rfl⟩ := h1 r hr
      refine ⟨k, hk, by simp, ?_⟩
      simp only [keyOf, List.map_cons, List.map_nil, List.cons.injEq, and_true]
      rw [emitsRowNum0_spec hn (hlen y hy) k]
      simp [Value.canonV]
    unfold KeyOn
    rw [List.pairwise_map, List.pairwise_map]
    refine (hpo.symm.pairwise_iff fun h => Ne.symm h).mp ?_
    refine h2.imp_of_mem fun {r r'} hr hr' hne he => hne ?_
    obtain ⟨k, hk, hkl, hke⟩ := hkey r hr
    obtain ⟨k', hk', hkl', hke'⟩ := hkey r' hr'
    rw [hke, hke'] at he
    simp only [List.cons.injEq, Value.int.injEq, and_true] at he
    rw [hkl, hkl']
    congr 2
    omega
  · cases hn

/-- **A LEFT as-of join keeps one row per left row** (#1992, ruling 194 D5):
every result the reference allows for a site of `sv.asof_join(how="left")`'s
shape has as many rows as the numbered left input it is built from. -/
theorem AsofSite.left_exactly_one {cat : Catalog} (hcat : cat.WF) {s : AsofSite}
    (hs : s.leftExact cat = true) (hwf : s.toRel.WF cat) (hcl : s.toRel.closedB = true)
    {out : Relation} (h : s.toRel.Allowed cat out) :
    ∃ x, s.numbered.Allowed cat x ∧ out.length = x.length := by
  obtain ⟨layers, numbered, right, type, on, keys, lon, ron, rest⟩ := s
  simp only [AsofSite.leftExact] at hs
  split at hs
  · rename_i c srt ps em k pre hrev
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨hc, hnum⟩, hem⟩, hpre⟩ := hs
    have hlay : layers = pre.reverse ++ [.filter (.bin .eq (.field k) (.lit (.int 0))), .emit em,
        .project ps, .window [c] srt [.rowNumber]] := by
      rw [← List.reverse_reverse layers, hrev]; simp
    simp only [AsofSite.toRel, hlay, AsofLayer.apply_append] at h hwf hcl
    have hjwf : (Rel.join numbered right .left on).WF cat :=
      AsofLayer.apply_wf (ls := [.filter (.bin .eq (.field k) (.lit (.int 0))), .emit em,
        .project ps, .window [c] srt [.rowNumber]]) (AsofLayer.apply_wf (ls := pre.reverse) hwf)
    have hjcl : numbered.closedB = true ∧ right.closedB = true := Bool.and_eq_true_iff.mp
      (AsofLayer.apply_closedB (ls := [.filter (.bin .eq (.field k) (.lit (.int 0))), .emit em,
        .project ps, .window [c] srt [.rowNumber]]) (AsofLayer.apply_closedB (ls := pre.reverse) hcl))
    obtain ⟨f, hf, hlen⟩ := AsofLayer.allowed_length (by simpa using hpre) h
    simp only [AsofLayer.apply] at hf
    obtain ⟨e, ⟨p, ⟨q, ⟨w, hw, s', hs', -, o, hpo, ho⟩, rfl⟩, rfl⟩, rfl⟩ := hf
    rw [windowRowsA_rowNumber ho] at hpo
    obtain ⟨x, y, hx, hy, hj⟩ := hw
    refine ⟨x, hx, ?_⟩
    rw [hlen]
    -- The arities: the numbered rows (an emit), the right rows, the joined rows.
    have hxlen : ∀ r ∈ x, r.length = numbered.arity cat := fun r hr =>
      Rel.orderAllowed_arity hcat hjwf.1 (Rel.allowed_orderAllowed hjcl.1 hx) r hr
    have hylen : ∀ r ∈ y, r.length = right.arity cat := fun r hr =>
      Rel.orderAllowed_arity hcat hjwf.2.1 (Rel.allowed_orderAllowed hjcl.2 hy) r hr
    have hjlen : ∀ r ∈ s', r.length = numbered.arity cat + right.arity cat := by
      intro r hr
      obtain ⟨z, hz, hr⟩ := List.mem_flatMap.mp (hj.mem_iff.mp (hs'.mem_iff.mp hr))
      dsimp only [leftJoinRow] at hr
      split at hr
      · rw [List.mem_singleton.mp hr]; simp [hxlen z hz]
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hr).1
        simp [hxlen z hz, hylen u hu]
    -- The filter keeps the rows `ROW_NUMBER` gives 1.
    have hkeep : ∀ r ∈ windowRows [c] [.rowNumber] [] s',
        (((Expr.bin .eq (.field k) (.lit (.int 0))).eval
          (em.map ((r ++ ps.map (·.eval r)).getD · .null))).isTrue) =
        (r.getLast? == some (.int 1)) := by
      intro r hr
      obtain ⟨z, hz, t, rfl⟩ := windowRows_rowNumber_mem [c] hr
      have hv := emitsRowNum0_spec hem (hjlen z hz) t
      simp only [Expr.eval] at hv ⊢
      rw [hv]
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
      by_cases ht : t = 1
      · subst ht; simp [BinFn.apply, Value.isTrue]
      · have : (t : Int) - 1 ≠ 0 := by omega
        have : (t : Int) ≠ 1 := by omega
        simp [BinFn.apply, Value.isTrue, *]
    -- The numbered rows' keys: as many as the rows.
    have hkey := Rel.numberedAt_key hcat hnum hjwf.1 hjcl.1 hx
    have hck : ∀ r ∈ x, ∀ c' ∈ [c], c' < r.length := by
      intro r hr c' hc'; rw [List.mem_singleton.mp hc', hxlen r hr]; exact hc
    have hcount := windowRows_rowNumber_count [c] [] s'
    simp only [List.map_nil, dedup_nil, List.length_nil, Nat.add_zero, List.nil_append] at hcount
    rw [List.filter_map, List.length_map, List.filter_map, List.length_map,
      (hpo.filter _).length_eq]
    simp only [Function.comp_def]
    rw [List.filter_congr fun r hr => hkeep r hr, hcount,
      (dedup_perm_of_mem fun v => by
        have hm : v ∈ s'.map (keyOf [c]) ↔
            v ∈ (x.flatMap (leftJoinRow on (right.arity cat) y)).map (keyOf [c]) := by
          simp only [List.mem_map]
          exact exists_congr fun r => and_congr_left fun _ => (hs'.trans hj).mem_iff
        exact hm.trans (keyOf_leftJoin_iff hck v)).length_eq,
      dedup_of_nodup (List.pairwise_map.mpr hkey), List.length_map]
  · cases hs

end Substrait
