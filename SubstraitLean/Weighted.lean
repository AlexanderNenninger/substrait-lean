import SubstraitLean.Incremental

/-!
# Running Z-set plans on a bag engine

Engines like DataFusion only know ordinary tables. `Rel.weighted` compiles a plan
over Z-sets into an ordinary plan in which every row carries its weight as an
**extra trailing column**:

* old tables get weight `1` appended (`project (read t) [1]`);
* change tables (`isW t`) already store the weight as their last column;
* filter and union are unchanged; project and emit keep the weight last;
* cross and inner join multiply the two weights, and the join condition's
  right-side field references shift by one past the left weight column.

`Rel.weighted_eval` proves that the engine's (bag) result is exactly the Z-set
result with weights encoded as a column.
-/

namespace Substrait

/-- A weighted row as an engine stores it: the weight as an extra last column. -/
def wrow (x : Row × Int) : Row := x.1 ++ [.int x.2]

def ZSet.encode (z : ZSet) : Relation := List.map wrow z

/-- Make room for one extra column at position `n`. -/
def Expr.shift (n : Nat) : Expr → Expr
  | .lit v => .lit v
  | .field i => .field (if i < n then i else i + 1)
  | .un f a => .un f (a.shift n)
  | .bin f a b => .bin f (a.shift n) (b.shift n)
  | .ifThen c t e => .ifThen (c.shift n) (t.shift n) (e.shift n)

/-- Columns `0..n-1`, then `n+1..n+k`, then `last`: drops the column at `n`
and moves `last` (the weight) to the end. -/
def spliceIdx (n k last : Nat) : List Nat :=
  List.range n ++ (List.range k).map (n + 1 + ·) ++ [last]

def Rel.weighted (cat : Catalog) (isW : String → Bool) : Rel → Rel
  | .read t => if isW t then .read t else .project (.read t) [.lit (.int 1)]
  | .values n rows => .values (n + 1) (rows.map (· ++ [.int 1]))
  | .filter r c => .filter (r.weighted cat isW) c
  | .project r es =>
      .emit (.project (r.weighted cat isW) es) (spliceIdx (r.arity cat) es.length (r.arity cat))
  | .emit r m => .emit (r.weighted cat isW) (m ++ [r.arity cat])
  | .cross a b =>
      let n := a.arity cat
      let m := b.arity cat
      .emit (.project (.cross (a.weighted cat isW) (b.weighted cat isW))
          [.bin .mul (.field n) (.field (n + m + 1))])
        (spliceIdx n m (n + m + 2))
  | .join a b ty on =>
      let n := a.arity cat
      let m := b.arity cat
      .emit (.project (.join (a.weighted cat isW) (b.weighted cat isW) ty (on.shift n))
          [.bin .mul (.field n) (.field (n + m + 1))])
        (spliceIdx n m (n + m + 2))
  | .unionAll a b => .unionAll (a.weighted cat isW) (b.weighted cat isW)
  | .fetch r o c => .fetch (r.weighted cat isW) o c
  | .window r p s f => .window (r.weighted cat isW) p s f
  | .orderBy r keys => .orderBy (r.weighted cat isW) keys
  -- Outside the incremental fragment.
  | .semi a b anti on => .semi (a.weighted cat isW) (b.weighted cat isW) anti on
  | .distinct r => .distinct (r.weighted cat isW)

/-! ## Index bookkeeping -/

theorem map_range_getD (L : List Value) (n : Nat) (h : n ≤ L.length) :
    (List.range n).map (fun i => L.getD i .null) = L.take n := by
  apply List.ext_getElem (by simp; omega)
  intro i h₁ _
  have : i < n := by simpa using h₁
  simp [List.getD, List.getElem?_eq_getElem (show i < L.length by omega)]

theorem map_range_getD_off (L : List Value) (off k : Nat) (h : off + k ≤ L.length) :
    (List.range k).map (fun j => L.getD (off + j) .null) = (L.drop off).take k := by
  apply List.ext_getElem (by simp; omega)
  intro i h₁ _
  have : i < k := by simpa using h₁
  simp [List.getD, List.getElem?_eq_getElem (show off + i < L.length by omega)]

/-- Evaluating the splice on `xs ++ [w] ++ ys` (with `|xs| = n`, `|ys| = k`). -/
theorem splice_eval (xs ys : Row) (w : Value) (rest : Row) (last : Nat)
    (hlast : ((xs ++ [w]) ++ ys ++ rest).getD last .null = w') :
    (spliceIdx xs.length ys.length last).map (((xs ++ [w]) ++ ys ++ rest).getD · .null)
      = xs ++ ys ++ [w'] := by
  simp only [spliceIdx, List.map_append, List.map_map, Function.comp_def, List.map_cons,
    List.map_nil, hlast]
  rw [map_range_getD _ _ (by simp), map_range_getD_off _ _ _ (by simp; omega)]
  have : xs.drop (xs.length + 1) = [] := List.drop_eq_nil_of_le (by omega)
  simp [List.drop_append, this]

theorem Expr.eval_shift {e : Expr} (xa xb rest : Row) (w : Value)
    (he : e.refsLt (xa.length + xb.length)) :
    (e.shift xa.length).eval ((xa ++ [w]) ++ (xb ++ rest)) = e.eval (xa ++ xb) := by
  induction e with
  | lit => rfl
  | field i =>
    simp only [refsLt] at he
    simp only [shift, eval, List.getD]
    split
    · rename_i h
      rw [List.append_assoc, List.getElem?_append_left h, List.getElem?_append_left h]
    · rename_i h
      have h2 : i - xa.length < xb.length := by omega
      have hl : (xa ++ [w] ++ (xb ++ rest))[i + 1]? = xb[i - xa.length]? := by
        rw [List.append_assoc, List.getElem?_append_right (by omega),
          show i + 1 - xa.length = (i - xa.length) + 1 by omega, List.singleton_append,
          List.getElem?_cons_succ, List.getElem?_append_left h2]
      rw [hl, List.getElem?_append_right (by omega)]
  | un f a ih => simp only [shift, eval, ih he]
  | bin f a b iha ihb => simp only [shift, eval, iha he.1, ihb he.2]
  | ifThen c t e ihc iht ihe => simp only [shift, eval, ihc he.1, iht he.2.1, ihe he.2.2]

/-! ## Arity of Z-set results -/

theorem Rel.zeval_arity {cat : Catalog} {Z : ZCatalog}
    (hZ : ∀ t, ∀ x ∈ Z t, x.1.length = (cat t).arity) :
    ∀ {r : Rel}, r.WF cat → r.Incremental → ∀ x ∈ r.zeval Z, x.1.length = r.arity cat
  | .read t, _, _, x, h => hZ t x h
  | .values _ _, hwf, _, x, h => by
      simp only [zeval, ZSet.lift, List.mem_map] at h
      obtain ⟨row, hr, rfl⟩ := h
      exact hwf row hr
  | .filter r _, hwf, hi, x, h => by
      simp only [zeval, ZSet.filter, List.mem_filter] at h
      exact zeval_arity hZ hwf.1 hi x h.1
  | .project r es, hwf, hi, x, h => by
      simp only [zeval, ZSet.map, List.mem_map] at h
      obtain ⟨y, hy, rfl⟩ := h
      simp [arity, zeval_arity hZ hwf.1 hi y hy]
  | .emit _ _, _, _, x, h => by
      simp only [zeval, ZSet.map, List.mem_map] at h
      obtain ⟨y, _, rfl⟩ := h
      simp [arity]
  | .cross a b, hwf, hi, x, h => by
      simp only [zeval, ZSet.cross, List.mem_flatMap, List.mem_map] at h
      obtain ⟨y, hy, z, hz, rfl⟩ := h
      simp [arity, zeval_arity hZ hwf.1 hi.1 y hy, zeval_arity hZ hwf.2 hi.2 z hz]
  | .join a b .inner _, hwf, hi, x, h => by
      simp only [zeval, ZSet.filter, ZSet.cross, List.mem_filter, List.mem_flatMap,
        List.mem_map] at h
      obtain ⟨⟨y, hy, z, hz, rfl⟩, _⟩ := h
      simp [arity, zeval_arity hZ hwf.1 hi.1 y hy, zeval_arity hZ hwf.2.1 hi.2 z hz]
  | .unionAll a b, hwf, hi, x, h => by
      simp only [zeval, List.mem_append] at h
      rcases h with h | h
      · exact zeval_arity hZ hwf.1 hi.1 x h
      · simp only [arity, hwf.2.2]; exact zeval_arity hZ hwf.2.1 hi.2 x h
  | .orderBy r _, hwf, hi, x, h => by
      simp only [zeval, List.mem_mergeSort] at h
      exact zeval_arity hZ (r := r) hwf.1 hi x h
  | .join _ _ .left _, _, hi, _, _ => hi.elim
  | .fetch _ _ _, _, hi, _, _ | .window _ _ _ _, _, hi, _, _ | .semi _ _ _ _, _, hi, _, _
  | .distinct _, _, hi, _, _ => hi.elim

/-- Sort keys only look at their own columns. -/
theorem sortLe_append {x y e e' : Row} :
    ∀ {ks : List SortKey}, (∀ k ∈ ks, k.col < x.length) → (∀ k ∈ ks, k.col < y.length) →
      sortLe ks (x ++ e) (y ++ e') = sortLe ks x y
  | [], _, _ => rfl
  | k :: ks, hx, hy => by
      have hkx : (x ++ e).getD k.col .null = x.getD k.col .null := by
        simp [List.getD, List.getElem?_append_left (hx k (by simp))]
      have hky : (y ++ e').getD k.col .null = y.getD k.col .null := by
        simp [List.getD, List.getElem?_append_left (hy k (by simp))]
      simp only [sortLe, lexLe, SortKey.le, hkx, hky,
        sortLe_append (ks := ks) (fun k hk => hx k (by simp [hk])) (fun k hk => hy k (by simp [hk]))]

/-! ## Correctness -/

def pairs (A B : ZSet) : List ((Row × Int) × (Row × Int)) :=
  List.flatMap (fun a => List.map (fun b => (a, b)) B) A

theorem cross_eq_pairs (A B : ZSet) :
    ZSet.cross A B = (pairs A B).map fun p => (p.1.1 ++ p.2.1, p.1.2 * p.2.2) := by
  simp [ZSet.cross, pairs, List.map_flatMap, Function.comp_def]

theorem crossRows_encode (A B : ZSet) :
    crossRows (List.map wrow A) (List.map wrow B) = (pairs A B).map fun p => wrow p.1 ++ wrow p.2 := by
  simp [crossRows, pairs, List.flatMap_map, List.map_flatMap, Function.comp_def]

theorem mem_pairs {A B : ZSet} {p : (Row × Int) × (Row × Int)} :
    p ∈ pairs A B ↔ p.1 ∈ A ∧ p.2 ∈ B := by
  obtain ⟨a, b⟩ := p
  simp [pairs]

theorem getElem?_after (xa L : Row) (w : Value) (j : Nat) :
    (xa ++ w :: L)[xa.length + 1 + j]? = L[j]? := by
  rw [List.getElem?_append_right (by omega), show xa.length + 1 + j - xa.length = j + 1 by omega,
    List.getElem?_cons_succ]

/-- The project + emit that the cross/join encoding puts on top. -/
theorem weight_mul_row (xa xb : Row) (wa wb : Int) :
    (spliceIdx xa.length xb.length (xa.length + xb.length + 2)).map
      ((wrow (xa, wa) ++ wrow (xb, wb) ++
        [BinFn.mul.apply ((wrow (xa, wa) ++ wrow (xb, wb)).getD xa.length .null)
          ((wrow (xa, wa) ++ wrow (xb, wb)).getD (xa.length + xb.length + 1) .null)]).getD · .null)
      = wrow (xa ++ xb, wa * wb) := by
  have h₁ : (wrow (xa, wa) ++ wrow (xb, wb)).getD xa.length .null = .int wa := by
    simp [wrow, List.getD]
  have h₂ : (wrow (xa, wa) ++ wrow (xb, wb)).getD (xa.length + xb.length + 1) .null = .int wb := by
    simp only [wrow, List.getD, List.append_assoc, List.singleton_append]
    rw [show xa.length + xb.length + 1 = xa.length + 1 + xb.length by omega, getElem?_after]
    simp
  rw [h₁, h₂]
  have := splice_eval xa xb (.int wa) [.int wb, .int (wa * wb)] (xa.length + xb.length + 2)
    (w' := .int (wa * wb)) (by
      simp only [List.getD, List.append_assoc, List.cons_append]
      rw [show xa.length + xb.length + 2 = xa.length + 1 + (xb.length + 1) by omega, getElem?_after]
      simp)
  simpa [wrow, BinFn.apply, List.append_assoc] using this

/-- **The weight-column encoding is correct.** `E` is the engine's catalog and
`Z` the Z-set view of it: `hT` says each table the plan reads holds the
encoding of its Z-set (see `weighted_read_plain` for old tables). -/
theorem Rel.weighted_eval {cat E : Catalog} {Z : ZCatalog} {isW : String → Bool}
    (hZ : ∀ t, ∀ x ∈ Z t, x.1.length = (cat t).arity) :
    ∀ {r : Rel}, r.WF cat → r.Incremental →
      (∀ t ∈ r.tables, ((Rel.read t).weighted cat isW).eval E = (Z t).encode) →
      (r.weighted cat isW).eval E = (r.zeval Z).encode
  | .read t, _, _, hT => hT t (by simp [tables])
  | .values _ _, _, _, _ => by
      simp [weighted, eval, zeval, ZSet.encode, ZSet.lift, wrow]
  | .filter r c, hwf, hi, hT => by
      simp only [weighted, eval, zeval, weighted_eval hZ hwf.1 hi hT, ZSet.encode, ZSet.filter,
        List.filter_map]
      congr 1
      apply List.filter_congr
      intro x hx
      simp [wrow, Expr.eval_append _ hwf.2 (zeval_arity hZ hwf.1 hi x hx)]
  | .project r es, hwf, hi, hT => by
      simp only [weighted, eval, zeval, weighted_eval hZ hwf.1 hi hT, ZSet.encode, ZSet.map,
        List.map_map]
      apply List.map_congr_left
      intro x hx
      have hlen := zeval_arity hZ hwf.1 hi x hx
      have hes : es.map (·.eval (x.1 ++ [.int x.2])) = es.map (·.eval x.1) :=
        List.map_congr_left fun e he => Expr.eval_append _ (hwf.2 e he) hlen
      simp only [Function.comp_apply, wrow, hes]
      rw [← hlen, show es.length = (es.map (·.eval x.1)).length by simp]
      have := splice_eval x.1 (es.map (·.eval x.1)) (.int x.2) [] x.1.length (w' := .int x.2)
        (by simp [List.getD])
      simp only [List.append_nil] at this
      exact this
  | .emit r m, hwf, hi, hT => by
      simp only [weighted, eval, zeval, weighted_eval hZ hwf.1 hi hT, ZSet.encode, ZSet.map,
        List.map_map]
      apply List.map_congr_left
      intro x hx
      have hlen := zeval_arity hZ hwf.1 hi x hx
      simp only [Function.comp_apply, wrow, List.map_append, List.map_cons, List.map_nil]
      congr 1
      · apply List.map_congr_left
        intro i hi'
        have := hwf.2 i hi'
        simp [List.getD, List.getElem?_append_left (show i < x.1.length by omega)]
      · simp [List.getD, ← hlen]
  | .cross a b, hwf, hi, hT => by
      simp only [tables, List.mem_append] at hT
      simp only [weighted, eval, zeval,
        weighted_eval hZ hwf.1 hi.1 (fun t ht => hT t (.inl ht)),
        weighted_eval hZ hwf.2 hi.2 (fun t ht => hT t (.inr ht)),
        ZSet.encode, crossRows_encode, cross_eq_pairs, List.map_map]
      apply List.map_congr_left
      intro p hp
      rw [mem_pairs] at hp
      have ha := zeval_arity hZ hwf.1 hi.1 _ hp.1
      have hb := zeval_arity hZ hwf.2 hi.2 _ hp.2
      simp only [Function.comp_apply, List.map_cons, List.map_nil, Expr.eval]
      rw [← ha, ← hb]
      exact weight_mul_row p.1.1 p.2.1 p.1.2 p.2.2
  | .join a b .inner on, hwf, hi, hT => by
      simp only [tables, List.mem_append] at hT
      simp only [weighted, eval, zeval,
        weighted_eval hZ hwf.1 hi.1 (fun t ht => hT t (.inl ht)),
        weighted_eval hZ hwf.2.1 hi.2 (fun t ht => hT t (.inr ht)),
        ZSet.encode, crossRows_encode, cross_eq_pairs, ZSet.filter, List.map_map,
        List.filter_map]
      -- The shifted condition on encoded rows is the condition on plain rows.
      rw [List.filter_congr (q := fun p => (on.eval (p.1.1 ++ p.2.1)).isTrue) ?cond]
      case cond =>
        intro p hp
        rw [mem_pairs] at hp
        have ha := zeval_arity hZ hwf.1 hi.1 _ hp.1
        have hb := zeval_arity hZ hwf.2.1 hi.2 _ hp.2
        simp only [Function.comp_apply, wrow]
        rw [← ha, Expr.eval_shift _ _ _ _ (by rw [ha, hb]; exact hwf.2.2)]
      apply List.map_congr_left
      intro p hp
      rw [List.mem_filter, mem_pairs] at hp
      have ha := zeval_arity hZ hwf.1 hi.1 _ hp.1.1
      have hb := zeval_arity hZ hwf.2.1 hi.2 _ hp.1.2
      simp only [Function.comp_apply, List.map_cons, List.map_nil, Expr.eval]
      rw [← ha, ← hb]
      exact weight_mul_row p.1.1 p.2.1 p.1.2 p.2.2
  | .unionAll a b, hwf, hi, hT => by
      simp only [tables, List.mem_append] at hT
      simp [weighted, eval, zeval, ZSet.encode,
        weighted_eval hZ hwf.1 hi.1 (fun t ht => hT t (.inl ht)),
        weighted_eval hZ hwf.2.1 hi.2 (fun t ht => hT t (.inr ht))]
  | .orderBy r keys, hwf, hi, hT => by
      simp only [weighted, eval, zeval, weighted_eval hZ hwf.1 hi hT, ZSet.encode]
      refine (List.map_mergeSort fun a ha b hb => ?_).symm
      have hla := zeval_arity hZ hwf.1 hi a ha
      have hlb := zeval_arity hZ hwf.1 hi b hb
      simp only [wrow]
      exact (sortLe_append (fun k hk => hla ▸ hwf.2 k hk) (fun k hk => hlb ▸ hwf.2 k hk)).symm
  | .join _ _ .left _, _, hi, _ => hi.elim
  | .fetch _ _ _, _, hi, _ | .window _ _ _ _, _, hi, _ | .semi _ _ _ _, _, hi, _
  | .distinct _, _, hi, _ => hi.elim

/-- Old (unweighted) tables satisfy `weighted_eval`'s table hypothesis with
every row at weight 1. -/
theorem weighted_read_plain {cat E : Catalog} {isW : String → Bool} {t : String}
    (h : isW t = false) :
    ((Rel.read t).weighted cat isW).eval E = (ZSet.lift (E t).rows).encode := by
  simp [Rel.weighted, h, Rel.eval, Expr.eval, ZSet.encode, ZSet.lift, wrow]

def Rel.isIncremental : Rel → Bool
  | .read _ | .values _ _ => true
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ => r.isIncremental
  | .cross a b | .unionAll a b | .join a b .inner _ => a.isIncremental && b.isIncremental
  | .join _ _ .left _ | .fetch _ _ _ | .window _ _ _ _ | .semi _ _ _ _ | .distinct _ => false

theorem Rel.isIncremental_iff {r : Rel} : r.isIncremental = true ↔ r.Incremental := by
  induction r with
  | join a b ty _ iha ihb => cases ty <;> simp_all [isIncremental, Incremental]
  | _ => simp_all [isIncremental, Incremental]

end Substrait
