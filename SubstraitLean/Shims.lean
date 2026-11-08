import SubstraitLean.Profile
import Sverify.Core.Order

/-!
# Shims the engines share (#1166)

Lemmas about a shim, or a guard, that more than one engine's translation
writes the same way, stated once for all of them: `Shim.<name>`. An engine's
own shims are in its module (`SubstraitLean/PolarsShims.lean`,
`SubstraitLean/SparkShims.lean`, DuckDB's lowering); its rows cite these
where its shim is one of them.

* `one_zero`: `-0.0` as `0.0` (Polars's `one_zero`, `Dialect.canon` on DuckDB
  and Spark).
* `null_order`: each key's NULL placement written (`nullsLast`, `sortWith`).
* `sum_empty_null`: an exact integer `SUM`, NULL for no values (Polars's
  `sum_empty_null`, Spark's `int_sum_decimal`).
* `avg_trunc`: an `AVG` of integers as the exact sum truncated by the count
  (Polars's `avg_int_declared`, Spark's `int_avg_decimal`).
* `makes_infinite`: the guard on an overflow to `±∞` (A4).

**Trusted**, per engine: that its function is the model here, from its facts.
-/

namespace Substrait.Shim

open FloatCode

/-! ## Zeros: `zero_sign` = `ONE_ZERO` -/

/-- `one_zero`: `-0.0` as `0.0`, on the full set of codes
(`FloatFormat.negZero`, #444 step 1b). An engine that compares IEEE doubles,
where `-0.0 = 0.0`, writes it as `x + 0.0` (`Dialect.canon`) or as Polars's
`one_zero` (polars-zero-sign, spark-zero-sign, duckdb-R14). -/
def oneZero (c : Int) : Int := if c = 0 ∨ c = FloatCode.negZero then 0 else c

/-- **`Shim.one_zero`**: the shim is `canon` on every code but the negative
NaN, whose sign an engine may keep (`nan_kind`, refines up to `canon`, B2);
so the keys it groups, deduplicates and joins on are the reference's codes. -/
theorem one_zero {c : Int} (h : c ≠ FloatCode.negNan) : oneZero c = FloatCode.canon c := by
  unfold oneZero
  have hz := fp64.negZero_ne_negNan
  by_cases h0 : c = 0
  · subst h0; simp [FloatCode.canon_zero]
  · by_cases hn : c = FloatCode.negZero
    · subst hn; simp [fp64.canon_negZero]
    · simp only [h0, hn, or_self, ite_false]
      exact (fp64.canon_eq_self ⟨hn, h⟩).symm

theorem one_zero_isRef {c : Int} (h : FloatCode.IsRef c ∨ c = FloatCode.negZero) :
    FloatCode.IsRef (oneZero c) := by
  have hne : c ≠ FloatCode.negNan := by
    rcases h with h | h
    · intro e; subst e; exact fp64.not_isRef_negNan h
    · intro e; exact fp64.negZero_ne_negNan (h.symm.trans e)
  rw [one_zero hne]
  exact fp64.isRef_canon_of_isRef_or (h.elim .inl fun e => .inr (.inl e))

/-! ## Aggregates: `empty_group_aggregates` and `avg_int_result` -/

/-- An engine's `sum` of a group's integers, exact: 0 for no values
(polars-sum-int); Spark sums them as `DECIMAL(38,0)` (spark-sum-int). -/
def sum0 (vs : List Int) : Int := vs.sum

/-- `sum_empty_null`: NULL where the group has no values. -/
def sumEmptyNull (vs : List Int) : Value := if vs.length = 0 then .null else .int (sum0 vs)

theorem intSum_map_int : ∀ vs : List Int, intSum (vs.map .int) = vs.sum
  | [] => rfl
  | v :: vs => by simp [intSum, intSum_map_int vs, List.sum_cons]

theorem sumOf_map_int (vs : List Int) : sumOf (vs.map .int) = .int (intSum (vs.map .int)) := by
  rcases sumOf_cases (vs.map .int) with ⟨s, h1, _⟩ | ⟨_, e⟩
  · exfalso
    simp only [allDecOf, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h1
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h1.1
    have hd := List.all_eq_true.mp h1.2 w hw
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
    simp [Value.isDecOf] at hd
  · exact e

/-- **`Shim.sum_empty_null`**: the shimmed `SUM` is the reference's
(`AggFn.sum`): NULL for no values. -/
theorem sum_empty_null (vs : List Int) : sumEmptyNull vs = AggFn.sum.apply (vs.map .int) := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    simp only [sumEmptyNull, List.length_cons, Nat.add_one_ne_zero, ite_false, sum0]
    show _ = sumOf ((v :: vs).map .int)
    rw [sumOf_map_int, intSum_map_int]

/-- `avg_trunc`: the exact sum of a group's integers truncated by their
count, NULL for no values (Spark's `div` truncates, spark-int-divide; Polars's
`avg_int_declared` corrects its floored quotient to it). -/
def avgTrunc (vs : List Int) : Value :=
  if vs.length = 0 then .null else .int (vs.sum.tdiv vs.length)

theorem sum_between (lo hi : Int) : ∀ vs : List Int, (∀ x ∈ vs, lo ≤ x ∧ x ≤ hi) →
    vs.length * lo ≤ vs.sum ∧ vs.sum ≤ vs.length * hi
  | [], _ => by simp
  | v :: vs, h => by
    have ih := sum_between lo hi vs fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hv := h v (List.mem_cons_self ..)
    simp only [List.length_cons, List.sum_cons, Int.natCast_add, Int.natCast_one, Int.add_mul,
      Int.one_mul]
    omega

/-- A truncated mean lies between the values. -/
theorem tdiv_mean_between {s lo hi : Int} {n : Nat} (hn : 0 < n) (h1 : n * lo ≤ s)
    (h2 : s ≤ n * hi) : lo ≤ s.tdiv n ∧ s.tdiv n ≤ hi := by
  have hn' : (0 : Int) < n := by omega
  have hd := Int.emod_add_ediv_mul s n
  have hr0 := Int.emod_nonneg s (b := n) (by omega)
  have hr1 := Int.emod_lt_of_pos s hn'
  -- `s = q n + r`, `0 ≤ r < n`.
  have hq := Int.mul_comm (s / n) n
  have l1 : lo ≤ s / n := by
    apply Int.le_of_lt_add_one
    apply Int.lt_of_mul_lt_mul_left (a := (n : Int)) _ (by omega)
    rw [Int.mul_add, Int.mul_one]
    omega
  have l2 : s / n ≤ hi := Int.le_of_mul_le_mul_left (by omega) hn'
  rw [Int.tdiv_eq_ediv]
  simp only [Int.sign_eq_one_of_pos hn']
  split
  · omega
  · rename_i hnot
    have hm : s % n ≠ 0 := fun h => hnot (.inr (Int.dvd_of_emod_eq_zero h))
    -- `s` is not a multiple of `n`, so the quotient is below `hi`.
    have l3 : s / n < hi := by
      apply Int.lt_of_mul_lt_mul_left (a := (n : Int)) _ (by omega)
      omega
    omega

theorem foldl_min_le_mem : ∀ (x : Int) (xs : List Int), ∀ y ∈ x :: xs, xs.foldl min x ≤ y
  | x, [], y, hy => by simp at hy; subst hy; exact Int.le_refl _
  | x, z :: zs, y, hy => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hy with h | h
    · subst h
      exact Int.le_trans (foldl_min_le_mem (min y z) zs _ (List.mem_cons_self ..)) (Int.min_le_left _ _)
    · rcases List.mem_cons.mp h with h | h
      · subst h
        exact Int.le_trans (foldl_min_le_mem (min x y) zs _ (List.mem_cons_self ..)) (Int.min_le_right _ _)
      · exact foldl_min_le_mem (min x z) zs y (List.mem_cons_of_mem _ h)

theorem le_foldl_max_mem : ∀ (x : Int) (xs : List Int), ∀ y ∈ x :: xs, y ≤ xs.foldl max x
  | x, [], y, hy => by simp at hy; subst hy; exact Int.le_refl _
  | x, z :: zs, y, hy => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hy with h | h
    · subst h
      exact Int.le_trans (Int.le_max_left _ _) (le_foldl_max_mem (max y z) zs _ (List.mem_cons_self ..))
    · rcases List.mem_cons.mp h with h | h
      · subst h
        exact Int.le_trans (Int.le_max_right _ _) (le_foldl_max_mem (max x y) zs _ (List.mem_cons_self ..))
      · exact le_foldl_max_mem (max x z) zs y (List.mem_cons_of_mem _ h)

theorem intsOf_map_int (vs : List Int) : intsOf (vs.map .int) = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [intsOf] at ih ⊢; exact ih

/-- **`Shim.avg_trunc`**: the truncated mean is the reference's `AVG` of
integers (`AggFn.iavg`): it lies between the values, so the reference's
clamp leaves it. -/
theorem avg_trunc (vs : List Int) : avgTrunc vs = AggFn.iavg.apply (vs.map .int) := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    have hl : (v :: vs).length ≠ 0 := by simp only [List.length_cons]; omega
    simp only [avgTrunc, hl, ite_false, AggFn.apply, List.map_cons]
    rw [← List.map_cons, intSum_map_int, List.length_map]
    congr 1
    unfold clampInts
    rw [intsOf_map_int]
    simp only
    have hb := sum_between (vs.foldl min v) (vs.foldl max v) (v :: vs) fun x hx =>
      ⟨foldl_min_le_mem v vs x hx, le_foldl_max_mem v vs x hx⟩
    have hm := tdiv_mean_between (s := (v :: vs).sum) (n := (v :: vs).length) (by simp) hb.1 hb.2
    rw [Int.max_eq_left hm.1, Int.min_eq_left hm.2]

/-! ## Sorts: `null_order` -/

/-- The placement of NULLs the translation writes for a key: as the key
states, and last for an `UNSPECIFIED` key (D8). Natively Polars puts NULLs
first in both directions (polars-null-order), Spark first in an ascending
key and last in a descending one (spark-null-order). -/
def nullsLast (k : SortKey) : Bool := if k.nullsOpen then true else !k.nullsFirst

/-- An engine's sort comparator for keys with their direction and NULL
placement written per key: NULLs first unless last, the values by `Value.le`
(polars-null-order, spark-null-order; NaN greatest, polars-nan-order,
spark-nan-order). -/
def sortWith (ks : List (SortKey × Bool)) : Row → Row → Bool :=
  sortLeWith Value.le (ks.map fun (k, last) => (k, !last))

/-- **`Shim.null_order`**: with each key's placement written, the engine
orders rows as the reference (`sortLe`). -/
theorem null_order (ks : List SortKey) : sortWith (ks.map fun k => (k, nullsLast k)) = sortLe ks := by
  rw [← sortLeWith_le]
  unfold sortWith
  congr 1
  rw [List.map_map]
  congr 1
  funext k
  simp only [Function.comp, nullsLast, SortKey.firstNulls]
  cases k.nullsOpen <;> cases k.nullsFirst <;> rfl

/-! ## Guards: `makes_infinite` -/

/-- `makes_infinite`: finite arguments, an infinite result (`is_finite`,
`is_infinite` on codes). -/
def makesInfinite (y : Int) (xs : List Int) : Bool := xs.all isFiniteCode && isInfCode y

/-- **`Shim.makes_infinite`** (A4): an engine whose IEEE operations are the
reference's (D31; `polars-ieee-arith-*`, spark-double-arith) flags a row
exactly where the reference's overflow to `±∞` does (`BinFn.infIssue`). -/
theorem makes_infinite (f : BinFn) (hf : f.makesInf = true) (a b : Int) :
    makesInfinite (match (f.apply (.float a) (.float b)) with | .float r => r | _ => 0) [a, b] =
      (f.infIssue (.float a) (.float b)).isSome := by
  have hf' : f = .fadd ∨ f = .fsub ∨ f = .fmul ∨ f = .fdiv ∨ f = .fpow := by
    cases f <;> simp_all [BinFn.makesInf]
  rcases hf' with rfl | rfl | rfl | rfl | rfl <;>
    simp [BinFn.infIssue, makesInfinite, BinFn.apply, BinFn.makesInf, Bool.and_assoc] <;>
    split <;> simp_all

end Substrait.Shim
