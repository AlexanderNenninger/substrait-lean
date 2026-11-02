import SubstraitLean.LoweringSearch

/-!
# The generated lowering to DuckDB (#241)

`generate_lowering` builds a table for DuckDB's profile under each setting of
`error_on_division_by_zero`. Every function is native but division and modulus
by zero with the setting off, where the search finds the guard
`CASE WHEN x IS NOT NULL AND y = 0 THEN error() ELSE x / y END`.

`duckdb_lower_eq_shim` shows the generated lowering is the hand-written shim
`shimDuckDB`, so its correctness (`shimDuckDB_correct`, `Rel.duckdb_shim_sound`)
now follows from the generic theorems of `SubstraitLean/Lowering.lean`.
`duckdbOff.coverage` and `duckdbOn.coverage` list how each construct is lowered.
-/

namespace Substrait

generate_lowering duckdbOff : Profile.duckdb { errorOnDivZero := false }
  unfolding [Profile.duckdb, BinFn.divides, duckDivZero]

generate_lowering duckdbOn : Profile.duckdb { errorOnDivZero := true }
  unfolding [Profile.duckdb, BinFn.divides, duckDivZero]

/-- The generated lowering to DuckDB under settings `s`. -/
def Lowering.duckdb : (s : DuckDBSettings) → Lowering (Profile.duckdb s)
  | { errorOnDivZero := false } => duckdbOff
  | { errorOnDivZero := true } => duckdbOn

theorem Lowering.duckdb_total : ∀ s, (Lowering.duckdb s).Total
  | { errorOnDivZero := false } => duckdbOff.total
  | { errorOnDivZero := true } => duckdbOn.total

theorem Lowering.duckdb_un_tmpl (s : DuckDBSettings) (f : UnFn) :
    ((Lowering.duckdb s).un f).map (·.tmpl) = some (.un f (.field 0)) := by
  obtain ⟨_ | _⟩ := s <;> cases f <;> rfl

theorem Lowering.duckdb_bin_tmpl (s : DuckDBSettings) (f : BinFn) :
    ((Lowering.duckdb s).bin f).map (·.tmpl) = some (if f.divides && !s.errorOnDivZero then
      .ifThen (.bin .and (.un .isNum (.field 0)) (.bin .eq (.field 1) (.lit (.int 0))))
        (.un (.raise "division by zero") (.field 1)) (.bin f (.field 0) (.field 1))
      else .bin f (.field 0) (.field 1)) := by
  obtain ⟨_ | _⟩ := s <;> cases f <;> rfl

/-- **The generated lowering is the hand-written shim.** -/
theorem duckdb_lower_eq_shim (s : DuckDBSettings) : ∀ e, (Lowering.duckdb s).lower e = shimDuckDB s e
  | .lit _ | .field _ => rfl
  | .un f a => by
    have h := Lowering.duckdb_un_tmpl s f
    cases hf : (Lowering.duckdb s).un f with
    | none => simp [hf] at h
    | some en =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      simp only [Lowering.lower, shimDuckDB, hf, ← duckdb_lower_eq_shim s a]
      cases (Lowering.duckdb s).lower a <;> simp [bind, h, Expr.subst]
  | .bin f a b => by
    have h := Lowering.duckdb_bin_tmpl s f
    cases hf : (Lowering.duckdb s).bin f with
    | none => simp [hf] at h
    | some en =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      simp only [Lowering.lower, shimDuckDB, hf, ← duckdb_lower_eq_shim s a,
        ← duckdb_lower_eq_shim s b]
      cases (Lowering.duckdb s).lower a <;> cases (Lowering.duckdb s).lower b <;>
        simp only [bind, Option.bind_some, Option.bind_none, h] <;> split <;> rfl
  | .ifThen c t e => by
    simp only [Lowering.lower, shimDuckDB, duckdb_lower_eq_shim s c, duckdb_lower_eq_shim s t,
      duckdb_lower_eq_shim s e]
  | .hof f l b => by
    simp only [Lowering.lower, shimDuckDB, duckdb_lower_eq_shim s l, duckdb_lower_eq_shim s b]

/-- **DuckDB's shim is correct:** the shimmed expression, run under DuckDB's
profile with settings `s`, has the reference's outcome: the same value, or an
error. -/
theorem shimDuckDB_correct (s : DuckDBSettings) (e t : Expr) (h : shimDuckDB s e = some t)
    (row : Row) : Outcome.Agree (t.evalP (Profile.duckdb s) row) (e.evalP Profile.reference row) :=
  (Lowering.duckdb s).lower_correct e t ((duckdb_lower_eq_shim s e).trans h) row

/-- The shim of an expression (it always has one). -/
def shimE (s : DuckDBSettings) (e : Expr) : Expr := (Lowering.duckdb s).lowerE e

/-- **Every shimmed expression is exact on DuckDB.** -/
theorem shimE_exact (s : DuckDBSettings) (e : Expr) : Expr.Exact (Profile.duckdb s) (shimE s e) e :=
  Lowering.lowerE_exact (Lowering.duckdb_total s) e

/-- DuckDB's shim of a plan: every expression shimmed. -/
def shimRel (s : DuckDBSettings) (r : Rel) : Rel := (Lowering.duckdb s).lowerRel r

/-- **The shimmed plan runs correctly on DuckDB, or raises.** Unless one of
its expressions raises on a row DuckDB evaluates it on, DuckDB's functions
give `Rel.eval`'s rows, on every catalog and under any settings: no contract
and no guard elimination needed. Trusted, as for `Rel.duckdb_sound`: that
`Profile.duckdb` is DuckDB's, and that the SQL printer is faithful. -/
theorem Rel.duckdb_shim_sound (s : DuckDBSettings) {cat : Catalog} {r : Rel}
    (h : ¬(shimRel s r).Raises (Profile.duckdb s) cat) :
    (shimRel s r).evalI (Profile.duckdb s).impl cat = r.eval cat :=
  Lowering.lowerRel_sound (Lowering.duckdb_total s) h

end Substrait
