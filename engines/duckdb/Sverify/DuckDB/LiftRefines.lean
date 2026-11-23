import Sverify.DuckDB.LiftSearch
import Sverify.DuckDB.Lift.Reference.Table

/-!
# The reference's lift refines DuckDB's SQL (#2008, D54)

D54 promises that SQL lifted under `semantics="reference"`, the default, means
DuckDB's value wherever the reference gives one. The lift's entries
(`liftReference`, generated) prove each template is the reference's meaning of
its DuckDB function (`LiftEntry.agree`). This module proves the other half:
where the reference's meaning of a DuckDB function gives a value, DuckDB's
gives the same (`DuckFn.reference_refines_duckdb`), for every function the
reference does not refuse. So a lifted template that gives a value gives
DuckDB's (`LiftEntry.refines_duckdb`), for every entry of `liftReference`
(`liftReference_refines_duckdb`).

The proof is function by function. `Profile.duckdb` is a diff against the
reference (`duckBin`, `duckUn`), and on the functions the lift's meanings use
(`+ - * / %` and `power` of doubles, the elementary functions, `CAST(BIGINT AS
DOUBLE)`) it differs only where the reference raises (`DuckDBSQL.duck_bin_of_ref`,
`duck_un_of_ref`). `sign`, `greatest`, `least` and the cast of a `BIGINT` mean
the same under both, and the casts of a rounded double agree by
`duck_rounded_float`. `CAST(DOUBLE AS BIGINT)` is refused under both: DuckDB
rounds half to even (D55), which the model's casts cannot state until #322.
-/

namespace Substrait

open scoped Substrait.DuckDB

/-- The binary functions of doubles the lift's meanings use. -/
def BinFn.liftDouble : BinFn → Bool
  | .fadd | .fsub | .fmul | .fdiv | .fmod | .fpow => true
  | _ => false

/-- **DuckDB's binary function gives the reference's value wherever the
reference gives one**, on the functions of doubles the lift uses. -/
theorem DuckDBSQL.duck_bin_of_ref {f : BinFn} (hf : f.liftDouble = true) {v w x : Value}
    (h : Profile.reference.bin f v w = .ok x) : (Profile.duckdb {}).bin f v w = .ok x := by
  have hon : f.onFloats = true := by cases f <;> simp_all [BinFn.liftDouble, BinFn.onFloats]
  cases v <;> cases w <;> simp only [Profile.duckdb, hon, ite_true] <;> try exact h
  rename_i a b
  have h' := h
  cases f <;> simp only [BinFn.liftDouble, Bool.false_eq_true] at hf <;> simp only [duckBin] <;>
    simp only [DuckDBSQL.ref_fadd_float, DuckDBSQL.ref_fsub_float, DuckDBSQL.ref_fmul_float,
      DuckDBSQL.ref_fdiv_float, DuckDBSQL.ref_fmod_float, DuckDBSQL.ref_fpow_float] at h' <;>
    repeat' split
  all_goals first | (simp_all; done) | simpa using h

/-- **DuckDB's unary function gives the reference's value wherever the
reference gives one**, but for `round`, `round_even` and `ceil`, whose zero's sign DuckDB
keeps (`canon_duck_rounded`). The statement is narrowed at `froundEven` (D55), where it is false:
DuckDB's `round_even` of a negative value that rounds to zero is `-0.0`. -/
theorem DuckDBSQL.duck_un_of_ref {f : UnFn} (hf : f ≠ .fround ∧ f ≠ .fceil ∧ f ≠ .froundEven) {v x : Value}
    (h : Profile.reference.un f v = .ok x) : (Profile.duckdb {}).un f v = .ok x := by
  cases v <;> simp only [Profile.duckdb] <;> try exact h
  rename_i c
  cases f <;> simp only [duckUn, Option.getD_none] <;> try exact h
  case fmath g =>
    rw [DuckDBSQL.ref_fmath_float] at h
    split
    · rename_i hn; simp_all
    · simp only [Option.getD_none]; rw [DuckDBSQL.ref_fmath_float]; exact h
  all_goals simp_all

/-- A unary step keeps the refinement. -/
theorem DuckDBSQL.evalP_un_of_ref {f : UnFn} (hf : f ≠ .fround ∧ f ≠ .fceil ∧ f ≠ .froundEven) {a : Expr} {row : Row}
    (ha : ∀ x, a.evalP Profile.reference row = .ok x → a.evalP (Profile.duckdb {}) row = .ok x)
    {x : Value} (h : (Expr.un f a).evalP Profile.reference row = .ok x) :
    (Expr.un f a).evalP (Profile.duckdb {}) row = .ok x := by
  simp only [Expr.evalP] at h ⊢
  cases hr : a.evalP Profile.reference row with
  | error e => rw [hr] at h; cases h
  | ok y =>
    rw [hr] at h; rw [ha y hr]
    exact DuckDBSQL.duck_un_of_ref hf h

/-- A binary step keeps the refinement. -/
theorem DuckDBSQL.evalP_bin_of_ref {f : BinFn} (hf : f.liftDouble = true) {a b : Expr} {row : Row}
    (ha : ∀ x, a.evalP Profile.reference row = .ok x → a.evalP (Profile.duckdb {}) row = .ok x)
    (hb : ∀ x, b.evalP Profile.reference row = .ok x → b.evalP (Profile.duckdb {}) row = .ok x)
    {x : Value} (h : (Expr.bin f a b).evalP Profile.reference row = .ok x) :
    (Expr.bin f a b).evalP (Profile.duckdb {}) row = .ok x := by
  simp only [Expr.evalP] at h ⊢
  cases hra : a.evalP Profile.reference row with
  | error e => rw [hra] at h; cases h
  | ok y =>
    cases hrb : b.evalP Profile.reference row with
    | error e => rw [hra, hrb] at h; cases h
    | ok z =>
      rw [hra, hrb] at h; rw [ha y hra, hb z hrb]
      exact DuckDBSQL.duck_bin_of_ref hf h

theorem DuckDBSQL.evalP_field_of_ref (i : Nat) (row : Row) :
    ∀ x, (Expr.field i).evalP Profile.reference row = .ok x →
      (Expr.field i).evalP (Profile.duckdb {}) row = .ok x := fun _ h => h

theorem DuckType.haveAll_one {t : DuckType} {xs : List Value} (h : DuckType.HaveAll [t] xs) :
    ∃ a, xs = [a] ∧ t.Has a := by
  rcases xs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp_all [DuckType.HaveAll]

theorem DuckType.haveAll_two {t u : DuckType} {xs : List Value} (h : DuckType.HaveAll [t, u] xs) :
    ∃ a b, xs = [a, b] := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp_all [DuckType.HaveAll]

/-- **The reference's reading of a DuckDB function refines DuckDB's** (#2008):
for a function the reference does not refuse, on arguments of its types, a
value the reference gives is DuckDB's. -/
theorem DuckFn.reference_refines_duckdb {f : DuckFn} (hr : f.refused .reference = none)
    {xs : List Value} (hx : DuckType.HaveAll f.args xs) {v : Value}
    (h : DuckFn.eval .reference f xs = .ok v) : DuckFn.eval .duckdb f xs = .ok v := by
  have fld := DuckDBSQL.evalP_field_of_ref
  have itof : UnFn.itof ≠ .fround ∧ UnFn.itof ≠ .fceil ∧ UnFn.itof ≠ .froundEven := by decide
  cases f <;> simp only [DuckFn.eval, DuckFn.meaning, Semantics.profile] at h ⊢
  case divInt =>
    exact DuckDBSQL.evalP_bin_of_ref rfl (fun _ => DuckDBSQL.evalP_un_of_ref itof (fld 0 xs))
      (fun _ => DuckDBSQL.evalP_un_of_ref itof (fld 1 xs)) h
  case divDouble => exact DuckDBSQL.evalP_bin_of_ref rfl (fld 0 xs) (fld 1 xs) h
  case modDouble => exact DuckDBSQL.evalP_bin_of_ref rfl (fld 0 xs) (fld 1 xs) h
  case addDouble => exact DuckDBSQL.evalP_bin_of_ref rfl (fld 0 xs) (fld 1 xs) h
  case subDouble => exact DuckDBSQL.evalP_bin_of_ref rfl (fld 0 xs) (fld 1 xs) h
  case mulDouble => exact DuckDBSQL.evalP_bin_of_ref rfl (fld 0 xs) (fld 1 xs) h
  case power => exact DuckDBSQL.evalP_bin_of_ref rfl (fld 0 xs) (fld 1 xs) h
  case elementary g =>
    exact DuckDBSQL.evalP_un_of_ref ⟨by simp, by simp, by simp⟩ (fld 0 xs) h
  case castRoundedBigint r =>
    obtain ⟨a, rfl, ha⟩ := DuckType.haveAll_one hx
    simp only [DuckFn.evalOwn] at h ⊢
    cases a with
    | null => rw [DuckDBSQL.ref_rounded_null] at h; rw [DuckDBSQL.duck_rounded_null]; exact h
    | float c => rw [DuckDBSQL.ref_rounded_float] at h; rw [DuckDBSQL.duck_rounded_float]; exact h
    | _ => simp [DuckType.Has] at ha
  all_goals
    simp only [DuckFn.args] at hx
    first
    | (obtain ⟨a, rfl, _⟩ := DuckType.haveAll_one hx
       cases a <;> simpa [DuckFn.evalOwn] using h)
    | (obtain ⟨a, b, rfl⟩ := DuckType.haveAll_two hx
       cases a <;> cases b <;> simpa [DuckFn.evalOwn] using h)

/-- **A lifted template that gives a value gives DuckDB's**: what an entry of
the reference's lift computes is DuckDB's value of its function wherever it
is a value (D54). -/
theorem LiftEntry.refines_duckdb {f : DuckFn} (E : LiftEntry .reference f)
    (hr : f.refused .reference = none) {xs : List Value} (hx : DuckType.HaveAll f.args xs)
    {v : Value} (h : E.tmpl.evalP Profile.reference xs = .ok v) :
    DuckFn.eval .duckdb f xs = .ok v := by
  have ha := E.agree xs hx
  simp only [h] at ha
  cases he : DuckFn.eval .reference f xs with
  | error _ => rw [he] at ha; exact ha.elim
  | ok w =>
    rw [he] at ha
    exact ha ▸ DuckFn.reference_refines_duckdb hr hx he

/-- **Every entry of the reference's lift refines DuckDB** (#2008): the table
holds no function the reference refuses, so each of its templates, where it
gives a value, gives DuckDB's. -/
theorem liftReference_refines_duckdb {f : DuckFn} {E : LiftEntry .reference f}
    (hE : liftReference.entry f = some E) {xs : List Value} (hx : DuckType.HaveAll f.args xs)
    {v : Value} (h : E.tmpl.evalP Profile.reference xs = .ok v) :
    DuckFn.eval .duckdb f xs = .ok v := by
  have hr : f.refused .reference = none := by
    cases f <;> first | rfl | simp [liftReference] at hE
  exact E.refines_duckdb hr hx h

end Substrait
