import SubstraitLean.Lowering

/-!
# Lemmas the DuckDB lowering's proofs compute with (#241)

The generated modules (`SubstraitLean/LoweringDuckDB/On`) use them;
`scripts/RegenLowering.lean` passes them to the generator (`using`).
-/

namespace Substrait

/-! ### `overflow` = `SILENT` or `SATURATE` (#241)

DuckDB has no function for `UnFn.fit`: its profile computes it as the
reference does, but the SQL printer has nothing to print, so every template
must avoid it (`excluding`). These lemmas let the proofs compute it. -/

theorem Lowering.ref_fit (m : OverflowMode) (w : IntWidth) (x : Value) :
    Profile.reference.un (.fit m w) x = .ok (UnFn.apply (.fit m w) x) := by
  cases x <;> rfl

theorem Lowering.apply_fit_int (m : OverflowMode) (w : IntWidth) (i : Int) :
    UnFn.apply (.fit m w) (.int i) = .int (w.fit m i) := rfl
theorem Lowering.apply_fit_null (m : OverflowMode) (w : IntWidth) :
    UnFn.apply (.fit m w) .null = .null := rfl
theorem Lowering.apply_fit_bool (m : OverflowMode) (w : IntWidth) (b : Bool) :
    UnFn.apply (.fit m w) (.bool b) = .bool b := rfl
theorem Lowering.apply_fit_str (m : OverflowMode) (w : IntWidth) (s : String) :
    UnFn.apply (.fit m w) (.str s) = .str s := rfl
theorem Lowering.apply_fit_list (m : OverflowMode) (w : IntWidth) (vs : List Value) :
    UnFn.apply (.fit m w) (.list vs) = .list vs := rfl

end Substrait
