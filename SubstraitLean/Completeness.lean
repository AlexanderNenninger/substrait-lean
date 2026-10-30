import SubstraitLean.Rel

/-!
# Completeness: nothing that should be in the result is lost

Contracts prove that every output row is good. Completeness is the converse:
every row that *should* be there is there. For filters, projections and
joins this follows from membership lemmas, one per operator, which compose
into a proof for a whole pipeline.

`window_complete` is the IoT example: if both sensors have valid readings at
`t` and `t + 60`, the window starting at `t` is in the output. Together with
the incremental theorems (the maintained view equals recomputation), a
window appears as soon as its data is present, including late data.
-/

namespace Substrait

open Rel

theorem mem_read {cat : Catalog} {t : String} {row : Row} (h : row ∈ (cat t).rows) :
    row ∈ (read t).eval cat := h

theorem mem_filter {cat : Catalog} {r : Rel} {c : Expr} {row : Row} (h : row ∈ r.eval cat)
    (hc : (c.eval row).isTrue = true) : row ∈ (filter r c).eval cat :=
  List.mem_filter.mpr ⟨h, hc⟩

theorem mem_project {cat : Catalog} {r : Rel} {es : List Expr} {row : Row} (h : row ∈ r.eval cat) :
    row ++ es.map (·.eval row) ∈ (project r es).eval cat :=
  List.mem_map.mpr ⟨row, h, rfl⟩

theorem mem_emit {cat : Catalog} {r : Rel} {m : List Nat} {row : Row} (h : row ∈ r.eval cat) :
    m.map (row.getD · .null) ∈ (emit r m).eval cat :=
  List.mem_map.mpr ⟨row, h, rfl⟩

theorem mem_cross {cat : Catalog} {a b : Rel} {x y : Row} (hx : x ∈ a.eval cat)
    (hy : y ∈ b.eval cat) : x ++ y ∈ (cross a b).eval cat :=
  mem_crossRows.mpr ⟨x, hx, y, hy, rfl⟩

theorem mem_join {cat : Catalog} {a b : Rel} {on : Expr} {x y : Row} (hx : x ∈ a.eval cat)
    (hy : y ∈ b.eval cat) (hon : (on.eval (x ++ y)).isTrue = true) :
    x ++ y ∈ (join a b .inner on).eval cat :=
  List.mem_filter.mpr ⟨mem_crossRows.mpr ⟨x, hx, y, hy, rfl⟩, hon⟩

/-! ## The IoT window pipeline -/

namespace IoT

def ERR : Int := -9999
def STEP : Int := 60

/-- `SELECT ts, value FROM t WHERE value <> -9999` -/
def clean (t : String) : Rel :=
  filter (read t) (.un .not (.bin .eq (.field 1) (.lit (.int ERR))))

/-- Both sensors at the same time: `(ts, v1, ts, v2)`. -/
def wide : Rel := join (clean "sensor1") (clean "sensor2") .inner (.bin .eq (.field 0) (.field 2))

/-- Two consecutive timesteps: `(ts, v1, ts, v2, ts + 60, v1', ts + 60, v2')`. -/
def windows : Rel :=
  join wide wide .inner (.bin .eq (.field 4) (.bin .add (.field 0) (.lit (.int STEP))))

theorem clean_mem {cat : Catalog} {s : String} {t v : Int} (h : [.int t, .int v] ∈ (cat s).rows)
    (hv : v ≠ ERR) : [.int t, .int v] ∈ (clean s).eval cat := by
  apply mem_filter (mem_read h)
  have : (v == ERR) = false := by simpa using hv
  simp [Expr.eval, BinFn.apply, UnFn.apply, Value.isTrue, this]

/-- **No window is lost**: valid readings from both sensors at `t` and
`t + 60` produce the window starting at `t`. -/
theorem window_complete {cat : Catalog} {t a₀ b₀ a₁ b₁ : Int}
    (ha₀ : [.int t, .int a₀] ∈ (cat "sensor1").rows) (hb₀ : [.int t, .int b₀] ∈ (cat "sensor2").rows)
    (ha₁ : [.int (t + STEP), .int a₁] ∈ (cat "sensor1").rows)
    (hb₁ : [.int (t + STEP), .int b₁] ∈ (cat "sensor2").rows)
    (va₀ : a₀ ≠ ERR) (vb₀ : b₀ ≠ ERR) (va₁ : a₁ ≠ ERR) (vb₁ : b₁ ≠ ERR) :
    [.int t, .int a₀, .int t, .int b₀,
      .int (t + STEP), .int a₁, .int (t + STEP), .int b₁] ∈ windows.eval cat := by
  have w₀ : [.int t, .int a₀, .int t, .int b₀] ∈ wide.eval cat :=
    mem_join (x := [.int t, .int a₀]) (y := [.int t, .int b₀]) (clean_mem ha₀ va₀) (clean_mem hb₀ vb₀)
      (by simp [Expr.eval, BinFn.apply, Value.isTrue])
  have w₁ : [.int (t + STEP), .int a₁, .int (t + STEP), .int b₁] ∈ wide.eval cat :=
    mem_join (x := [.int (t + STEP), .int a₁]) (y := [.int (t + STEP), .int b₁])
      (clean_mem ha₁ va₁) (clean_mem hb₁ vb₁) (by simp [Expr.eval, BinFn.apply, Value.isTrue])
  exact mem_join (x := [.int t, .int a₀, .int t, .int b₀]) w₀ w₁
    (by simp [Expr.eval, BinFn.apply, Value.isTrue])

end IoT

end Substrait
