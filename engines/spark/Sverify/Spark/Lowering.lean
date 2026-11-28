import Sverify.Engines.LoweringExport
import Sverify.Spark.LoweringOn.Table

/-!
# The generated lowering to Spark (#271)

The table for Spark's profile, `sparkOn`, is generated: the search
(`generate_lowering`, `engines/Sverify/Engines/LoweringSearch.lean`) runs in
`scripts/RegenLoweringSpark.lean` (`poe regen-lowering`) and writes each entry
it found, with its proof, to `engines/spark/Sverify/Spark/LoweringOn`, which a
build checks without searching. Where `Profile.spark` differs from the
reference, an entry is a template over Spark's functions
(`Sverify.Spark.LoweringSchemas`); elsewhere the native function.

Two kinds of entry are not exact on every value (rulings 249 and 254), and
the flags say which (`Lowering.spark_exact_except`, `Lowering.spark_onDbl_only`):

* IEEE division is `/`'s entry, which raises at a zero divisor of either sign,
  as Spark does under ANSI (`spark.sql.ansi.enabled`, `sverify_spark.dialect.SPARK_CONF`,
  fact spark-double-divide), where IEEE gives `±∞`: it agrees with the
  reference or raises.
* `floor` and `ceil` give a `BIGINT` on Spark, which raises past `2⁶³`: their
  template passes doubles of `2⁵²` or more through, exact on doubles' codes.

`power` and `atan2` of doubles are Java's, within an ulp of C's: the table is
partial, and `Lowering.lowerRel?` refuses a plan that calls them, naming them.
So the soundness (`Rel.spark_lowered_sound`) is `Lowering.lowerRel?_sound_dbl`:
on a catalog of doubles, for a plan whose constants are doubles.

`Engine.spark` runs the plan this table lowers (`Spark/Engine.lean`), and the
writer reads its templates (`--lowering-table`, `SparkDialect.lowered`).
`ftod`, a double to a decimal, is refused here (`refusing`, ruling 278): Spark's
own cast rounds the double's shortest text (`1.005` to `1.01`), the reference the
product `x · 10ˢ`, and `Profile.spark` states it only within one unit. The writer
keeps the dialect's `decimal_cast`, which rounds the product.
-/

namespace Substrait

variable [Boxes.Ambient]

/-- The generated lowering to Spark. -/
def Lowering.spark : Lowering Profile.spark := sparkOn

/-- **The entries that are not exact** (ruling 250, J1): IEEE division alone. -/
theorem Lowering.spark_exact_except :
    (∀ f, (Lowering.spark.un f).all (·.exact) = true) ∧
      ∀ f, (Lowering.spark.bin f).all (·.exact) = true ∨ f = .fdivIeee :=
  ⟨fun f => by cases f <;> repeat (first | rfl | (rename_i a; cases a)),
   fun f => by cases f <;> repeat (first | exact .inl rfl | exact .inr rfl | (rename_i a; cases a))⟩

/-- **The entries stated on doubles only** (ruling 254, M1): `floor` and `ceil`. -/
theorem Lowering.spark_onDbl_only :
    (∀ f, (Lowering.spark.un f).all (!·.onDbl) = true ∨ f = .ffloor ∨ f = .fceil) ∧
      ∀ f, (Lowering.spark.bin f).all (!·.onDbl) = true :=
  ⟨fun f => by
     cases f <;> repeat (first | exact .inl rfl | exact .inr (.inl rfl) | exact .inr (.inr rfl) |
       (rename_i a; cases a)),
   fun f => by cases f <;> repeat (first | rfl | (rename_i a; cases a))⟩

/-- The table has no entry for `power` and `atan2` of doubles. -/
theorem Lowering.spark_refuses :
    Lowering.spark.bin .fpow = none ∧ Lowering.spark.bin .fatan2 = none := ⟨rfl, rfl⟩

/-- **The lowered plan runs correctly on Spark, or raises.** A plan the table
lowers (`Lowering.lowerRel?`) gives `Rel.eval`'s rows under Spark's functions,
on a catalog of doubles, for a plan whose constants are doubles, unless one of
its expressions raises on a row Spark evaluates it on. Trusted: that
`Profile.spark` is Spark's under `SPARK_CONF` (ANSI on), and that the
translation writes each template's functions as Spark's. -/
theorem Rel.spark_lowered_sound {cat : Catalog} (hcat : cat.Dbl) {r r' : Rel} (hc : r.ConstsDbl)
    (hr : Lowering.spark.lowerRel? r = .ok r') (h : ¬r'.Raises Profile.spark cat) :
    r'.eval cat Profile.spark.impl = r.eval cat :=
  Lowering.lowerRel?_sound_dbl hcat hc hr h

/-! ## True where reached (ruling 290)

`Profile.spark` keeps the reference's casts of a double to `BIGINT` at `2⁶³`, where Spark
saturates (`Spark.ftoiExcepted`, spark-cast-double-to-int). The table's entries for them
are the guarded templates (`Spark.ftoiEntry`, `Spark.ftoiOrNullEntry`), whose native cast
is reached only below `2⁶³` (`Spark.ftoi_native_not_excepted`), and no other entry calls
them: a regeneration that drops `excluding [UnFn.ftoi, UnFn.ftoiOrNull]`
(`scripts/RegenLoweringSpark.lean`) fails here; that no other entry calls them is
`Spark/Engine.lean`'s guard (P4). -/

#guard letI := Boxes.Ambient.none
  (Lowering.spark.un .ftoi).any (·.tmpl == Spark.ftoiTemplate) &&
    (Lowering.spark.un .ftoiOrNull).any (·.tmpl == Spark.ftoiOrNullTemplate)

/-! ## Tests (rulings 248 G6, 249 H5)

The entries evaluated under `Profile.spark` beside the reference's outcome. -/

/-- The entry's outcome and the reference's, as a check: the same value, or
both raise (`exact`), or the entry raises (`AgreeOrRaises`). -/
def Spark.checkOutcome (exact : Bool) : Outcome → Outcome → Bool
  | .ok v, .ok w => v == w
  | .error _, .error _ => true
  | .error _, .ok _ => !exact
  | .ok _, .error _ => false

-- `floor` and `ceil` at NaN, `±∞`, `±0`, `-0.5`, `2⁵² ± 1`, `2⁶³` and the largest
-- double: exact, on doubles' codes.
#guard letI := Boxes.Ambient.none
  [0.0 / 0.0, 1.0 / 0.0, -1.0 / 0.0, 0.0, -0.0, -0.5, 4503599627370497.0, 4503599627370495.0,
    -4503599627370497.0, 9223372036854775808.0, -9223372036854775808.0,
    1.7976931348623157e308, -1.7976931348623157e308].all fun (x : Float) =>
    let v := Value.float (FloatCode.ofFloat x)
    Spark.checkOutcome true (Spark.ffloorEntry.tmpl.evalP Profile.spark [v]) (Profile.reference.un .ffloor v) &&
    Spark.checkOutcome true (Spark.fceilEntry.tmpl.evalP Profile.spark [v]) (Profile.reference.un .fceil v)

-- The casts to `BIGINT` at the 64-bit edges (spark-cast-double-to-int's probe): `2⁶³`, the
-- doubles beside it and beside `-2⁶³`, NaN, `±∞`, `-0.0`: exact.
#guard letI := Boxes.Ambient.none
  [9223372036854775808.0, 9223372036854777856.0, 9223372036854774784.0, -9223372036854775808.0,
    -9223372036854777856.0, -9223372036854774784.0, 0.0 / 0.0, 1.0 / 0.0, -1.0 / 0.0, -0.0, -1.5,
    2.5].all fun (x : Float) =>
    let v := Value.float (FloatCode.ofFloat x)
    Spark.checkOutcome true (Spark.ftoiEntry.tmpl.evalP Profile.spark [v]) (Profile.reference.un .ftoi v) &&
    Spark.checkOutcome true (Spark.ftoiOrNullEntry.tmpl.evalP Profile.spark [v])
      (Profile.reference.un .ftoiOrNull v)

-- IEEE division: a zero divisor of either sign raises, for a finite, infinite or
-- NaN dividend; a divisor that is not zero gives the reference's value, NaN and
-- `±∞` operands included.
#guard letI := Boxes.Ambient.none
  let en := sparkOn.fdivIeee
  let xs : List Float := [1.5, -2.0, 0.0, -0.0, 1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0]
  xs.all fun a => [0.0, -0.0].all fun b =>
    match en.tmpl.evalP Profile.spark [.float (FloatCode.ofFloat a), .float (FloatCode.ofFloat b)] with
    | .error _ => true
    | .ok _ => false
#guard letI := Boxes.Ambient.none
  let en := sparkOn.fdivIeee
  let xs : List Float := [1.5, -2.0, 0.0, -0.0, 1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0, 1e308]
  xs.all fun a => [2.0, -0.5, 1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0, 1e-308].all fun b =>
    let x := Value.float (FloatCode.ofFloat a)
    let y := Value.float (FloatCode.ofFloat b)
    Spark.checkOutcome true (en.tmpl.evalP Profile.spark [x, y]) (Profile.reference.bin .fdivIeee x y)

/-- The Spark table, exported: its entries that are not the native call. -/
def Lowering.sparkTableJson : Lean.Json := LoweringExport.tableJson sparkOn

end Substrait
