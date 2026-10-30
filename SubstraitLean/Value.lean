/-!
# Values, rows and relations

A deliberately small model of Substrait's type system: nullable booleans,
64-bit-ish integers (modelled as unbounded `Int`) and strings. Every type is
nullable, mirroring Substrait's `NULLABILITY_NULLABLE`.

Relations use **bag semantics**: a relation is a `List Row`, and two relations
are considered equal as bags when they are permutations of each other
(`List.Perm`, written `~`).
-/

namespace Substrait

inductive Value where
  | null
  | bool (b : Bool)
  | int (i : Int)
  | str (s : String)
  deriving Repr, DecidableEq, Inhabited

/-- A row is a positional tuple; Substrait addresses fields by ordinal. -/
abbrev Row := List Value

/-- A relation is a bag of rows. -/
abbrev Relation := List Row

/-- SQL/Substrait filters keep a row only when the predicate is *true*
(not false, not null). -/
def Value.isTrue : Value → Bool
  | .bool true => true
  | _ => false

end Substrait
