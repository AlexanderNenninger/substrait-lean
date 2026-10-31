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
  | list (vs : List Value)
  deriving Repr, Inhabited

mutual
def Value.decEq : (a b : Value) → Decidable (a = b)
  | .null, .null => isTrue rfl
  | .bool a, .bool b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .int a, .int b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .str a, .str b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .list as, .list bs => match Value.decEqList as bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by simp [h])
  | .null, .bool _ | .null, .int _ | .null, .str _ | .null, .list _
  | .bool _, .null | .bool _, .int _ | .bool _, .str _ | .bool _, .list _
  | .int _, .null | .int _, .bool _ | .int _, .str _ | .int _, .list _
  | .str _, .null | .str _, .bool _ | .str _, .int _ | .str _, .list _
  | .list _, .null | .list _, .bool _ | .list _, .int _ | .list _, .str _ =>
    isFalse (by simp)

def Value.decEqList : (as bs : List Value) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by simp)
  | a :: as, b :: bs => match Value.decEq a b, Value.decEqList as bs with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (by simp [h])
    | _, isFalse h' => isFalse (by simp [h'])
end

instance : DecidableEq Value := Value.decEq

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
