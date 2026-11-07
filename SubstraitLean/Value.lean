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

/-- A value, tagged by its kind (#923): a function applied to a value of
the wrong kind is a non-matching pattern. Doubles are their codes
(`SubstraitLean/Float.lean`), dates days since 1970-01-01, timestamps
(`ts`, with or without a time zone) and times of day (`tod`) microseconds,
decimals their unscaled integer at their scale. A struct is its fields in
order. -/
inductive Value where
  | null
  | bool (b : Bool)
  | int (i : Int)
  /-- A double, as its code (`FloatCode`). -/
  | float (c : Int)
  /-- A `DATE`: days since 1970-01-01. -/
  | date (days : Int)
  /-- A `TIMESTAMP`: microseconds since 1970-01-01. -/
  | ts (micros : Int)
  /-- A `TIME`: microseconds since midnight. -/
  | tod (micros : Int)
  /-- A `DECIMAL` of scale `scale`: `unscaled / 10 ^ scale`. -/
  | dec (scale : Nat) (unscaled : Int)
  | str (s : String)
  | list (vs : List Value)
  | struct (vs : List Value)
  deriving Repr, Inhabited

mutual
def Value.decEq : (a b : Value) → Decidable (a = b)
  | .null, .null => isTrue rfl
  | .bool a, .bool b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .int a, .int b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .float a, .float b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .date a, .date b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .ts a, .ts b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .tod a, .tod b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .dec s a, .dec t b =>
    if h : s = t ∧ a = b then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
    else isFalse (by simp only [Value.dec.injEq]; exact h)
  | .str a, .str b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .list as, .list bs => match Value.decEqList as bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by simp [h])
  | .struct as, .struct bs => match Value.decEqList as bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by simp [h])
  | .null, .bool _ | .null, .int _ | .null, .float _ | .null, .date _ | .null, .ts _
  | .null, .tod _ | .null, .dec _ _ | .null, .str _ | .null, .list _ | .null, .struct _
  | .bool _, .null | .bool _, .int _ | .bool _, .float _ | .bool _, .date _ | .bool _, .ts _
  | .bool _, .tod _ | .bool _, .dec _ _ | .bool _, .str _ | .bool _, .list _
  | .bool _, .struct _ | .int _, .null | .int _, .bool _ | .int _, .float _ | .int _, .date _
  | .int _, .ts _ | .int _, .tod _ | .int _, .dec _ _ | .int _, .str _ | .int _, .list _
  | .int _, .struct _ | .float _, .null | .float _, .bool _ | .float _, .int _
  | .float _, .date _ | .float _, .ts _ | .float _, .tod _ | .float _, .dec _ _
  | .float _, .str _ | .float _, .list _ | .float _, .struct _ | .date _, .null
  | .date _, .bool _ | .date _, .int _ | .date _, .float _ | .date _, .ts _ | .date _, .tod _
  | .date _, .dec _ _ | .date _, .str _ | .date _, .list _ | .date _, .struct _ | .ts _, .null
  | .ts _, .bool _ | .ts _, .int _ | .ts _, .float _ | .ts _, .date _ | .ts _, .tod _
  | .ts _, .dec _ _ | .ts _, .str _ | .ts _, .list _ | .ts _, .struct _ | .tod _, .null
  | .tod _, .bool _ | .tod _, .int _ | .tod _, .float _ | .tod _, .date _ | .tod _, .ts _
  | .tod _, .dec _ _ | .tod _, .str _ | .tod _, .list _ | .tod _, .struct _ | .dec _ _, .null
  | .dec _ _, .bool _ | .dec _ _, .int _ | .dec _ _, .float _ | .dec _ _, .date _
  | .dec _ _, .ts _ | .dec _ _, .tod _ | .dec _ _, .str _ | .dec _ _, .list _
  | .dec _ _, .struct _ | .str _, .null | .str _, .bool _ | .str _, .int _ | .str _, .float _
  | .str _, .date _ | .str _, .ts _ | .str _, .tod _ | .str _, .dec _ _ | .str _, .list _
  | .str _, .struct _ | .list _, .null | .list _, .bool _ | .list _, .int _ | .list _, .float _
  | .list _, .date _ | .list _, .ts _ | .list _, .tod _ | .list _, .dec _ _ | .list _, .str _
  | .list _, .struct _ | .struct _, .null | .struct _, .bool _ | .struct _, .int _
  | .struct _, .float _ | .struct _, .date _ | .struct _, .ts _ | .struct _, .tod _
  | .struct _, .dec _ _ | .struct _, .str _ | .struct _, .list _ =>
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

/-! ## Column kinds

Doubles, timestamps and dates all become integers in the model (see
`SubstraitLean/Float.lean`); the parser and the writer track which is which,
and `Rel.inferKinds` (`SubstraitLean/Kinds.lean`) checks it. -/

inductive Kind where
  /-- `tod`: a time of day (`TIME`), in microseconds since midnight. -/
  | int | float | time | date | str | bool | tod | other
  /-- A timestamp with a time zone: an instant, whose calendar arithmetic is
  daylight-saving-aware in DataFusion, so it is refused. -/
  | timeTz
  /-- A list of values of the element kind. -/
  | list (elem : Kind)
  /-- A struct of fields of these kinds, in order. Its value is the list of
  its fields (`docs/nested-values.md`). -/
  | struct (fields : List Kind)
  /-- `DECIMAL(p, s)`, as its unscaled integer (#27). -/
  | dec (p s : Nat)
  deriving Repr, BEq, Inhabited

mutual
/-- `DecidableEq` by hand: the deriving handler does not take the list in
`struct` (as for `Value.decEq`). -/
def Kind.decEq : (a b : Kind) → Decidable (a = b)
  | .int, .int => isTrue rfl
  | .float, .float => isTrue rfl
  | .time, .time => isTrue rfl
  | .date, .date => isTrue rfl
  | .str, .str => isTrue rfl
  | .bool, .bool => isTrue rfl
  | .tod, .tod => isTrue rfl
  | .other, .other => isTrue rfl
  | .timeTz, .timeTz => isTrue rfl
  | .list a, .list b => match Kind.decEq a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by simp [h])
  | .struct as, .struct bs => match Kind.decEqList as bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by simp [h])
  | .dec p s, .dec q t =>
    if h : p = q ∧ s = t then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
    else isFalse (by simp only [Kind.dec.injEq]; exact h)
  | .int, .float | .int, .time | .int, .date | .int, .str | .int, .bool | .int, .tod
  | .int, .other | .int, .timeTz | .int, .list _ | .int, .struct _ | .int, .dec _ _
  | .float, .int | .float, .time | .float, .date | .float, .str | .float, .bool | .float, .tod
  | .float, .other | .float, .timeTz | .float, .list _ | .float, .struct _ | .float, .dec _ _
  | .time, .int | .time, .float | .time, .date | .time, .str | .time, .bool | .time, .tod
  | .time, .other | .time, .timeTz | .time, .list _ | .time, .struct _ | .time, .dec _ _
  | .date, .int | .date, .float | .date, .time | .date, .str | .date, .bool | .date, .tod
  | .date, .other | .date, .timeTz | .date, .list _ | .date, .struct _ | .date, .dec _ _
  | .str, .int | .str, .float | .str, .time | .str, .date | .str, .bool | .str, .tod
  | .str, .other | .str, .timeTz | .str, .list _ | .str, .struct _ | .str, .dec _ _
  | .bool, .int | .bool, .float | .bool, .time | .bool, .date | .bool, .str | .bool, .tod
  | .bool, .other | .bool, .timeTz | .bool, .list _ | .bool, .struct _ | .bool, .dec _ _
  | .tod, .int | .tod, .float | .tod, .time | .tod, .date | .tod, .str | .tod, .bool
  | .tod, .other | .tod, .timeTz | .tod, .list _ | .tod, .struct _ | .tod, .dec _ _
  | .other, .int | .other, .float | .other, .time | .other, .date | .other, .str | .other, .bool
  | .other, .tod | .other, .timeTz | .other, .list _ | .other, .struct _ | .other, .dec _ _
  | .timeTz, .int | .timeTz, .float | .timeTz, .time | .timeTz, .date | .timeTz, .str
  | .timeTz, .bool | .timeTz, .tod | .timeTz, .other | .timeTz, .list _ | .timeTz, .struct _
  | .timeTz, .dec _ _ | .list _, .int | .list _, .float | .list _, .time | .list _, .date
  | .list _, .str | .list _, .bool | .list _, .tod | .list _, .other | .list _, .timeTz
  | .list _, .struct _ | .list _, .dec _ _ | .struct _, .int | .struct _, .float
  | .struct _, .time | .struct _, .date | .struct _, .str | .struct _, .bool | .struct _, .tod
  | .struct _, .other | .struct _, .timeTz | .struct _, .list _ | .struct _, .dec _ _
  | .dec _ _, .int | .dec _ _, .float | .dec _ _, .time | .dec _ _, .date | .dec _ _, .str
  | .dec _ _, .bool | .dec _ _, .tod | .dec _ _, .other | .dec _ _, .timeTz | .dec _ _, .list _
  | .dec _ _, .struct _ =>
    isFalse (by simp)

def Kind.decEqList : (as bs : List Kind) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by simp)
  | a :: as, b :: bs => match Kind.decEq a b, Kind.decEqList as bs with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (by simp [h])
    | _, isFalse h' => isFalse (by simp [h'])
end

instance : DecidableEq Kind := Kind.decEq

/-- Decimals of any type and integers compare as numbers: `decimalCall`
brings them to one scale. -/
def Kind.numeric : Kind → Kind
  | .dec _ _ => .int
  | k => k


end Substrait
