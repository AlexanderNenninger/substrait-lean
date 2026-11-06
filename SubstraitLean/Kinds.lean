import SubstraitLean.Rel

/-!
# Kinds: a decidable kind checker and its soundness

`Rel.inferKinds` infers each column's `Kind` from the tables' declared
kinds and refuses a plan whose functions do not fit their arguments
(`ftoi` of a timestamp, `+` of a double). `checkPlan` runs it beside
`checkWF`, so the parser is no longer trusted for typing:
`Rel.kinds_sound` proves that a well-kinded plan evaluates to values of the
inferred kinds.

Values are untyped across the integer-represented kinds (doubles, dates,
timestamps, times of day and decimals are all `Value.int`), so
`Value.hasKind` reads a kind by its representation: any integer has every
integer-represented kind. The checker is stricter than that, and its
refusals are by kind; the theorem is about representations until `Value`
has a constructor per kind (#923). NULL has every kind, and `Kind.other`
(a column whose kind the plan does not say) has every value.

Integer literals have no kind of their own (a double literal is its code,
a date literal its days): `KT.num` is such a literal, accepted wherever an
integer-represented kind is.
-/

namespace Substrait

/-- The kinds held as `Value.int`. -/
def Kind.isIntRep : Kind → Bool
  | .int | .float | .time | .date | .tod | .timeTz | .dec _ _ => true
  | _ => false

mutual
/-- Does `v` have kind `k`, by its representation? NULL has every kind. -/
def Value.hasKind : Kind → Value → Bool
  | _, .null => true
  | .other, _ => true
  | .bool, .bool _ => true
  | .str, .str _ => true
  | .list k, .list vs => Value.allHaveKind k vs
  | .struct ks, .list vs => Value.fieldsHaveKinds ks vs
  | k, .int _ => k.isIntRep
  | _, _ => false

def Value.allHaveKind (k : Kind) : List Value → Bool
  | [] => true
  | v :: vs => Value.hasKind k v && Value.allHaveKind k vs

def Value.fieldsHaveKinds : List Kind → List Value → Bool
  | [], [] => true
  | k :: ks, v :: vs => Value.hasKind k v && Value.fieldsHaveKinds ks vs
  | _, _ => false
end

@[simp] theorem Value.hasKind_null (k : Kind) : Value.null.hasKind k = true := by
  cases k <;> rfl

@[simp] theorem Value.hasKind_other (v : Value) : v.hasKind .other = true := by
  cases v <;> rfl

theorem Value.allHaveKind_iff {k : Kind} :
    ∀ {vs : List Value}, Value.allHaveKind k vs = true ↔ ∀ v ∈ vs, v.hasKind k = true
  | [] => by simp [Value.allHaveKind]
  | v :: vs => by simp [Value.allHaveKind, Value.allHaveKind_iff (vs := vs)]

theorem Value.hasKind_list {k : Kind} {vs : List Value} :
    (Value.list vs).hasKind (.list k) = true ↔ ∀ v ∈ vs, v.hasKind k = true := by
  rw [← Value.allHaveKind_iff]; rfl

theorem Value.fieldsHaveKinds_getD :
    ∀ {ks : List Kind} {vs : List Value}, Value.fieldsHaveKinds ks vs = true →
      ∀ i, (vs.getD i .null).hasKind (ks.getD i .other) = true
  | [], [], _, i => by simp
  | k :: ks, v :: vs, h, i => by
    simp only [Value.fieldsHaveKinds, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i => simpa using Value.fieldsHaveKinds_getD h.2 i
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp [Value.fieldsHaveKinds] at h

/-- An integer has every integer-represented kind. -/
theorem Value.hasKind_of_int {k : Kind} (hk : k.isIntRep = true) :
    ∀ {v : Value}, v.hasKind .int = true → v.hasKind k = true
  | .null, _ => by simp
  | .int _, _ => by cases k <;> simp_all [Value.hasKind, Kind.isIntRep]
  | .bool _, h | .str _, h | .list _, h => by simp [Value.hasKind, Kind.isIntRep] at h

/-! ## Kinds of expressions -/

/-- An expression's kind: a `Kind`, or `num`, an integer literal of no
stated kind. -/
inductive KT where
  | kind (k : Kind)
  | num
  deriving DecidableEq, Repr

/-- The kind a column of this expression gets. -/
def KT.toKind : KT → Kind
  | .kind k => k
  | .num => .int

/-- Does `v` have the kind? -/
def KT.has (t : KT) (v : Value) : Bool := v.hasKind t.toKind

/-- Two branches' kind: their own if equal, else unknown. -/
def KT.join (a b : KT) : KT := if a = b then a else .kind .other

/-- Is `t` accepted where `p` describes the integer-represented kinds
taken? A literal integer and an unknown kind are. -/
def KT.okI (p : Kind → Bool) : KT → Bool
  | .num | .kind .other => true
  | .kind k => p k

/-- Is `t` the kind `want` (a string, a boolean, a list), or unknown? -/
def KT.okK (want : Kind) : KT → Bool
  | .kind .other => true
  | .kind k => decide (k = want)
  | .num => false

def Kind.isInt : Kind → Bool
  | .int => true
  | _ => false

def Kind.isFloat : Kind → Bool
  | .float => true
  | _ => false

def Kind.isDate : Kind → Bool
  | .date => true
  | _ => false

def Kind.isTimeOrTod : Kind → Bool
  | .time | .timeTz | .tod => true
  | _ => false

def Kind.isIntOrDec : Kind → Bool
  | .int | .dec _ _ => true
  | _ => false

def Kind.isTime : Kind → Bool
  | .time | .timeTz => true
  | _ => false

def Kind.isDec : Kind → Bool
  | .dec _ _ => true
  | _ => false

/-- Integer-represented kinds that integer arithmetic (`+`, `-`, `×`,
negation, wrapping) applies to: everything but doubles. -/
def Kind.isExactNum : Kind → Bool
  | .int | .time | .date | .tod | .timeTz | .dec _ _ => true
  | _ => false

/-- `t`, unless it is unknown: an integer-represented result of an argument
of unknown kind. -/
def KT.orNum : KT → KT
  | .kind .other => .num
  | t => t

/-- What `f` gives for an argument of kind `t`, if it takes it. -/
def UnFn.kindOf (f : UnFn) (t : KT) : Option KT :=
  let need (c : Bool) (out : KT) : Option KT := if c then some out else none
  match f with
  | .not => need (t.okK .bool) (.kind .bool)
  | .isNull | .isNum => some (.kind .bool)
  | .neg => need (t.okI Kind.isExactNum) t.orNum
  | .itof => need (t.okI Kind.isInt) (.kind .float)
  | .fneg | .ffloor | .fceil | .fround | .froundTo _ | .fmath _ =>
    need (t.okI Kind.isFloat) (.kind .float)
  | .ftoi | .ftoiOrNull => need (t.okI Kind.isFloat) (.kind .int)
  | .narrow _ | .narrowOrNull _ => need (t.okI Kind.isInt) (.kind .int)
  | .wrap _ | .fit _ _ => need (t.okI Kind.isExactNum) t
  | .widen => need (t.okI Kind.isFloat) (if t = .num then .kind .float else t)
  | .itos => need (t.okI Kind.isInt) (.kind .str)
  | .upper | .lower | .reverse | .replace _ _ | .regexExtract _ _ | .regexReplace _ _ _
  | .md5 | .sha256 => need (t.okK .str) (.kind .str)
  | .length | .ascii | .regexMatch _ => need (t.okK .str) (.kind .int)
  | .datePart _ => need (t.okI Kind.isTimeOrTod) (.kind .int)
  | .dateTrunc _ => need (t.okI Kind.isTimeOrTod) t.orNum
  | .toDate => need (t.okI Kind.isTime) (.kind .date)
  | .dayPart _ => need (t.okI Kind.isDate) (.kind .int)
  | .dayTrunc _ | .addMonths _ false => need (t.okI Kind.isDate) (.kind .date)
  | .addMonths _ true | .bucket _ _ => need (t.okI Kind.isTime) (.kind .time)
  | .timeOfDay => need (t.okI Kind.isTime) (.kind .tod)
  | .asTime => need (t.okI Kind.isInt) (.kind .time)
  | .dateTime => need (t.okI Kind.isDate) (.kind .time)
  | .epochUs => need (t.okI Kind.isTime) (.kind .int)
  | .strftime _ => need (t.okI Kind.isTime) (.kind .str)
  | .decimal p s | .dkind p s =>
    need (t.okI Kind.isIntOrDec) (if t = .kind .other then t else .kind (.dec p s))
  | .dround _ | .dtrunc _ => need (t.okI Kind.isIntOrDec) (.kind .int)
  | .ftod _ => need (t.okI Kind.isFloat) (.kind .int)
  | .dtof _ => need (t.okI Kind.isIntOrDec) (.kind .float)
  | .structField i => match t with
    | .kind (.struct ks) => some (.kind (ks.getD i .other))
    | .kind .other => some (.kind .other)
    | _ => none
  | .listElement _ => match t with
    | .kind (.list k) => some (.kind k)
    | .kind .other => some (.kind .other)
    | _ => none
  | .cardinality => match t with
    | .kind (.list _) | .kind .other => some (.kind .int)
    | _ => none
  | .raise _ | .bbox _ => some (.kind .other)

/-- Integer arithmetic's result: the kind that is not a plain integer (a
timestamp plus microseconds is a timestamp). -/
def KT.arith (a b : KT) : KT :=
  match a, b with
  | .kind .other, _ | _, .kind .other => .num
  | .num, b => b
  | .kind .int, b => b
  | a, _ => a

/-- What `f` gives for arguments of kinds `a` and `b`, if it takes them. -/
def BinFn.kindOf (f : BinFn) (a b : KT) : Option KT :=
  let need (c : Bool) (out : KT) : Option KT := if c then some out else none
  let num (p : Kind → Bool) := a.okI p && b.okI p
  match f with
  | .add | .sub | .mul => need (num Kind.isExactNum) (a.arith b)
  | .eq | .lt => some (.kind .bool)
  | .and | .or => need (a.okK .bool && b.okK .bool) (.kind .bool)
  | .fadd | .fsub | .fmul | .fdiv | .fmod | .fpow | .fatan2 | .flogb =>
    need (num Kind.isFloat) (.kind .float)
  -- A time of day modulo a day (`Parse`'s wrap around midnight) keeps its kind.
  | .idiv | .imod => need (num Kind.isExactNum) (a.arith b)
  | .ipow | .bit _ => need (num Kind.isInt) (.kind .int)
  | .concat | .trim _ _ => need (a.okK .str && b.okK .str) (.kind .str)
  | .strpos | .levenshtein => need (a.okK .str && b.okK .str) (.kind .int)
  | .startsWith | .endsWith | .like | .ilike => need (a.okK .str && b.okK .str) (.kind .bool)
  | .substr _ _ | .strRepeat => need (a.okK .str && b.okI Kind.isInt) (.kind .str)
  | .dateAdd => need (a.okI Kind.isDate && b.okI Kind.isInt) (.kind .date)
  | .dateDiff => need (num Kind.isDate) (.kind .int)
  | .dadd | .dsub | .dmul | .ddiv => need (num Kind.isIntOrDec) (.kind .int)
  | .pair => some (.kind (.struct [a.toKind, b.toKind]))
  | .greatest | .least => some (a.join b)
  | .bbox2 _ => some (.kind .other)

/-- The kind of a literal: integers have none of their own. -/
def Value.kt : Value → KT
  | .int _ => .num
  | .bool _ => .kind .bool
  | .str _ => .kind .str
  | .null | .list _ => .kind .other

/-- The element kind of a list's kind. -/
def KT.elem? : KT → Option Kind
  | .kind (.list k) => some k
  | .kind .other => some .other
  | _ => none

/-- What a higher-order function gives for a list of kind `tl` and a body
of kind `tb`. -/
def HoFn.kindOf (f : HoFn) (tl tb : KT) : Option KT :=
  match f with
  | .anyMatch | .allMatch => if tb.okK .bool then some (.kind .bool) else none
  | .transform => some (.kind (.list tb.toKind))
  | .filter => some tl

/-- The kind of `e` over columns of kinds `env`, if it is well-kinded. A
lambda's body is typed under its element's kind in front of `env` (D28). -/
def Expr.kindT (env : List Kind) : Expr → Option KT
  | .lit v => some v.kt
  | .field i => env[i]?.map .kind
  | .un f a => (a.kindT env).bind f.kindOf
  | .bin f a b => (a.kindT env).bind fun ta => (b.kindT env).bind fun tb => f.kindOf ta tb
  | .ifThen c t e =>
    (c.kindT env).bind fun _ => (t.kindT env).bind fun tt => (e.kindT env).map tt.join
  | .hof f l b =>
    (l.kindT env).bind fun tl => tl.elem?.bind fun elem =>
      (b.kindT (elem :: env)).bind fun tb => f.kindOf tl tb

/-- A row has the kinds `ks`: every column's value has its kind (columns
past `ks` have any kind). -/
def Row.HasKinds (ks : List Kind) (row : Row) : Prop :=
  ∀ i, (row.getD i .null).hasKind (ks.getD i .other) = true

/-! ### Soundness of the function table -/

theorem KT.has_join_left {a b : KT} {v : Value} (h : a.has v = true) : (a.join b).has v = true := by
  unfold KT.join; split
  · exact h
  · simp [KT.has, KT.toKind]

theorem KT.has_join_right {a b : KT} {v : Value} (h : b.has v = true) : (a.join b).has v = true := by
  unfold KT.join; split
  · rename_i hab; subst hab; exact h
  · simp [KT.has, KT.toKind]

/-- A value of an accepted integer-represented kind is an integer or NULL. -/
theorem KT.okI_int {p : Kind → Bool} (hp : ∀ k, p k = true → k.isIntRep = true) {t : KT} {v : Value}
    (ht : t.okI p = true) (hv : t.has v = true) (hk : t ≠ .kind .other) : v.hasKind .int = true := by
  match t, v with
  | _, .null => simp
  | .num, .int _ => rfl
  | .kind k, .int _ => rfl
  | .num, .bool _ | .num, .str _ | .num, .list _ => simp [KT.has, KT.toKind, Value.hasKind] at hv
  | .kind k, .bool _ | .kind k, .str _ | .kind k, .list _ =>
    cases k <;> simp_all [KT.okI, KT.has, KT.toKind, Value.hasKind, Kind.isIntRep] <;>
      (have := hp _ ht; simp [Kind.isIntRep] at this)

/-- The integer-represented results, by the function alone. -/
theorem KT.has_intRep {t : KT} (ht : t.toKind.isIntRep = true) {v : Value}
    (hv : v.hasKind .int = true) : t.has v = true :=
  Value.hasKind_of_int ht hv

/-- What `UnFn.apply` gives, by the function alone: an integer, a boolean or
a string (or NULL), for those that give one. -/
def UnFn.out : UnFn → Kind
  | .not | .isNull | .isNum => .bool
  | .itos | .upper | .lower | .reverse | .replace _ _ | .regexExtract _ _ | .regexReplace _ _ _
  | .md5 | .sha256 | .strftime _ => .str
  | .wrap _ | .widen | .decimal _ _ | .dkind _ _ | .fit _ _ | .structField _ | .listElement _
  | .raise _ | .bbox _ => .other
  | _ => .int

theorem UnFn.apply_out (f : UnFn) (v : Value) : (f.apply v).hasKind f.out = true := by
  cases f
  case addMonths m t => cases t <;> cases v <;> simp [UnFn.apply, UnFn.out, Value.hasKind, Kind.isIntRep]
  all_goals cases v <;> simp only [UnFn.apply, UnFn.out] <;>
    (try split) <;> (try split) <;> (try simp [Value.hasKind, Kind.isIntRep])

/-- An accepted integer-represented kind has every integer. -/
theorem KT.okI_has_int {p : Kind → Bool} (hp : ∀ k, p k = true → k.isIntRep = true) {t : KT}
    (ht : t.okI p = true) (i : Int) : t.has (.int i) = true := by
  match t with
  | .num => rfl
  | .kind k =>
    simp only [KT.okI] at ht
    cases k <;> first | rfl | (have := hp _ ht; simp_all [Kind.isIntRep])

theorem KT.orNum_intRep {p : Kind → Bool} (hp : ∀ k, p k = true → k.isIntRep = true) {t : KT}
    (ht : t.okI p = true) : t.orNum.toKind.isIntRep = true := by
  match t with
  | .num => rfl
  | .kind k =>
    simp only [KT.okI] at ht
    cases k <;> first | rfl | (have := hp _ ht; simp_all [Kind.isIntRep])

theorem Value.getD_hasKind {k : Kind} {vs : List Value} (h : ∀ v ∈ vs, v.hasKind k = true)
    (n : Nat) : (vs.getD n .null).hasKind k = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hg : vs[n]? with
  | none => simp
  | some w => exact h w (List.mem_of_getElem? hg)

theorem Value.listElement_hasKind {k : Kind} {vs : List Value} (h : ∀ v ∈ vs, v.hasKind k = true)
    (off : Int) : (Value.listElement off vs).hasKind k = true := by
  unfold Value.listElement
  dsimp only
  split <;> split <;> first | exact Value.getD_hasKind h _ | simp

theorem UnFn.kindOf_sound {f : UnFn} {t t' : KT} {v : Value} (h : f.kindOf t = some t')
    (hv : t.has v = true) : t'.has (f.apply v) = true := by
  have hout := f.apply_out v
  cases f
  case addMonths m b =>
    cases b <;> simp only [UnFn.kindOf, UnFn.out, Option.ite_none_right_eq_some,
      Option.some.injEq] at h hout <;> (obtain ⟨_, rfl⟩ := h; exact Value.hasKind_of_int rfl hout)
  all_goals simp only [UnFn.kindOf, UnFn.out, Option.ite_none_right_eq_some, Option.some.injEq] at h hout
  all_goals first
    | (obtain ⟨_, rfl⟩ := h; first | exact hout | exact Value.hasKind_of_int rfl hout)
    | (obtain ⟨ht, rfl⟩ := h
       exact Value.hasKind_of_int (KT.orNum_intRep (by intro k hk; cases k <;>
         simp_all [Kind.isExactNum, Kind.isIntRep, Kind.isTimeOrTod, Kind.isTime]) ht) hout)
    | (subst h; first | exact hout | simp [KT.has, KT.toKind])
    | skip
  case wrap => obtain ⟨_, rfl⟩ := h; exact hv
  case fit =>
    obtain ⟨ht, rfl⟩ := h
    cases v <;> simp only [UnFn.apply] <;> first | exact hv |
      exact KT.okI_has_int (fun k hk => by cases k <;> simp_all [Kind.isExactNum, Kind.isIntRep]) ht _
  case widen =>
    obtain ⟨_, rfl⟩ := h
    split
    · rename_i hn; subst hn; exact Value.hasKind_of_int rfl hv
    · exact hv
  case decimal p s | dkind p s =>
    obtain ⟨ht, rfl⟩ := h
    split
    · exact hv
    · rename_i hn
      exact Value.hasKind_of_int rfl (KT.okI_int (fun k hk => by
        cases k <;> simp_all [Kind.isIntOrDec, Kind.isIntRep]) ht hv hn)
  case structField i =>
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · rename_i ks
      match v, hv with
      | .null, _ => simp [UnFn.apply, KT.has]
      | .list vs, hv => exact Value.fieldsHaveKinds_getD hv i
      | .int _, hv | .bool _, hv | .str _, hv => simp [KT.has, KT.toKind, Value.hasKind, Kind.isIntRep] at hv
    · simp [KT.has, KT.toKind]
  case listElement off =>
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · rename_i k
      match v, hv with
      | .null, _ => simp [UnFn.apply, KT.has]
      | .list vs, hv => exact Value.listElement_hasKind (Value.hasKind_list.mp hv) off
      | .int _, hv | .bool _, hv | .str _, hv => simp [KT.has, KT.toKind, Value.hasKind, Kind.isIntRep] at hv
    · simp [KT.has, KT.toKind]
  case cardinality =>
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      exact Value.hasKind_of_int rfl hout

/-- What `BinFn.apply` gives, by the function alone, for those that give an
integer, a boolean or a string (or NULL). -/
def BinFn.out : BinFn → Kind
  | .eq | .lt | .and | .or | .startsWith | .endsWith | .like | .ilike => .bool
  | .concat | .substr _ _ | .trim _ _ | .strRepeat => .str
  | .pair | .greatest | .least | .bbox2 _ => .other
  | _ => .int

theorem and3_hasKind (a b : Value) : (and3 a b).hasKind .bool = true := by
  unfold and3; split <;> rfl

theorem or3_hasKind (a b : Value) : (or3 a b).hasKind .bool = true := by
  unfold or3; split <;> rfl

theorem BinFn.apply_out (f : BinFn) (a b : Value) : (f.apply a b).hasKind f.out = true := by
  cases f
  case and => exact and3_hasKind a b
  case or => exact or3_hasKind a b
  case lt =>
    cases a <;> cases b <;> simp only [BinFn.apply, BinFn.out] <;> (try simp [Value.hasKind]) <;>
      (generalize Value.listLt3 _ _ = r; rcases r with _ | _ | _ <;> rfl)
  all_goals cases a <;> cases b <;> simp only [BinFn.apply, BinFn.out] <;>
    (try split) <;> (try split) <;> (try simp [Value.hasKind, Kind.isIntRep])

theorem KT.arith_intRep {a b : KT} (ha : a.okI Kind.isExactNum = true)
    (hb : b.okI Kind.isExactNum = true) : (a.arith b).toKind.isIntRep = true := by
  have ex : ∀ k, Kind.isExactNum k = true → k.isIntRep = true := fun k hk => by
    cases k <;> simp_all [Kind.isExactNum, Kind.isIntRep]
  match a, b with
  | .num, .num => rfl
  | .num, .kind k => cases k <;> first | rfl | exact ex _ hb
  | .kind ka, .num => cases ka <;> first | rfl | exact ex _ ha
  | .kind ka, .kind kb =>
    cases ka <;> cases kb <;> first | rfl | exact ex _ ha | exact ex _ hb |
      simp_all [KT.okI, Kind.isExactNum]

theorem BinFn.kindOf_sound {f : BinFn} {ta tb t' : KT} {a b : Value} (h : f.kindOf ta tb = some t')
    (ha : ta.has a = true) (hb : tb.has b = true) : t'.has (f.apply a b) = true := by
  have hout := f.apply_out a b
  cases f <;> simp only [BinFn.kindOf, BinFn.out, Option.ite_none_right_eq_some, Option.some.injEq,
    Bool.and_eq_true] at h hout
  all_goals first
    | (obtain ⟨_, rfl⟩ := h; first | exact hout | exact Value.hasKind_of_int rfl hout)
    | (obtain ⟨⟨h1, h2⟩, rfl⟩ := h; exact Value.hasKind_of_int (KT.arith_intRep h1 h2) hout)
    | (subst h; first | exact hout | simp [KT.has, KT.toKind])
    | skip
  case pair =>
    subst_vars
    show (BinFn.apply .pair a b).hasKind (.struct [ta.toKind, tb.toKind]) = true
    have e : ∀ x y : Value, (Value.list [x, y]).hasKind (.struct [ta.toKind, tb.toKind]) =
        (x.hasKind ta.toKind && (y.hasKind tb.toKind && true)) := fun _ _ => rfl
    have ha' : a.hasKind ta.toKind = true := ha
    have hb' : b.hasKind tb.toKind = true := hb
    cases a <;> cases b <;> simp only [BinFn.apply] <;>
      first | exact Value.hasKind_null _ | (rw [e, ha', hb']; rfl)
  case greatest | least =>
    subst_vars
    simp only [BinFn.apply]
    rcases Value.pick_mem (better := _) a b with he | he <;> rw [he]
    · exact KT.has_join_left ha
    · exact KT.has_join_right hb

/-! ### Soundness of expressions -/

theorem Value.has_kt : ∀ v : Value, v.kt.has v = true
  | .null | .bool _ | .str _ | .int _ | .list _ => rfl

theorem Row.HasKinds.cons {ks : List Kind} {row : Row} {k : Kind} {x : Value}
    (h : Row.HasKinds ks row) (hx : x.hasKind k = true) : Row.HasKinds (k :: ks) (x :: row)
  | 0 => hx
  | i + 1 => by simpa using h i

theorem HoFn.match_hasKind (f : HoFn) (hf : f = .anyMatch ∨ f = .allMatch) (v : Value)
    (p : Value → Value) : (f.apply v p).hasKind .bool = true := by
  rcases hf with rfl | rfl <;> cases v <;> simp only [HoFn.apply] <;> (try rfl)
  all_goals
    rename_i vs
    cases vs with
    | nil => rfl
    | cons x xs => simp only [List.foldr_cons]; first | exact or3_hasKind _ _ | exact and3_hasKind _ _

/-- **Soundness of `Expr.kindT`**: on a row of kinds `env`, a well-kinded
expression's value has its kind. -/
theorem Expr.kindT_sound : ∀ {e : Expr} {env : List Kind} {row : Row} {t : KT},
    Row.HasKinds env row → e.kindT env = some t → t.has (e.eval row) = true
  | .lit v, _, _, t, _, h => by
    simp only [kindT, Option.some.injEq] at h; subst h; exact Value.has_kt v
  | .field i, env, row, t, hr, h => by
    simp only [kindT, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have := hr i
    rw [List.getD_eq_getElem?_getD, hk] at this
    exact this
  | .un f a, env, row, t, hr, h => by
    simp only [kindT, Option.bind_eq_some_iff] at h
    obtain ⟨ta, ha, hf⟩ := h
    exact UnFn.kindOf_sound hf (Expr.kindT_sound hr ha)
  | .bin f a b, env, row, t, hr, h => by
    simp only [kindT, Option.bind_eq_some_iff] at h
    obtain ⟨ta, ha, tb, hb, hf⟩ := h
    exact BinFn.kindOf_sound hf (Expr.kindT_sound hr ha) (Expr.kindT_sound hr hb)
  | .ifThen c th el, env, row, t, hr, h => by
    simp only [kindT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, tt, ht, te, he, rfl⟩ := h
    simp only [eval]
    split
    · exact KT.has_join_left (Expr.kindT_sound hr ht)
    · exact KT.has_join_right (Expr.kindT_sound hr he)
  | .hof f l b, env, row, t, hr, h => by
    simp only [kindT, Option.bind_eq_some_iff] at h
    obtain ⟨tl, hl, elem, helem, tb, hb, hf⟩ := h
    have hlv := Expr.kindT_sound hr hl
    -- Every element of the list has the element's kind.
    have hx : ∀ x ∈ (l.eval row).elems, x.hasKind elem = true := by
      intro x hxm
      unfold KT.elem? at helem
      split at helem <;> simp only [Option.some.injEq, reduceCtorEq] at helem <;> subst helem
      · rename_i k
        cases hv : l.eval row with
        | list vs =>
          rw [hv] at hlv hxm
          exact Value.hasKind_list.mp hlv x hxm
        | _ => rw [hv] at hxm; simp [Value.elems] at hxm
      · simp
    have hbody : ∀ x ∈ (l.eval row).elems, tb.has (b.eval (x :: row)) = true := fun x hxm =>
      Expr.kindT_sound (hr.cons (hx x hxm)) hb
    simp only [eval]
    cases f <;> simp only [HoFn.kindOf] at hf
    · split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf; subst hf
      exact HoFn.match_hasKind _ (.inl rfl) _ _
    · split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf; subst hf
      exact HoFn.match_hasKind _ (.inr rfl) _ _
    · simp only [Option.some.injEq] at hf; subst hf
      cases hv : l.eval row with
      | list vs =>
        rw [hv] at hbody
        simp only [HoFn.apply, KT.has, KT.toKind]
        refine Value.hasKind_list.mpr fun w hw => ?_
        obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hw
        exact hbody x hxm
      | _ => simp [HoFn.apply, KT.has]
    · simp only [Option.some.injEq] at hf; subst hf
      cases hv : l.eval row with
      | list vs =>
        rw [hv] at hlv
        simp only [HoFn.apply]
        unfold KT.elem? at helem
        split at helem <;> simp only [Option.some.injEq, reduceCtorEq] at helem
        · exact Value.hasKind_list.mpr fun w hw =>
            Value.hasKind_list.mp hlv w (List.mem_filter.mp hw).1
        · simp [KT.has, KT.toKind]
      | _ => simp [HoFn.apply, KT.has]

/-! ## Kinds of relations -/

/-- The kind of a measure's result, where the function alone says it. -/
def Measure.kindOut (m : Measure) : Kind :=
  match m.fn with
  | .count | .sum | .iavg | .bit _ => .int
  | .fsum | .avg => .float
  | .concat _ => .str
  | _ => .other

theorem Measure.eval_kindOut (m : Measure) (rows : Relation) :
    (m.eval rows).hasKind m.kindOut = true := by
  unfold Measure.eval Measure.kindOut
  rcases m with ⟨fn, arg, distinct, filter, sort⟩
  cases fn <;> simp only
  all_goals first
    | exact Value.hasKind_other _
    | (generalize Measure.inputs _ _ = vs
       cases vs <;> simp [AggFn.apply, Value.hasKind, Kind.isIntRep])

/-- Are a measure's argument and filter well-kinded? -/
def Measure.wk (env : List Kind) (m : Measure) : Bool :=
  (m.arg.kindT env).isSome && m.filter.all fun c => (c.kindT env).isSome

def WinFn.kindOut : WinFn → Kind
  | .rowNumber | .rank _ | .denseRank _ | .ntile _ => .int
  | .percentRank _ | .cumeDist _ => .float
  | .agg m _ _ => m.kindOut
  | _ => .other

def WinFn.wk (env : List Kind) : WinFn → Bool
  | .agg m _ _ => m.wk env
  | _ => true

theorem WinFn.value_kindOut (part : List Nat) (before after : List Row) (x : Row) (f : WinFn) :
    (f.value part before after x).hasKind f.kindOut = true := by
  unfold WinFn.value
  cases f <;> simp only [WinFn.valueIn, WinFn.kindOut, floatRatio] <;>
    first | exact Value.hasKind_other _ | exact Measure.eval_kindOut _ _ | (try split) <;> rfl

/-- The kinds of a list of expressions, if all are well-kinded. -/
def Expr.kindsT (env : List Kind) : List Expr → Option (List KT)
  | [] => some []
  | e :: es => (e.kindT env).bind fun t => (Expr.kindsT env es).map (t :: ·)

/-- Two columns' kind: their own if equal, else unknown. -/
def Kind.join (a b : Kind) : Kind := if a = b then a else .other

/-- `ks` cut or padded with unknown kinds to `n` columns. -/
def fitKinds (n : Nat) (ks : List Kind) : List Kind := (List.range n).map (ks.getD · .other)

/-- The kinds of a plan's columns, if it is well-kinded: the tables' kinds
are `tk`. Mirrors `Rel.arity`. -/
def Rel.inferKinds (cat : Catalog) (tk : String → List Kind) : Rel → Option (List Kind)
  | .read t => some (fitKinds (cat t).arity (tk t))
  | .values n _ => some (List.replicate n .other)
  | .filter r c => (r.inferKinds cat tk).bind fun ks =>
      if (c.kindT ks).isSome then some ks else none
  | .project r es => (r.inferKinds cat tk).bind fun ks =>
      (Expr.kindsT ks es).map fun ts => ks ++ ts.map KT.toKind
  | .emit r m => (r.inferKinds cat tk).map fun ks => m.map (ks.getD · .other)
  | .cross a b => (a.inferKinds cat tk).bind fun ka => (b.inferKinds cat tk).map (ka ++ ·)
  | .join a b _ on => (a.inferKinds cat tk).bind fun ka =>
      (b.inferKinds cat tk).bind fun kb =>
        if (on.kindT (ka ++ kb)).isSome then some (ka ++ kb) else none
  | .semi a b _ on => (a.inferKinds cat tk).bind fun ka =>
      (b.inferKinds cat tk).bind fun kb =>
        if (on.kindT (ka ++ kb)).isSome then some ka else none
  | .fetch r _ _ | .orderBy r _ | .distinct r => r.inferKinds cat tk
  | .unionAll a b => (a.inferKinds cat tk).bind fun ka =>
      (b.inferKinds cat tk).map fun kb => List.zipWith Kind.join ka kb
  | .window r _ _ fns => (r.inferKinds cat tk).bind fun ks =>
      if fns.all (·.wk ks) then some (ks ++ fns.map WinFn.kindOut) else none
  | .aggregate r gs ms => (r.inferKinds cat tk).bind fun ks =>
      (Expr.kindsT ks gs).bind fun ts =>
        if ms.all (·.wk ks) then some (ts.map KT.toKind ++ ms.map Measure.kindOut) else none
  | .unnest r c => (r.inferKinds cat tk).map fun ks =>
      ks.set c (match ks.getD c .other with | .list k => k | _ => .other)

/-! ### Refusals

A catalog of one table `t` with a double, a timestamp and a list of
integers. -/

private def kcat : Catalog := fun _ => ⟨3, []⟩
private def ktk : String → List Kind := fun _ => [.float, .time, .list .int]

-- `+` of a double and `ftoi` of a timestamp are refused.
#guard (Rel.project (.read "t") [.bin .add (.field 0) (.lit (.int 1))]).inferKinds kcat ktk == none
#guard (Rel.project (.read "t") [.un .ftoi (.field 1)]).inferKinds kcat ktk == none
-- Their well-kinded forms are kinded.
#guard (Rel.project (.read "t") [.bin .fadd (.field 0) (.lit (.int 1))]).inferKinds kcat ktk ==
  some [.float, .time, .list .int, .float]
#guard (Rel.project (.read "t") [.bin .add (.field 1) (.lit (.int 60000000))]).inferKinds kcat ktk ==
  some [.float, .time, .list .int, .time]
-- A lambda's body reads its element (field 0) and the row (from field 1, D28).
#guard (Rel.project (.read "t")
    [.hof .transform (.field 2) (.bin .fadd (.un .itof (.field 0)) (.field 1))]).inferKinds kcat ktk ==
  some [.float, .time, .list .int, .list .float]
#guard (Rel.project (.read "t")
    [.hof .filter (.field 2) (.bin .add (.field 0) (.field 1))]).inferKinds kcat ktk == none

/-! ### Soundness -/

theorem Expr.kindsT_length {env : List Kind} :
    ∀ {es : List Expr} {ts : List KT}, Expr.kindsT env es = some ts → ts.length = es.length
  | [], ts, h => by simp only [kindsT, Option.some.injEq] at h; subst h; rfl
  | e :: es, ts, h => by
    simp only [kindsT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, ts', h', rfl⟩ := h
    simp [Expr.kindsT_length h']

theorem Expr.kindsT_sound {env : List Kind} {row : Row} (hr : Row.HasKinds env row) :
    ∀ {es : List Expr} {ts : List KT}, Expr.kindsT env es = some ts →
      Row.HasKinds (ts.map KT.toKind) (es.map (·.eval row))
  | [], ts, h, i => by simp only [kindsT, Option.some.injEq] at h; subst h; simp
  | e :: es, ts, h, i => by
    simp only [kindsT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, ts', h', rfl⟩ := h
    cases i with
    | zero => exact Expr.kindT_sound hr ht
    | succ i => simpa using Expr.kindsT_sound hr h' i

theorem Row.HasKinds.append {ka kb : List Kind} {x y : Row} (hx : Row.HasKinds ka x)
    (hy : Row.HasKinds kb y) (hl : ka.length = x.length) : Row.HasKinds (ka ++ kb) (x ++ y) := by
  intro i
  simp only [List.getD_eq_getElem?_getD]
  by_cases hi : i < x.length
  · rw [List.getElem?_append_left hi, List.getElem?_append_left (hl ▸ hi)]
    simpa [List.getD_eq_getElem?_getD] using hx i
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hl]
    simpa [List.getD_eq_getElem?_getD] using hy (i - x.length)

theorem Row.HasKinds.nulls (ks : List Kind) (n : Nat) : Row.HasKinds ks (List.replicate n .null) := by
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> simp

theorem Row.HasKinds.other (n : Nat) (row : Row) : Row.HasKinds (List.replicate n .other) row := by
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> simp

theorem Row.HasKinds.fit {ks : List Kind} {row : Row} (h : Row.HasKinds ks row) (n : Nat) :
    Row.HasKinds (fitKinds n ks) row := by
  intro i
  simp only [fitKinds, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < n
  · rw [List.getElem?_range hi]; simpa [List.getD_eq_getElem?_getD] using h i
  · rw [List.getElem?_eq_none (by simpa using hi)]; simp

theorem Row.HasKinds.emit {ks : List Kind} {row : Row} (h : Row.HasKinds ks row) (m : List Nat) :
    Row.HasKinds (m.map (ks.getD · .other)) (m.map (row.getD · .null)) := by
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? with
  | none => simp
  | some j => simpa [List.getD_eq_getElem?_getD] using h j

theorem Row.HasKinds.zipJoin {ka kb : List Kind} {row : Row} :
    (Row.HasKinds ka row ∨ Row.HasKinds kb row) → Row.HasKinds (List.zipWith Kind.join ka kb) row := by
  intro h i
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  cases ha : ka[i]? <;> cases hb : kb[i]? <;> simp only [Option.map_some, Option.map_none,
    Option.bind_some, Option.bind_none, Option.getD_none, Option.getD_some, Value.hasKind_other]
  rename_i a b
  unfold Kind.join
  split
  · rename_i hab; subst hab
    rcases h with h | h
    · have := h i; rw [List.getD_eq_getElem?_getD, ha, Option.getD_some] at this; exact this
    · have := h i; rw [List.getD_eq_getElem?_getD, hb, Option.getD_some] at this; exact this
  · simp

theorem Row.HasKinds.set {ks : List Kind} {row : Row} (h : Row.HasKinds ks row) (c : Nat) (v : Value)
    (k : Kind) (hv : v.hasKind k = true) : Row.HasKinds (ks.set c k) (row.set c v) := by
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hi : c = i
  · subst hi
    by_cases hc : c < row.length
    · by_cases hk : c < ks.length
      · simp [hc, hk, hv]
      · simp only [hc, hk, if_true, if_false]
        cases hg : ks[c]? <;> simp_all
    · have := List.getElem?_eq_none (l := row) (by omega : row.length ≤ c)
      simp [hc, this]
  · simpa [hi, List.getD_eq_getElem?_getD] using h i

theorem Rel.inferKinds_length {cat : Catalog} {tk : String → List Kind} :
    ∀ {r : Rel} {ks : List Kind}, r.WF cat → r.inferKinds cat tk = some ks → ks.length = r.arity cat
  | .read t, ks, _, h => by
    simp only [inferKinds, Option.some.injEq] at h; subst h; simp [fitKinds, arity]
  | .values n _, ks, _, h => by
    simp only [inferKinds, Option.some.injEq] at h; subst h; simp [arity]
  | .filter r _, ks, hwf, h => by
    simp only [inferKinds, Option.bind_eq_some_iff] at h
    obtain ⟨ks', h', hc⟩ := h
    split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc; subst hc
    simp only [arity]; exact inferKinds_length hwf.1 h'
  | .project r es, ks, hwf, h => by
    simp only [inferKinds, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ks', h', ts, hts, rfl⟩ := h
    simp [arity, inferKinds_length hwf.1 h', Expr.kindsT_length hts]
  | .emit r m, ks, _, h => by
    simp only [inferKinds, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; simp [arity]
  | .cross a b, ks, hwf, h => by
    simp only [inferKinds, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ka, ha, kb, hb, rfl⟩ := h
    simp [arity, inferKinds_length hwf.1 ha, inferKinds_length hwf.2 hb]
  | .join a b _ _, ks, hwf, h => by
    simp only [inferKinds, Option.bind_eq_some_iff] at h
    obtain ⟨ka, ha, kb, hb, hc⟩ := h
    split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc; subst hc
    simp [arity, inferKinds_length hwf.1 ha, inferKinds_length hwf.2.1 hb]
  | .semi a b _ _, ks, hwf, h => by
    simp only [inferKinds, Option.bind_eq_some_iff] at h
    obtain ⟨ka, ha, kb, hb, hc⟩ := h
    split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc; subst hc
    simp [arity, inferKinds_length hwf.1 ha]
  | .fetch r _ _, ks, hwf, h => by
    simp only [inferKinds] at h; simp only [arity]; exact inferKinds_length (r := r) hwf h
  | .orderBy r _, ks, hwf, h => by
    simp only [inferKinds] at h; simp only [arity]; exact inferKinds_length (r := r) hwf.1 h
  | .distinct r, ks, hwf, h => by
    simp only [inferKinds] at h; simp only [arity]; exact inferKinds_length (r := r) hwf h
  | .unionAll a b, ks, hwf, h => by
    simp only [inferKinds, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ka, ha, kb, hb, rfl⟩ := h
    simp [arity, inferKinds_length hwf.1 ha, inferKinds_length hwf.2.1 hb, hwf.2.2]
  | .window r _ _ fns, ks, hwf, h => by
    simp only [inferKinds, Option.bind_eq_some_iff] at h
    obtain ⟨ks', h', hc⟩ := h
    split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc; subst hc
    simp [arity, inferKinds_length hwf.1 h']
  | .aggregate r gs ms, ks, hwf, h => by
    simp only [inferKinds, Option.bind_eq_some_iff] at h
    obtain ⟨ks', h', ts, hts, hc⟩ := h
    split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc; subst hc
    simp [arity, Expr.kindsT_length hts]
  | .unnest r _, ks, hwf, h => by
    simp only [inferKinds, Option.map_eq_some_iff] at h
    obtain ⟨ks', h', rfl⟩ := h
    simp [arity, inferKinds_length hwf.1 h']

/-- The tables' rows have their declared kinds. -/
def Catalog.HasKinds (cat : Catalog) (tk : String → List Kind) : Prop :=
  ∀ t, ∀ row ∈ (cat t).rows, Row.HasKinds (tk t) row

/-- **Soundness of the kind checker**: on a well-formed catalog whose rows
have their tables' kinds, every row of a well-formed, well-kinded plan has
the inferred kinds (`KT.num`, an integer literal's, as `int`). -/
theorem Rel.kinds_sound {cat : Catalog} {tk : String → List Kind} (hcat : cat.WF)
    (hk : cat.HasKinds tk) :
    ∀ {r : Rel} {ks : List Kind}, r.WF cat → r.inferKinds cat tk = some ks →
      ∀ row ∈ r.eval cat, Row.HasKinds ks row
  | .read t, ks, _, h, row, hr => by
    simp only [inferKinds, Option.some.injEq] at h; subst h
    exact (hk t row hr).fit _
  | .values n _, ks, _, h, row, _ => by
    simp only [inferKinds, Option.some.injEq] at h; subst h
    exact Row.HasKinds.other n row
  | .filter r _, ks, hwf, h, row, hr => by
    simp only [inferKinds, Option.bind_eq_some_iff] at h
    obtain ⟨ks', h', hc⟩ := h
    split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc; subst hc
    simp only [eval, List.mem_filter] at hr
    exact kinds_sound hcat hk hwf.1 h' row hr.1
  | .project r es, ks, hwf, h, row, hr => by
    simp only [inferKinds, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ks', h', ts, hts, rfl⟩ := h
    simp only [eval, List.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    have hxk := kinds_sound hcat hk hwf.1 h' x hx
    exact hxk.append (Expr.kindsT_sound hxk hts)
      ((inferKinds_length hwf.1 h').trans (eval_arity hcat hwf.1 x hx).symm)
  | .emit r m, ks, hwf, h, row, hr => by
    simp only [inferKinds, Option.map_eq_some_iff] at h
    obtain ⟨ks', h', rfl⟩ := h
    simp only [eval, List.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact (kinds_sound hcat hk hwf.1 h' x hx).emit m
  | .cross a b, ks, hwf, h, row, hr => by
    simp only [inferKinds, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ka, ha, kb, hb, rfl⟩ := h
    simp only [eval, mem_crossRows] at hr
    obtain ⟨x, hx, y, hy, rfl⟩ := hr
    exact (kinds_sound hcat hk hwf.1 ha x hx).append (kinds_sound hcat hk hwf.2 hb y hy)
      ((inferKinds_length hwf.1 ha).trans (eval_arity hcat hwf.1 x hx).symm)
  | .join a b ty _, ks, hwf, h, row, hr => by
    simp only [inferKinds, Option.bind_eq_some_iff] at h
    obtain ⟨ka, ha, kb, hb, hc⟩ := h
    split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc; subst hc
    cases ty with
    | inner =>
      simp only [eval, List.mem_filter, mem_crossRows] at hr
      obtain ⟨⟨x, hx, y, hy, rfl⟩, _⟩ := hr
      exact (kinds_sound hcat hk hwf.1 ha x hx).append (kinds_sound hcat hk hwf.2.1 hb y hy)
        ((inferKinds_length hwf.1 ha).trans (eval_arity hcat hwf.1 x hx).symm)
    | left =>
      simp only [eval, List.mem_flatMap] at hr
      obtain ⟨x, hx, hr⟩ := hr
      have hxk := kinds_sound hcat hk hwf.1 ha x hx
      have hl := (inferKinds_length hwf.1 ha).trans (eval_arity hcat hwf.1 x hx).symm
      unfold leftJoinRow at hr
      simp only [] at hr
      split at hr
      · simp only [List.mem_singleton] at hr; subst hr
        exact hxk.append (Row.HasKinds.nulls kb _) hl
      · simp only [List.mem_filter, List.mem_map] at hr
        obtain ⟨⟨y, hy, rfl⟩, _⟩ := hr
        exact hxk.append (kinds_sound hcat hk hwf.2.1 hb y hy) hl
  | .semi a b _ _, ks, hwf, h, row, hr => by
    simp only [inferKinds, Option.bind_eq_some_iff] at h
    obtain ⟨ka, ha, kb, hb, hc⟩ := h
    split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc; subst hc
    simp only [eval, List.mem_filter] at hr
    exact kinds_sound hcat hk hwf.1 ha row hr.1
  | .fetch r _ _, ks, hwf, h, row, hr => by
    simp only [inferKinds] at h
    simp only [eval] at hr
    have := kinds_sound hcat hk (r := r) hwf h
    split at hr
    · exact this row (List.mem_of_mem_drop hr)
    · exact this row (List.mem_of_mem_drop (List.mem_of_mem_take hr))
  | .orderBy r _, ks, hwf, h, row, hr => by
    simp only [inferKinds] at h
    simp only [eval, List.mem_mergeSort] at hr
    exact kinds_sound hcat hk (r := r) hwf.1 h row hr
  | .distinct r, ks, hwf, h, row, hr => by
    simp only [inferKinds] at h
    simp only [eval, mem_dedup] at hr
    exact kinds_sound hcat hk (r := r) hwf h row hr
  | .unionAll a b, ks, hwf, h, row, hr => by
    simp only [inferKinds, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ka, ha, kb, hb, rfl⟩ := h
    simp only [eval, List.mem_append] at hr
    rcases hr with hr | hr
    · exact Row.HasKinds.zipJoin (.inl (kinds_sound hcat hk hwf.1 ha row hr))
    · exact Row.HasKinds.zipJoin (.inr (kinds_sound hcat hk hwf.2.1 hb row hr))
  | .window r _ _ fns, ks, hwf, h, row, hr => by
    simp only [inferKinds, Option.bind_eq_some_iff] at h
    obtain ⟨ks', h', hc⟩ := h
    split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc; subst hc
    obtain ⟨_, x, _, _, hx, rfl⟩ := mem_windowEval hr
    refine (kinds_sound hcat hk hwf.1 h' x hx).append (fun i => ?_)
      ((inferKinds_length hwf.1 h').trans (eval_arity hcat hwf.1 x hx).symm)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases fns[i]? with
    | none => simp
    | some f => exact WinFn.value_kindOut _ _ _ _ f
  | .aggregate r gs ms, ks, hwf, h, row, hr => by
    simp only [inferKinds, Option.bind_eq_some_iff] at h
    obtain ⟨ks', h', ts, hts, hc⟩ := h
    split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc; subst hc
    obtain ⟨k, grp, rfl, _, hk'⟩ := mem_aggregateEval hr
    have hm : Row.HasKinds (ms.map Measure.kindOut) (ms.map (·.eval grp)) := fun i => by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases ms[i]? with
      | none => simp
      | some m => exact Measure.eval_kindOut m grp
    rcases hk' with ⟨rfl, rfl⟩ | ⟨x, hx, rfl⟩
    · have : ts = [] := by simpa [Expr.kindsT] using hts.symm
      subst this
      simpa using hm
    · have hxk := kinds_sound hcat hk hwf.1 h' x hx
      exact (Expr.kindsT_sound hxk hts).append hm (by simp [groupKey, Expr.kindsT_length hts])
  | .unnest r c, ks, hwf, h, row, hr => by
    simp only [inferKinds, Option.map_eq_some_iff] at h
    obtain ⟨ks', h', rfl⟩ := h
    simp only [eval, List.mem_flatMap] at hr
    obtain ⟨x, hx, hr⟩ := hr
    obtain ⟨vs, v, hvs, hv, rfl⟩ := mem_unnestRow hr
    have hxk := kinds_sound hcat hk hwf.1 h' x hx
    refine hxk.set c v _ ?_
    have hc := hxk c
    rw [hvs] at hc
    split
    · rename_i k hkc
      rw [hkc] at hc
      exact Value.hasKind_list.mp hc v hv
    · simp

end Substrait
