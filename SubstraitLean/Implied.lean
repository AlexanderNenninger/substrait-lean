import SubstraitLean.Pruning

/-!
# Implied predicates on base tables (#81)

A view's conditions and the facts about its other inputs can imply a
predicate on a base table's columns that the query does not state. With
`o.ts >= c.since` in a view over `orders o JOIN customers c`, and the
customers' preconditions or CHECK constraints saying
`c.since >= DATE '2026-01-01'`,
only orders with `ts >= DATE '2026-01-01'` can reach the view's output.
Engines push down the predicates a query states; this one they do not
derive. `sverify.io` adds it to the source's condition, so it prunes the
data files of older orders (`SubstraitLean/Pruning.lean`).

`Rel.need` finds it. It pushes a demand, a condition on a node's output
rows, down the plan: a filter adds its condition, an emit or a projection
rewrites the demand over its input's columns (`Expr.subst`), and a union
passes it to both sides. At a read of the table, under a cross product or
an inner join with an input that does not read the table, the demand and
the join condition are refined (`Expr.refine`) on the abstract values of
the other input (`Rel.aeval`, from its preconditions and facts): the result
is an abstract row that every row of the table reaching the output lies in.
Anywhere else the table is read (under an aggregate, a window, a left join,
a `FETCH`, …), `Rel.need` gives up.

`Rel.need_sound`: if two catalogs agree on every table but `t`, and on the
rows of `t` that pass a condition `P` implied by each abstract row
`Rel.need` returns (`anyCond` is one), the view has the same rows on both.
So reading only the rows of `t` that pass `P`, or only the files that may
hold such rows, changes no result.
-/

namespace Substrait

/-! ## Abstract rows as conditions -/

/-- `NOT (col j < lo) AND NOT (hi < col j)`, the sides the bound has, for a
column of numbers of kind `k` (constants of the column's kind, #923). -/
def boundConds (k : NumKind) (j : Nat) (b : Bound) : List Expr :=
  (match b.lo with
    | some l => [.un .not (.bin .lt (.field j) (.lit (k.val l)))]
    | none => []) ++
  (match b.hi with
    | some h => [.un .not (.bin .lt (.lit (k.val h)) (.field j))]
    | none => [])

/-- The columns of `E` that are certainly numbers of one kind within a
bound (no NULL, no booleans, no strings). -/
def envBounds (E : List AVal) : List (Nat × NumKind × Bound) :=
  (List.range E.length).filterMap fun j =>
    let a := E.getD j AVal.top
    if a.null = false ∧ a.tt = false ∧ a.ff = false ∧ a.str = false then
      match a.int, a.nk with
      | some b, some k => some (j, k, b)
      | _, _ => none
    else none

def andAll : List Expr → Expr
  | [] => .lit (.bool true)
  | e :: es => .bin .and e (andAll es)

def orAll : List Expr → Expr
  | [] => .lit (.bool false)
  | e :: es => .bin .or e (orAll es)

/-- A condition TRUE on every row in `E` (`envCond_of_mem`). -/
def envCond (E : List AVal) : Expr :=
  andAll ((envBounds E).flatMap fun (j, k, b) => boundConds k j b)

/-- A condition TRUE on every row in one of `Es`. -/
def anyCond (Es : List (List AVal)) : Expr := orAll (Es.map envCond)

theorem andAll_isTrue {row : Row} :
    ∀ {es : List Expr}, (∀ e ∈ es, (e.eval row).isTrue = true) → ((andAll es).eval row).isTrue = true
  | [], _ => rfl
  | e :: es, h => by
      simp only [andAll, Expr.eval, BinFn.apply, isTrue_and3, Bool.and_eq_true]
      exact ⟨h e List.mem_cons_self, andAll_isTrue fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

theorem orAll_isTrue {row : Row} :
    ∀ {es : List Expr} {e : Expr}, e ∈ es → (e.eval row).isTrue = true →
      ((orAll es).eval row).isTrue = true
  | [], _, h, _ => by simp at h
  | e' :: es, e, h, ht => by
      simp only [orAll, Expr.eval, BinFn.apply, isTrue_or3, Bool.or_eq_true]
      rcases List.mem_cons.mp h with rfl | h
      · exact .inl ht
      · exact .inr (orAll_isTrue h ht)

theorem boundConds_isTrue {k : NumKind} {j : Nat} {b : Bound} {i : Int} {row : Row}
    (hv : row.getD j .null = k.val i) (hb : b.Mem i) :
    ∀ e ∈ boundConds k j b, (e.eval row).isTrue = true := by
  intro e he
  simp only [boundConds, List.mem_append] at he
  rcases he with he | he
  · cases hl : b.lo with
    | none => simp [hl] at he
    | some l =>
        simp only [hl, List.mem_singleton] at he; subst he
        have := hb.1 l hl
        change (UnFn.apply .not (BinFn.apply .lt (row.getD j .null) (k.val l))).isTrue = true
        rw [hv]
        cases k <;> simp [NumKind.val, BinFn.apply, UnFn.apply] <;> omega
  · cases hh : b.hi with
    | none => simp [hh] at he
    | some h =>
        simp only [hh, List.mem_singleton] at he; subst he
        have := hb.2 h hh
        change (UnFn.apply .not (BinFn.apply .lt (k.val h) (row.getD j .null))).isTrue = true
        rw [hv]
        cases k <;> simp [NumKind.val, BinFn.apply, UnFn.apply] <;> omega

theorem envCond_of_mem {E : List AVal} {row : Row} (h : EnvMem E row) :
    ((envCond E).eval row).isTrue = true := by
  refine andAll_isTrue fun e he => ?_
  obtain ⟨⟨j, k, b⟩, hjb, he⟩ := List.mem_flatMap.mp he
  simp only [envBounds, List.mem_filterMap, List.mem_range] at hjb
  obtain ⟨j', _, hj'⟩ := hjb
  have h' : ∀ j, (E[j]?.getD AVal.top).Mem (row[j]?.getD .null) := fun j => by
    simpa only [List.getD_eq_getElem?_getD] using h j
  simp only [List.getD_eq_getElem?_getD] at hj'
  split at hj'
  · rename_i hc
    obtain ⟨hn, htt, hff, hs⟩ := hc
    split at hj'
    · rename_i b' k₀ hi hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hj'
      obtain ⟨h1, h2, h3⟩ := hj'
      subst h1 h2 h3
      have hm := h' j'
      have hv' : row.getD j' .null = row[j']?.getD .null := List.getD_eq_getElem?_getD ..
      rcases AVal.mem_cases hm with ⟨hv, hn'⟩ | ⟨k', i, b'', hv, hb'', hmem, hk'⟩ | ⟨_, ht⟩ | ⟨_, hf⟩ |
          ⟨_, _, hs', _⟩ | ⟨_, _, ht, _⟩
      · simp_all
      · rw [hi] at hb''; cases hb''
        rw [hk] at hk'; simp only [Option.all_some, beq_iff_eq] at hk'; subst hk'
        exact boundConds_isTrue (hv'.trans hv) hmem e he
      all_goals simp_all
    · cases hj'
  · cases hj'

theorem anyCond_of_mem {Es : List (List AVal)} {E : List AVal} (hE : E ∈ Es) {row : Row}
    (h : EnvMem E row) : ((anyCond Es).eval row).isTrue = true :=
  orAll_isTrue (List.mem_map_of_mem hE) (envCond_of_mem h)

/-! ## Abstract rows of the table's rows that matter -/

theorem envMem_top (n : Nat) (row : Row) : EnvMem (List.replicate n AVal.top) row := fun i => by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> exact AVal.mem_top _

theorem envMem_take {e : List AVal} {x y : Row} (h : EnvMem e (x ++ y)) (hx : x.length = n) :
    EnvMem (e.take n) x := fun i => by
  have hi := h i
  simp only [List.getD_eq_getElem?_getD] at *
  by_cases hin : i < n
  · rw [List.getElem?_take_of_lt hin]
    rwa [List.getElem?_append_left (by omega)] at hi
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    exact AVal.mem_top _

theorem envMem_drop {e : List AVal} {x y : Row} (h : EnvMem e (x ++ y)) (hx : x.length = n) :
    EnvMem (e.drop n) y := fun i => by
  have hi := h (n + i)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at *
  rwa [List.getElem?_append_right (by omega), show n + i - x.length = i by omega] at hi

/-! ## Comparisons of two columns -/

/-- `x_i ≥ x_j` (`x_i > x_j` with `strict`) is TRUE only on two values of
the same kind (two numbers of one kind, booleans, strings or lists). On
numbers, `x_i` is at least `x_j`'s lower bound and `x_j` at most `x_i`'s upper
bound; each side may be of a kind only if the other may be too. -/
def geTransfer (env : List AVal) (i j : Nat) (strict : Bool) : List AVal :=
  let ai := env.getD i AVal.top
  let aj := env.getD j AVal.top
  let d : Int := if strict then 1 else 0
  let ii : Option Bound := match ai.int, aj.int with
    | some bi, some bj => some (bi.meet ⟨bj.lo.map (· + d), none⟩)
    | _, _ => none
  let ij : Option Bound := match aj.int, ai.int with
    | some bj, some bi => some (bj.meet ⟨none, bi.hi.map (· - d)⟩)
    | _, _ => none
  let ai' : AVal :=
    ⟨ai.null, ii, ai.tt && (aj.tt || aj.ff), ai.ff && (aj.tt || aj.ff), ai.str && aj.str, ai.strs,
      ai.nk⟩
  let aj' : AVal :=
    ⟨aj.null, ij, aj.tt && (ai.tt || ai.ff), aj.ff && (ai.tt || ai.ff), aj.str && ai.str, aj.strs,
      aj.nk⟩
  refineCol (refineCol env i fun _ => ai') j fun _ => aj'

def cmpAtom (env : List AVal) : Expr → List AVal
  | .un .not (.bin .lt (.field i) (.field j)) => geTransfer env i j false
  | .bin .lt (.field j) (.field i) => geTransfer env i j true
  | _ => env

def Expr.cmpRefine (env : List AVal) : Expr → List AVal
  | .bin .and p q => q.cmpRefine (p.cmpRefine env)
  | e => cmpAtom env e

/-- `Expr.refine`, then `Expr.cmpRefine`. -/
def Expr.refineAll (e : Expr) (env : List AVal) : List AVal := e.cmpRefine (e.refine env)

/-- Under a cross product of `a` and `b` whose rows matter where `g` is
TRUE: the side that reads `t` (`true`: `a`), and the demand on its rows, a
condition TRUE on the rows of that side with some partner in the other.
`none` when both sides read `t`. -/
def crossDemand (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (t : String)
    (a b : Rel) (g : Expr) : Option (Bool × Expr) :=
  if !b.tables.contains t then
    some (true, envCond ((g.refineAll (List.replicate (a.arity cat) AVal.top ++
      b.aeval cat A F .none)).take (a.arity cat)))
  else if !a.tables.contains t then
    some (false, envCond ((g.refineAll (a.aeval cat A F .none ++
      List.replicate (b.arity cat) AVal.top)).drop (a.arity cat)))
  else none

/-- **Implied predicates.** For a demand `dm` on the rows of `r`: abstract
rows such that a row of `t` that reaches a row of `r` on which `dm` is TRUE
lies in one of them (`[]`: `r` does not read `t`). `none` where `t` is read
under an operator this does not see through. -/
def Rel.need (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (t : String) :
    Expr → Rel → Option (List (List AVal))
  | dm, .read s =>
      if s = t then some [dm.refineAll (List.replicate (cat t).arity AVal.top)] else some []
  | dm, .filter r c => if r.tables.contains t then r.need cat A F t (.bin .and c dm) else some []
  | dm, .emit r m =>
      if r.tables.contains t then r.need cat A F t (dm.subst (m.map .field)) else some []
  | dm, .project r es =>
      if r.tables.contains t then
        r.need cat A F t (dm.subst ((List.range (r.arity cat)).map .field ++ es))
      else some []
  | dm, .unionAll a b =>
      if (a.tables ++ b.tables).contains t then
        match a.need cat A F t dm, b.need cat A F t dm with
        | some x, some y => some (x ++ y)
        | _, _ => none
      else some []
  | dm, .cross a b =>
      if (a.tables ++ b.tables).contains t then
        match crossDemand cat A F t a b dm with
        | some (true, d) => a.need cat A F t d
        | some (false, d) => b.need cat A F t d
        | none => none
      else some []
  | dm, .join a b .inner on =>
      if (a.tables ++ b.tables).contains t then
        match crossDemand cat A F t a b (.bin .and on dm) with
        | some (true, d) => a.need cat A F t d
        | some (false, d) => b.need cat A F t d
        | none => none
      else some []
  | _, r => if r.tables.contains t then none else some []

/-! ## Soundness -/

/-- The kind of a value: comparisons are TRUE only within one kind, and
decimals only of one scale. -/
def Value.kind : Value → Nat
  | .null => 0 | .int _ => 1 | .bool _ => 2 | .str _ => 3 | .list _ => 4
  | .float _ => 5 | .date _ => 6 | .ts _ => 7 | .tod _ => 8 | .struct _ => 9
  | .dec s _ => 10 + s

theorem AVal.mem_transfer {a b a' : AVal} {u v : Value} (hu : a.Mem u) (hv : b.Mem v)
    (hk : u.kind = v.kind) (hn : a'.null = a.null) (htt : a'.tt = (a.tt && (b.tt || b.ff)))
    (hff : a'.ff = (a.ff && (b.tt || b.ff))) (hs : a'.str = (a.str && b.str))
    (hss : a'.strs = a.strs) (hnk : a'.nk = a.nk)
    (hi : ∀ (k : NumKind) n, u = k.val n → ∃ c, a'.int = some c ∧ c.Mem n) : a'.Mem u := by
  rcases AVal.mem_cases hu with ⟨rfl, h⟩ | ⟨k, n, _, rfl, _, _, hk'⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf⟩ |
      ⟨_, rfl, h1, h2⟩ | ⟨_, rfl | rfl, h1, h2, h3⟩
  · simpa [AVal.Mem, hn] using h
  · obtain ⟨c, hc, hm⟩ := hi k n rfl
    exact AVal.mem_val.mpr ⟨c, hc, hm, by rw [hnk]; exact hk'⟩
  all_goals
    cases v <;> simp [Value.kind] at hk <;> try omega
    all_goals simp_all [AVal.Mem]
  all_goals (rename_i y; cases y <;> (try simp_all))

/-- `<` with a number on the left is not NULL only against a number of the
same kind, where it compares their integers. -/
theorem lt_val_left {v : Value} {k : NumKind} {a : Int} (h : BinFn.apply .lt (k.val a) v ≠ .null) :
    ∃ b, v = k.val b ∧ BinFn.apply .lt (k.val a) v = .bool (decide (a < b)) := by
  cases k
  case dec s =>
    cases v
    case dec t b =>
      by_cases hst : s = t
      · subst hst; exact ⟨b, rfl, by simp [NumKind.val, BinFn.apply]⟩
      · simp [NumKind.val, BinFn.apply, hst] at h
    all_goals simp [NumKind.val, BinFn.apply] at h
  all_goals (cases v <;> simp [NumKind.val, BinFn.apply] at h ⊢)

theorem lt_val_right {u : Value} {k : NumKind} {b : Int} (h : BinFn.apply .lt u (k.val b) ≠ .null) :
    ∃ a, u = k.val a ∧ BinFn.apply .lt u (k.val b) = .bool (decide (a < b)) := by
  cases k
  case dec t =>
    cases u
    case dec s a =>
      by_cases hst : s = t
      · subst hst; exact ⟨a, rfl, by simp [NumKind.val, BinFn.apply]⟩
      · simp [NumKind.val, BinFn.apply, hst] at h
    all_goals simp [NumKind.val, BinFn.apply] at h
  all_goals (cases u <;> simp [NumKind.val, BinFn.apply] at h ⊢)

theorem Value.kind_val (k : NumKind) (a b : Int) : (k.val a).kind = (k.val b).kind := by
  cases k <;> rfl

/-- `<` that is not NULL compares two values of one kind. -/
theorem lt_kind {u v : Value} (h : BinFn.apply .lt u v ≠ .null) : u.kind = v.kind := by
  cases hu : u.numOf? with
  | some p =>
    obtain ⟨k, a⟩ := p
    have hu' := Value.numOf?_some hu; subst hu'
    obtain ⟨b, rfl, -⟩ := lt_val_left h
    exact Value.kind_val k a b
  | none =>
    cases hv : v.numOf? with
    | some p =>
      obtain ⟨k, b⟩ := p
      have hv' := Value.numOf?_some hv; subst hv'
      obtain ⟨a, rfl, -⟩ := lt_val_right h
      exact Value.kind_val k a b
    | none =>
      cases u <;> cases v <;> simp_all [Value.numOf?, BinFn.apply, Value.kind]

theorem not_null_of_isTrue_not {x : Value} (h : (UnFn.apply .not x).isTrue = true) : x ≠ .null := by
  rintro rfl; simp [UnFn.apply, Value.isTrue] at h

theorem not_null_of_isTrue {x : Value} (h : x.isTrue = true) : x ≠ .null := by
  rintro rfl; simp [Value.isTrue] at h

theorem not_lt_int_isTrue {u v : Value}
    (h : (UnFn.apply .not (BinFn.apply .lt u v)).isTrue = true) :
    (∀ (k : NumKind) a, u = k.val a → ∃ b, v = k.val b ∧ b ≤ a) ∧
      (∀ (k : NumKind) b, v = k.val b → ∃ a, u = k.val a ∧ b ≤ a) ∧ u.kind = v.kind := by
  have hn := not_null_of_isTrue_not h
  refine ⟨fun k a hu => ?_, fun k b hv => ?_, lt_kind hn⟩
  · subst hu
    obtain ⟨b, rfl, he⟩ := lt_val_left hn
    rw [he] at h; simp [UnFn.apply] at h
    exact ⟨b, rfl, h⟩
  · subst hv
    obtain ⟨a, rfl, he⟩ := lt_val_right hn
    rw [he] at h; simp [UnFn.apply] at h
    exact ⟨a, rfl, h⟩

theorem lt_int_isTrue {u v : Value} (h : (BinFn.apply .lt v u).isTrue = true) :
    (∀ (k : NumKind) a, u = k.val a → ∃ b, v = k.val b ∧ b + 1 ≤ a) ∧
      (∀ (k : NumKind) b, v = k.val b → ∃ a, u = k.val a ∧ b + 1 ≤ a) ∧ u.kind = v.kind := by
  have hn := not_null_of_isTrue h
  refine ⟨fun k a hu => ?_, fun k b hv => ?_, (lt_kind hn).symm⟩
  · subst hu
    obtain ⟨b, rfl, he⟩ := lt_val_right hn
    rw [he] at h; simp at h
    exact ⟨b, rfl, by omega⟩
  · subst hv
    obtain ⟨a, rfl, he⟩ := lt_val_left hn
    rw [he] at h; simp at h
    exact ⟨a, rfl, by omega⟩

theorem geTransfer_sound {env : List AVal} {row : Row} {i j : Nat} {strict : Bool}
    (h : EnvMem env row)
    (hi : ∀ (k : NumKind) a, row.getD i .null = k.val a →
      ∃ b, row.getD j .null = k.val b ∧ b + (if strict then 1 else 0) ≤ a)
    (hj : ∀ (k : NumKind) b, row.getD j .null = k.val b →
      ∃ a, row.getD i .null = k.val a ∧ b + (if strict then 1 else 0) ≤ a)
    (hk : (row.getD i .null).kind = (row.getD j .null).kind) :
    EnvMem (geTransfer env i j strict) row := by
  unfold geTransfer
  refine refineCol_sound (refineCol_sound h ?_) ?_
  · refine AVal.mem_transfer (h i) (h j) hk rfl rfl rfl rfl rfl rfl fun k a ha => ?_
    obtain ⟨b, hb, hba⟩ := hi k a ha
    have hmi := h i; have hmj := h j
    rw [ha, AVal.mem_val] at hmi; rw [hb, AVal.mem_val] at hmj
    obtain ⟨bi, hbi, hmi, -⟩ := hmi
    obtain ⟨bj, hbj, hmj, -⟩ := hmj
    refine ⟨bi.meet ⟨bj.lo.map (· + if strict then 1 else 0), none⟩,
      by simp only [List.getD_eq_getElem?_getD] at hbi hbj; simp [hbi, hbj],
      Bound.mem_meet hmi ⟨fun l hl => ?_, fun _ h => by cases h⟩⟩
    cases hjl : bj.lo with
    | none => simp [hjl] at hl
    | some l' =>
        simp only [hjl, Option.map_some, Option.some.injEq] at hl
        subst hl
        have := hmj.1 l' hjl
        cases strict <;> simp at hba ⊢ <;> omega
  · refine AVal.mem_transfer (h j) (h i) hk.symm rfl rfl rfl rfl rfl rfl fun k b hb => ?_
    obtain ⟨a, ha, hba⟩ := hj k b hb
    have hmi := h i; have hmj := h j
    rw [ha, AVal.mem_val] at hmi; rw [hb, AVal.mem_val] at hmj
    obtain ⟨bi, hbi, hmi, -⟩ := hmi
    obtain ⟨bj, hbj, hmj, -⟩ := hmj
    refine ⟨bj.meet ⟨none, bi.hi.map (· - if strict then 1 else 0)⟩,
      by simp only [List.getD_eq_getElem?_getD] at hbi hbj; simp [hbi, hbj],
      Bound.mem_meet hmj ⟨(fun _ h => by cases h), fun u hu => ?_⟩⟩
    cases hih : bi.hi with
    | none => simp [hih] at hu
    | some u' =>
        simp only [hih, Option.map_some, Option.some.injEq] at hu
        subst hu
        have := hmi.2 u' hih
        cases strict <;> simp at hba ⊢ <;> omega

theorem cmpAtom_sound {env : List AVal} {row : Row} (h : EnvMem env row) {e : Expr}
    (ht : (e.eval row).isTrue = true) : EnvMem (cmpAtom env e) row := by
  unfold cmpAtom
  split
  · rename_i i j
    have := not_lt_int_isTrue (u := row.getD i .null) (v := row.getD j .null) ht
    exact geTransfer_sound (strict := false) h (by simpa using this.1) (by simpa using this.2.1)
      this.2.2
  · rename_i j i
    have := lt_int_isTrue (u := row.getD i .null) (v := row.getD j .null) ht
    exact geTransfer_sound (strict := true) h (by simpa using this.1) (by simpa using this.2.1)
      this.2.2
  · exact h

theorem Expr.cmpRefine_sound {row : Row} :
    ∀ {env : List AVal} (e : Expr), EnvMem env row → (e.eval row).isTrue = true →
      EnvMem (e.cmpRefine env) row
  | env, .bin f p q, h, ht => by
      cases f
      case and =>
        simp only [Expr.eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at ht
        exact cmpRefine_sound q (cmpRefine_sound p h ht.1) ht.2
      all_goals (simp only [Expr.cmpRefine]; exact cmpAtom_sound h ht)
  | env, .lit _, h, ht | env, .field _, h, ht | env, .un _ _, h, ht
  | env, .ifThen _ _ _, h, ht | env, .hof _ _ _, h, ht => by
      simp only [Expr.cmpRefine]; exact cmpAtom_sound h ht

theorem Expr.refineAll_sound {env : List AVal} {row : Row} (e : Expr) (h : EnvMem env row)
    (ht : (e.eval row).isTrue = true) : EnvMem (e.refineAll env) row :=
  e.cmpRefine_sound (Expr.refine_sound env e h ht) ht


theorem filter_of_implies {L : Relation} {d p : Row → Bool} (h : ∀ x, d x = true → p x = true) :
    L.filter d = (L.filter p).filter d := by
  rw [List.filter_filter]
  exact List.filter_congr fun x _ => by
    cases hd : d x
    · simp
    · simp [h x hd]

/-- The hypotheses of `Rel.need_sound`: `cat₂` is `cat₁` but for the rows
of `t` that fail `P`. -/
structure SameOn (cat₁ cat₂ : Catalog) (t : String) (P : Expr) : Prop where
  wf₁ : cat₁.WF
  wf₂ : cat₂.WF
  other : ∀ s, s ≠ t → cat₂ s = cat₁ s
  arity : (cat₂ t).arity = (cat₁ t).arity
  rows : (cat₂ t).rows.filter (fun x => (P.eval x).isTrue) =
    (cat₁ t).rows.filter (fun x => (P.eval x).isTrue)

theorem SameOn.arities {cat₁ cat₂ : Catalog} {t : String} {P : Expr}
    (h : SameOn cat₁ cat₂ t P) (s : String) : (cat₂ s).arity = (cat₁ s).arity := by
  by_cases hs : s = t
  · subst hs; exact h.arity
  · rw [h.other s hs]

theorem SameOn.eval_free {cat₁ cat₂ : Catalog} {t : String} {P : Expr}
    (h : SameOn cat₁ cat₂ t P) {r : Rel} (hr : t ∉ r.tables) :
    r.eval cat₂ = r.eval cat₁ :=
  Rel.eval_congr h.arities fun s hs => by
    have : s ≠ t := fun e => by subst e; exact hr hs
    rw [h.other s this]

theorem flatMap_nil_of_not {α β : Type} {L : List α} {f : α → List β} {p : α → Bool}
    (h : ∀ x ∈ L, p x = false → f x = []) : L.flatMap f = (L.filter p).flatMap f := by
  induction L with
  | nil => rfl
  | cons x L ih =>
      have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
      cases hp : p x
      · simp [hp, h x List.mem_cons_self hp, ih']
      · simp [hp, ih']

theorem map_filter_nil_of_not {L : Relation} {f : Row → Row} {g p : Row → Bool}
    (h : ∀ y ∈ L, g (f y) = true → p y = true) :
    (L.map f).filter g = ((L.filter p).map f).filter g := by
  rw [List.filter_map, List.filter_map, List.filter_filter]
  congr 1
  exact List.filter_congr fun y hy => by
    cases hg : g (f y)
    · simp [Function.comp, hg]
    · simp [Function.comp, hg, h y hy hg]

theorem crossRows_filter_left {L B : Relation} {g : Expr} {d : Row → Bool}
    (h : ∀ x ∈ L, ∀ y ∈ B, (g.eval (x ++ y)).isTrue = true → d x = true) :
    (crossRows L B).filter (fun r => (g.eval r).isTrue) =
      (crossRows (L.filter d) B).filter (fun r => (g.eval r).isTrue) := by
  simp only [crossRows, List.filter_flatMap]
  refine flatMap_nil_of_not fun x hx hd => List.filter_eq_nil_iff.mpr fun r hr hg => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
  rw [h x hx y hy (by simpa using hg)] at hd; cases hd

theorem crossRows_filter_right {A L : Relation} {g : Expr} {d : Row → Bool}
    (h : ∀ x ∈ A, ∀ y ∈ L, (g.eval (x ++ y)).isTrue = true → d y = true) :
    (crossRows A L).filter (fun r => (g.eval r).isTrue) =
      (crossRows A (L.filter d)).filter (fun r => (g.eval r).isTrue) := by
  simp only [crossRows, List.filter_flatMap]
  exact flatMap_congr fun x hx => map_filter_nil_of_not fun y hy hg => h x hx y hy hg

/-- What `crossDemand` promises: on any catalog with `cat₁`'s arities, a
row of the side that reads `t` with a partner in the other side's rows on
`cat₁` meets the demand. -/
theorem crossDemand_sound {cat₁ : Catalog} {A : String → List AVal} {F : String → List Fact}
    {t : String} (hc₁ : cat₁.WF) (hA : ∀ s, ∀ row ∈ (cat₁ s).rows, EnvMem (A s) row)
    (hF : ∀ s, ∀ row ∈ (cat₁ s).rows, FactsHold (F s) row) {a b : Rel} {g d : Expr}
    (hwa : a.WF cat₁) (hwb : b.WF cat₁) {cat : Catalog} (hc : cat.WF)
    (har : ∀ s, (cat s).arity = (cat₁ s).arity) :
    (crossDemand cat₁ A F t a b g = some (true, d) →
      t ∉ b.tables ∧ ∀ x ∈ a.eval cat, ∀ y ∈ b.eval cat₁,
        (g.eval (x ++ y)).isTrue = true → (d.eval x).isTrue = true) ∧
    (crossDemand cat₁ A F t a b g = some (false, d) →
      t ∉ a.tables ∧ ∀ x ∈ a.eval cat₁, ∀ y ∈ b.eval cat,
        (g.eval (x ++ y)).isTrue = true → (d.eval y).isTrue = true) := by
  unfold crossDemand
  constructor
  · intro hcd
    split at hcd
    · rename_i hb
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hcd; subst hcd
      refine ⟨by simpa using hb, fun x hx y hy hg => envCond_of_mem (envMem_take (y := y) ?_ ?_)⟩
      · exact Expr.refineAll_sound g (EnvMem.append (envMem_top _ _)
          (Rel.aeval_sound hc₁ hA hF (WindowKeys.none_soundAll _) (sz := false) hwb (by simp) y hy)
          (by rw [List.length_replicate, Rel.eval_arity hc (Rel.wf_congr har hwa) x hx,
            Rel.arity_congr har])) hg
      · rw [Rel.eval_arity hc (Rel.wf_congr har hwa) x hx, Rel.arity_congr har]
    · split at hcd
      · simp at hcd
      · cases hcd
  · intro hcd
    split at hcd
    · simp at hcd
    · split at hcd
      · rename_i _ ha
        simp only [Option.some.injEq, Prod.mk.injEq] at hcd; obtain ⟨-, rfl⟩ := hcd
        refine ⟨by simpa using ha, fun x hx y hy hg => envCond_of_mem (envMem_drop (x := x) ?_ ?_)⟩
        · exact Expr.refineAll_sound g (EnvMem.append
            (Rel.aeval_sound hc₁ hA hF (WindowKeys.none_soundAll _) (sz := false) hwa (by simp) x hx)
            (envMem_top _ _) (by rw [Rel.aeval_length hwa, Rel.eval_arity hc₁ hwa x hx])) hg
        · exact Rel.eval_arity hc₁ hwa x hx
      · cases hcd

theorem filter_and {L : Relation} (c dm : Expr) :
    (L.filter fun x => (c.eval x).isTrue).filter (fun x => (dm.eval x).isTrue) =
      L.filter fun x => ((Expr.bin .and c dm).eval x).isTrue := by
  rw [List.filter_filter]
  exact List.filter_congr fun x _ => by
    simp only [Expr.eval, BinFn.apply, isTrue_and3, Bool.and_comm]

theorem cross_case {cat₁ cat₂ : Catalog} {A : String → List AVal}
    {F : String → List Fact} {t : String} {P : Expr} (hs : SameOn cat₁ cat₂ t P)
    (hA : ∀ s, ∀ row ∈ (cat₁ s).rows, EnvMem (A s) row)
    (hF : ∀ s, ∀ row ∈ (cat₁ s).rows, FactsHold (F s) row)
    {a b : Rel} {g : Expr} {Es : List (List AVal)} (hwa : a.WF cat₁) (hwb : b.WF cat₁)
    (hn : (match crossDemand cat₁ A F t a b g with
      | some (true, d) => a.need cat₁ A F t d
      | some (false, d) => b.need cat₁ A F t d
      | none => none) = some Es)
    (hP : ∀ E ∈ Es, ∀ row, EnvMem E row → (P.eval row).isTrue = true)
    (iha : a.WF cat₁ → ∀ d, a.need cat₁ A F t d = some Es →
      (∀ E ∈ Es, ∀ row, EnvMem E row → (P.eval row).isTrue = true) →
      (a.eval cat₂).filter (fun x => (d.eval x).isTrue) =
        (a.eval cat₁).filter (fun x => (d.eval x).isTrue))
    (ihb : b.WF cat₁ → ∀ d, b.need cat₁ A F t d = some Es →
      (∀ E ∈ Es, ∀ row, EnvMem E row → (P.eval row).isTrue = true) →
      (b.eval cat₂).filter (fun x => (d.eval x).isTrue) =
        (b.eval cat₁).filter (fun x => (d.eval x).isTrue)) :
    (crossRows (a.eval cat₂) (b.eval cat₂)).filter (fun x => (g.eval x).isTrue) =
      (crossRows (a.eval cat₁) (b.eval cat₁)).filter (fun x => (g.eval x).isTrue) := by
  cases hcd : crossDemand cat₁ A F t a b g with
  | none => rw [hcd] at hn; cases hn
  | some p =>
    obtain ⟨side, d⟩ := p
    rw [hcd] at hn
    have s₂ := crossDemand_sound hs.wf₁ hA hF hwa hwb hs.wf₂ hs.arities (t := t) (g := g) (d := d)
    have s₁ := crossDemand_sound hs.wf₁ hA hF hwa hwb hs.wf₁ (fun _ => rfl) (t := t) (g := g)
      (d := d)
    cases side
    · obtain ⟨hfree, h₂⟩ := s₂.2 hcd
      have h₁ := (s₁.2 hcd).2
      rw [hs.eval_free hfree, crossRows_filter_right (d := fun y => (d.eval y).isTrue) h₂,
        crossRows_filter_right (d := fun y => (d.eval y).isTrue) h₁, ihb hwb d hn hP]
    · obtain ⟨hfree, h₂⟩ := s₂.1 hcd
      have h₁ := (s₁.1 hcd).2
      rw [hs.eval_free hfree]
      rw [crossRows_filter_left (d := fun x => (d.eval x).isTrue) h₂,
        crossRows_filter_left (d := fun x => (d.eval x).isTrue) h₁, iha hwa d hn hP]

/-- **Pushing an implied predicate to a base table.** If `Rel.need` finds
abstract rows `Es` for table `t`, each implying `P`, then on two catalogs
that differ only in rows of `t` that fail `P`, the plan's rows on which the
demand is TRUE are the same, in the same order. With the demand TRUE, the
plan's result is the same (`Rel.need_eval`). -/
theorem Rel.need_sound {cat₁ cat₂ : Catalog} {A : String → List AVal}
    {F : String → List Fact} {t : String} {P : Expr} (hs : SameOn cat₁ cat₂ t P)
    (hA : ∀ s, ∀ row ∈ (cat₁ s).rows, EnvMem (A s) row)
    (hF : ∀ s, ∀ row ∈ (cat₁ s).rows, FactsHold (F s) row) :
    ∀ {r : Rel} {dm : Expr} {Es : List (List AVal)}, r.WF cat₁ →
      r.need cat₁ A F t dm = some Es →
      (∀ E ∈ Es, ∀ row, EnvMem E row → (P.eval row).isTrue = true) →
      (r.eval cat₂).filter (fun x => (dm.eval x).isTrue) =
        (r.eval cat₁).filter (fun x => (dm.eval x).isTrue)
  | .read s, dm, Es, _, hn, hP => by
      simp only [need] at hn
      split at hn
      · rename_i hst; subst hst
        simp only [Option.some.injEq] at hn; subst hn
        simp only [eval]
        have imp : ∀ x, (dm.eval x).isTrue = true → (P.eval x).isTrue = true := fun x hx =>
          hP _ List.mem_cons_self x (Expr.refineAll_sound dm (envMem_top _ x) hx)
        rw [filter_of_implies (L := (cat₂ s).rows) imp, filter_of_implies (L := (cat₁ s).rows) imp,
          hs.rows]
      · rename_i hst
        simp only [eval, hs.other s hst]
  | .filter r c, dm, Es, hw, hn, hP => by
      simp only [need] at hn
      split at hn
      · simp only [eval, filter_and]
        exact need_sound hs hA hF hw.1 hn hP
      · rename_i hc
        rw [hs.eval_free (r := .filter r c) (by simpa [tables] using hc)]
  | .emit r m, dm, Es, hw, hn, hP => by
      simp only [need] at hn
      split at hn
      · have ih := need_sound hs hA hF hw.1 hn hP
        simp only [eval, List.filter_map]
        have hc : ∀ x : Row, (dm.subst (m.map .field)).eval x =
            dm.eval (m.map (x.getD · .null)) := fun x => by
          rw [Expr.eval_subst, List.map_map]; rfl
        have e₁ : ∀ (L : Relation), L.filter ((fun x => (dm.eval x).isTrue) ∘
            fun row => m.map (row.getD · .null)) =
            L.filter fun x => ((dm.subst (m.map .field)).eval x).isTrue :=
          fun L => List.filter_congr fun x _ => by simp [Function.comp, hc]
        rw [e₁, e₁, ih]
      · rename_i hc
        rw [hs.eval_free (r := .emit r m) (by simpa [tables] using hc)]
  | .project r es, dm, Es, hw, hn, hP => by
      simp only [need] at hn
      split at hn
      · have ih := need_sound hs hA hF hw.1 hn hP
        simp only [eval, List.filter_map]
        have hc : ∀ x : Row, x.length = r.arity cat₁ →
            (dm.subst ((List.range (r.arity cat₁)).map .field ++ es)).eval x =
              dm.eval (x ++ es.map (·.eval x)) := fun x hx => by
          rw [Expr.eval_subst, List.map_append, List.map_map]
          congr 1
          congr 1
          rw [← hx]
          apply List.ext_getElem (by simp)
          intro i h₁ h₂
          simp [Expr.eval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₁)]
        have e₁ : ∀ (L : Relation), (∀ x ∈ L, x.length = r.arity cat₁) →
            L.filter ((fun x => (dm.eval x).isTrue) ∘ fun row => row ++ es.map (·.eval row)) =
            L.filter fun x => ((dm.subst ((List.range (r.arity cat₁)).map .field ++ es)).eval
              x).isTrue :=
          fun L hL => List.filter_congr fun x hx => by simp [Function.comp, hc x (hL x hx)]
        rw [e₁ _ fun x hx => (Rel.eval_arity hs.wf₂ (Rel.wf_congr hs.arities hw.1) x hx).trans
            (Rel.arity_congr hs.arities r),
          e₁ _ fun x hx => Rel.eval_arity hs.wf₁ hw.1 x hx, ih]
      · rename_i hc
        rw [hs.eval_free (r := .project r es) (by simpa [tables] using hc)]
  | .unionAll a b, dm, Es, hw, hn, hP => by
      simp only [need] at hn
      split at hn
      · split at hn
        · rename_i x y hx hy
          simp only [Option.some.injEq] at hn; subst hn
          simp only [eval, List.filter_append]
          rw [need_sound hs hA hF hw.1 hx fun E hE => hP E (List.mem_append_left _ hE),
            need_sound hs hA hF hw.2.1 hy fun E hE => hP E (List.mem_append_right _ hE)]
        · cases hn
      · rename_i hc
        rw [hs.eval_free (r := .unionAll a b) (by simpa [tables] using hc)]
  | .cross a b, dm, Es, hw, hn, hP => by
      simp only [need] at hn
      split at hn
      · simp only [eval]
        exact cross_case hs hA hF hw.1 hw.2 hn hP
          (fun hwa d hd hP' => need_sound hs hA hF hwa hd hP')
          (fun hwb d hd hP' => need_sound hs hA hF hwb hd hP')
      · rename_i hc
        rw [hs.eval_free (r := .cross a b) (by simpa [tables] using hc)]
  | .join a b .inner on, dm, Es, hw, hn, hP => by
      simp only [need] at hn
      split at hn
      · simp only [eval, filter_and]
        exact cross_case hs hA hF hw.1 hw.2.1 hn hP
          (fun hwa d hd hP' => need_sound hs hA hF hwa hd hP')
          (fun hwb d hd hP' => need_sound hs hA hF hwb hd hP')
      · rename_i hc
        rw [hs.eval_free (r := .join a b .inner on) (by simpa [tables] using hc)]
  | .join a b .left on, dm, Es, _, hn, _
  | .values n rows, dm, Es, _, hn, _ | .fetch r o c, dm, Es, _, hn, _
  | .window r p s f, dm, Es, _, hn, _ | .semi a b x on, dm, Es, _, hn, _
  | .orderBy r k, dm, Es, _, hn, _ | .distinct r, dm, Es, _, hn, _
  | .aggregate r g m, dm, Es, _, hn, _ | .unnest r c, dm, Es, _, hn, _ => by
      simp only [need] at hn
      split at hn
      · cases hn
      · rename_i hc
        rw [hs.eval_free (by simpa using hc)]

/-- With the demand TRUE (`Rel.need` at the plan's root), the result is the
same: a view reads the same rows from `t` restricted to `anyCond Es`. -/
theorem Rel.need_eval {cat₁ cat₂ : Catalog} {A : String → List AVal}
    {F : String → List Fact} {t : String} {r : Rel} {Es : List (List AVal)}
    (hs : SameOn cat₁ cat₂ t (anyCond Es))
    (hA : ∀ s, ∀ row ∈ (cat₁ s).rows, EnvMem (A s) row)
    (hF : ∀ s, ∀ row ∈ (cat₁ s).rows, FactsHold (F s) row) (hw : r.WF cat₁)
    (hn : r.need cat₁ A F t (.lit (.bool true)) = some Es) : r.eval cat₂ = r.eval cat₁ := by
  have := need_sound hs hA hF hw hn fun E hE row hm => anyCond_of_mem hE hm
  have h1 : ∀ L : Relation, L.filter (fun _ => true) = L := fun L => List.filter_eq_self.mpr (by simp)
  simpa [Expr.eval, Value.isTrue, h1] using this

end Substrait
