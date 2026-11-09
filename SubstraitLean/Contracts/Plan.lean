import SubstraitLean.Contracts.Facts

/-!
# Contracts: Plan

Abstract plan evaluation: row counts and float error bounds (#85), the
`Rel.aeval` mutual, its one-pass form `Rel.lane` (#903) and the `@[csimp]`
lemmas that run it.

Part of `SubstraitLean.Contracts`, which re-exports it. -/

namespace Substrait

/-! ## Abstract plan evaluation -/

/-- Exactly `n` columns: missing ones are unknown. -/
def fit (n : Nat) (env : List AVal) : List AVal := (List.range n).map (env.getD · AVal.top)



/-- Sums of integers in `b` keep their sign. -/
def sumBound (b : Bound) : Bound :=
  ⟨b.lo.bind fun l => if 0 ≤ l then some 0 else none,
   b.hi.bind fun h => if h ≤ 0 then some 0 else none⟩

/-- A non-empty sum of integers in `b`: at least `b`'s lower bound where that
is not negative (the other terms are not negative), at most its upper bound
where that is not positive. -/
def sumBoundPos (b : Bound) : Bound :=
  ⟨b.lo.bind fun l => if 0 ≤ l then some l else none,
   b.hi.bind fun h => if h ≤ 0 then some h else none⟩

/-- A sum of at most `n` integers in `b` (#470): at least `n` times its lower
bound where that is negative, and 0 otherwise (no terms sum to 0); at most
`n` times its upper bound where that is positive, and 0 otherwise. -/
def sumCap (b : Bound) (n : Nat) : Bound :=
  ⟨b.lo.map fun l => min 0 (n * l), b.hi.map fun h => max 0 (n * h)⟩

/-- Every value but NULL is a number of kind `k`. -/
def AVal.kindOnly (k : NumKind) (a : AVal) : Bool := a.intsOnly && a.nk == some k

/-- Every value but NULL is an integer, or a decimal of one scale: `intSum`
adds them all. -/
def AVal.unscaledOnly (a : AVal) : Bool :=
  a.intsOnly && match a.nk with
    | some .int | some (.dec _) => true
    | _ => false

/-- The kind of a `SUM` of `a`'s values (`sumOf`): an integer of integers, a
decimal of decimals of one scale. -/
def sumKind (a : AVal) : Option NumKind :=
  match a.nk with
  | some .int => some .int
  | some (.dec s) => if a.intsOnly then some (.dec s) else none
  | _ => none

/-- Some double, or NULL. -/
def AVal.double : AVal := { null := true, int := some Bound.top, nk := some .float }

/-! ### Row counts and float error bounds (#85) -/

/-- An upper bound on the number of rows of a plan. Reads have none of their
own: `sverify` wraps the reads of tables with a `max_rows` precondition in a
`FETCH` of that many rows (`Rel.capReads`), which keeps their rows. -/
def Rel.maxRows : Rel → Option Nat
  | .read _ => none
  | .values _ rows => some rows.length
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ | .distinct r | .semi r _ _ _
  | .window r _ _ _ => r.maxRows
  | .fetch r _ cnt => match cnt, r.maxRows with
    | some k, some n => some (min k n)
    | some k, none => some k
    | none, n => n
  | .cross a b | .join a b .inner _ => a.maxRows.bind fun n => b.maxRows.map (n * ·)
  | .join _ _ .left _ => none
  | .unionAll a b => a.maxRows.bind fun n => b.maxRows.map (n + ·)
  | .aggregate r gs _ => if gs.isEmpty then some 1 else r.maxRows
  | .unnest _ _ => none

theorem length_crossRows (xs ys : Relation) : (crossRows xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [crossRows]
  | cons x xs ih =>
    simp only [crossRows, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih, List.length_cons, Nat.add_mul, Nat.one_mul]; omega

/-- **Row bounds hold on every order**, `Rel.eval`'s among them. -/
theorem Rel.maxRows_sound_all {cat : Catalog} :
    ∀ {r : Rel} {n : Nat}, r.maxRows = some n → ∀ {out : Relation}, r.OrderAllowed cat out →
      out.length ≤ n
  | .read _, _, h, _, _ => by simp [maxRows] at h
  | .values _ _, _, h, _, ho => by
    simp only [maxRows, Option.some.injEq] at h; rw [ho.length_eq, h]; exact Nat.le_refl _
  | .filter r _, _, h, _, ⟨i, hi, rfl⟩ => by
    simp only [maxRows] at h
    exact Nat.le_trans (List.length_filter_le _ _) (maxRows_sound_all (r := r) h hi)
  | .project r _, _, h, _, ⟨i, hi, rfl⟩ | .emit r _, _, h, _, ⟨i, hi, rfl⟩ => by
    simp only [maxRows] at h; simp only [List.length_map]; exact maxRows_sound_all (r := r) h hi
  | .orderBy r _, _, h, _, ⟨i, hi, hp, _⟩ => by
    simp only [maxRows] at h; rw [hp.length_eq]; exact maxRows_sound_all (r := r) h hi
  | .distinct r, _, h, _, ⟨i, hi, _, hd, hp⟩ => by
    simp only [maxRows] at h; rw [hp.length_eq]
    exact Nat.le_trans hd.length_le (maxRows_sound_all (r := r) h hi)
  | .semi r _ _ _, _, h, _, ⟨i, _, hi, _, hp⟩ => by
    simp only [maxRows] at h; rw [hp.length_eq]
    exact Nat.le_trans (List.length_filter_le _ _) (maxRows_sound_all (r := r) h hi)
  | .window r _ _ _, _, h, _, ⟨i, hi, s, hs, _, hp⟩ => by
    simp only [maxRows] at h
    rw [hp.length_eq, windowRows_length, hs.length_eq]
    exact maxRows_sound_all (r := r) h hi
  | .fetch r _ cnt, n, h, _, ⟨i, hi, rfl⟩ => by
    cases cnt with
    | none =>
      simp only [maxRows] at h
      have := maxRows_sound_all (cat := cat) h hi
      simp only [List.length_drop]; omega
    | some k =>
      cases hr : r.maxRows with
      | none =>
        simp only [maxRows, hr, Option.some.injEq] at h
        subst h; simp only [List.length_take]; exact Nat.min_le_left _ _
      | some m =>
        simp only [maxRows, hr, Option.some.injEq] at h
        subst h
        have := maxRows_sound_all (cat := cat) hr hi
        simp only [List.length_take, List.length_drop]; omega
  | .cross a b, n, h, _, ⟨x, y, hx, hy, hp⟩ => by
    simp only [maxRows, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨na, ha, nb, hb, rfl⟩ := h
    rw [hp.length_eq, length_crossRows]
    exact Nat.mul_le_mul (maxRows_sound_all ha hx) (maxRows_sound_all hb hy)
  | .join a b .inner _, n, h, _, ⟨x, y, hx, hy, hp⟩ => by
    simp only [maxRows, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨na, ha, nb, hb, rfl⟩ := h
    rw [hp.length_eq]
    exact Nat.le_trans (List.length_filter_le _ _)
      (by rw [length_crossRows]; exact Nat.mul_le_mul (maxRows_sound_all ha hx) (maxRows_sound_all hb hy))
  | .join _ _ .left _, _, h, _, _ => by simp [maxRows] at h
  | .unionAll a b, n, h, _, ⟨x, y, hx, hy, hp⟩ => by
    simp only [maxRows, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨na, ha, nb, hb, rfl⟩ := h
    rw [hp.length_eq, List.length_append]
    exact Nat.add_le_add (maxRows_sound_all ha hx) (maxRows_sound_all hb hy)
  | .aggregate r gs _, n, h, _, ⟨i, hi, o, hp, ho⟩ => by
    simp only [maxRows] at h
    rw [hp.length_eq]
    unfold aggOrderAllowed at ho
    split at h
    · rename_i hg
      simp only [Option.some.injEq] at h; subst h
      simp only [hg, ite_true] at ho
      obtain ⟨_, rfl, _⟩ := ho; exact Nat.le_refl _
    · rename_i hg
      simp only [hg, Bool.false_eq_true, ite_false] at ho
      obtain ⟨ks, hks, ho⟩ := ho
      rw [← ho.length_eq]
      exact Nat.le_trans hks.length_le (by simpa using maxRows_sound_all (r := r) h hi)
  | .unnest _ _, _, h, _, _ => by simp [maxRows] at h

theorem Rel.maxRows_sound {cat : Catalog} {r : Rel} {n : Nat} (h : r.maxRows = some n) :
    (r.eval cat).length ≤ n :=
  Rel.maxRows_sound_all h (r.eval_orderAllowed cat)

/-- Each read of a table with a row cap, as a `FETCH` of at most that many
rows. On tables within their caps it changes nothing (`Rel.capReads_eval`),
and `Rel.maxRows` sees the caps. -/
def Rel.capReads (caps : String → Option Nat) : Rel → Rel
  | .read t => match caps t with
    | some n => .fetch (.read t) 0 (some n)
    | none => .read t
  | .values n rows => .values n rows
  | .filter r c => .filter (r.capReads caps) c
  | .project r es => .project (r.capReads caps) es
  | .emit r m => .emit (r.capReads caps) m
  | .cross a b => .cross (a.capReads caps) (b.capReads caps)
  | .join a b ty on => .join (a.capReads caps) (b.capReads caps) ty on
  | .fetch r o c => .fetch (r.capReads caps) o c
  | .unionAll a b => .unionAll (a.capReads caps) (b.capReads caps)
  | .window r p s fns => .window (r.capReads caps) p s fns
  | .semi a b anti on => .semi (a.capReads caps) (b.capReads caps) anti on
  | .orderBy r k => .orderBy (r.capReads caps) k
  | .distinct r => .distinct (r.capReads caps)
  | .aggregate r gs ms => .aggregate (r.capReads caps) gs ms
  | .unnest r c => .unnest (r.capReads caps) c

theorem Rel.capReads_arity (caps : String → Option Nat) (cat : Catalog) :
    ∀ r : Rel, (r.capReads caps).arity cat = r.arity cat
  | .read t => by unfold capReads; split <;> rfl
  | .values _ _ => rfl
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .semi r _ _ _ => by
    simp only [capReads, arity]; exact capReads_arity caps cat r
  | .project r es => by simp only [capReads, arity, capReads_arity caps cat r]
  | .emit _ _ => rfl
  | .cross a b | .join a b _ _ => by
    simp only [capReads, arity, capReads_arity caps cat a, capReads_arity caps cat b]
  | .unionAll a _ => by simp only [capReads, arity, capReads_arity caps cat a]
  | .window r _ _ _ => by simp only [capReads, arity, capReads_arity caps cat r]
  | .aggregate _ _ _ => rfl
  | .unnest r _ => by simp only [capReads, arity, capReads_arity caps cat r]

/-- **Capping reads changes nothing** on tables within their caps. -/
theorem Rel.capReads_eval {caps : String → Option Nat} {cat : Catalog}
    (h : ∀ t n, caps t = some n → (cat t).rows.length ≤ n) :
    ∀ r : Rel, (r.capReads caps).eval cat = r.eval cat
  | .read t => by
    unfold capReads
    split
    · rename_i n hn
      simp only [eval, List.drop_zero]
      exact List.take_of_length_le (h t n hn)
    · rfl
  | .values _ _ => rfl
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .window r _ _ _ | .unnest r _ | .aggregate r _ _ => by
    simp only [capReads, eval, capReads_eval h r]
  | .cross a b | .unionAll a b | .semi a b _ _ => by
    simp only [capReads, eval, capReads_eval h a, capReads_eval h b]
  | .join a b ty _ => by
    cases ty <;> simp only [capReads, eval, capReads_eval h a, capReads_eval h b,
      capReads_arity caps cat b]

/-- The mean of the doubles `cs`, as `AggFn.avg` computes it. -/
def avgCode (cs : List Int) : Int := floatAvgCR (cs.map .float)

/-- The codes a `SUM` (`avg = false`) or an `AVG` of doubles in `b` lies in:
signs are exact (`floatSumCR_sign`), and with at most `rows` values, finite
bounds and at most `2³²` rows, the result is within the proved tolerance of
the exact one (`floatSumCR_mem`, `floatAvgCR_mem`). -/
def floatBound (avg : Bool) (b : Bound) (rows : Option Nat) : Bound :=
  let signed : Bound :=
    ⟨b.lo.bind fun l => if 0 ≤ l then some 0 else none,
     b.hi.bind fun h => if h ≤ 0 then some 0 else none⟩
  match b.lo, b.hi, rows with
  | some cl, some ch, some n =>
    let lo := FloatCode.scaled cl
    let hi := FloatCode.scaled ch
    if n ≤ 2 ^ 32 ∧ lo.natAbs ≤ 2 ^ 1474 ∧ hi.natAbs ≤ 2 ^ 1474 then
      let Bs := max lo.natAbs hi.natAbs
      if avg then
        let t : Int := FloatCode.avgTolScaled n Bs
        signed.meet ⟨some (FloatCode.codeLo (lo - t)), some (FloatCode.codeHi (hi + t))⟩
      else
        let t : Int := FloatCode.sumTolScaled n Bs
        signed.meet ⟨some (FloatCode.codeLo (min lo (n * lo) - t)),
          some (FloatCode.codeHi (max hi (n * hi) + t))⟩
    else signed
  | _, _, _ => signed

theorem floatBound_sound {avg : Bool} {b : Bound} {rows : Option Nat} {cs : List Int}
    (hne : cs ≠ []) (hb : ∀ c ∈ cs, b.Mem (FloatCode.canon c)) (hrows : ∀ n, rows = some n → cs.length ≤ n) :
    (floatBound avg b rows).Mem (if avg then avgCode cs else floatSumCR (cs.map .float)) := by
  obtain ⟨blo, bhi⟩ := b
  have hsign := floatSumCR_sign hne
  have hsigned : (Bound.mk (blo.bind fun l => if 0 ≤ l then some 0 else none)
      (bhi.bind fun h => if h ≤ 0 then some 0 else none)).Mem
      (if avg then avgCode cs else floatSumCR (cs.map .float)) := by
    constructor
    · intro l hl
      simp only [Option.bind_eq_some_iff] at hl
      obtain ⟨l', hl', h⟩ := hl
      split at h
      · rename_i h0
        cases h
        have := (hsign.1 fun c hc => Int.le_trans h0 ((hb c hc).1 l' hl'))
        cases avg <;> simp only [Bool.false_eq_true, ↓reduceIte, avgCode] <;> omega
      · simp at h
    · intro u hu
      simp only [Option.bind_eq_some_iff] at hu
      obtain ⟨u', hu', h⟩ := hu
      split at h
      · rename_i h0
        cases h
        have := (hsign.2 fun c hc => Int.le_trans ((hb c hc).2 u' hu') h0)
        cases avg <;> simp only [Bool.false_eq_true, ↓reduceIte, avgCode] <;> omega
      · simp at h
  rcases blo with _ | cl
  · exact hsigned
  rcases bhi with _ | ch
  · exact hsigned
  rcases rows with _ | n
  · exact hsigned
  have hlen := hrows n rfl
  have hsc : ∀ c ∈ cs, FloatCode.scaled cl ≤ FloatCode.scaled (FloatCode.canon c) ∧
      FloatCode.scaled (FloatCode.canon c) ≤ FloatCode.scaled ch := fun c hc =>
    ⟨FloatCode.scaled_mono ((hb c hc).1 cl rfl), FloatCode.scaled_mono ((hb c hc).2 ch rfl)⟩
  simp only [floatBound]
  split
  · rename_i hok
    obtain ⟨h32, hlo, hhi⟩ := hok
    cases avg
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsigned ⊢
      obtain ⟨l, u⟩ := floatSumCR_mem hne hlen h32 hlo hhi hsc
      refine Bound.mem_meet hsigned ⟨?_, ?_⟩
      · intro x hx; cases hx; exact FloatCode.codeLo_le l
      · intro x hx; cases hx; exact FloatCode.le_codeHi u
    · simp only [↓reduceIte] at hsigned ⊢
      obtain ⟨l, u⟩ := floatAvgCR_mem hne hlen h32 hlo hhi hsc
      refine Bound.mem_meet hsigned ⟨?_, ?_⟩
      · intro x hx; cases hx; exact FloatCode.codeLo_le l
      · intro x hx; cases hx; exact FloatCode.le_codeHi u
  · exact hsigned

/-- A measure over rows described by `env` and `fs`: a count is a natural
number, a sum of integers keeps their sign, `MIN`, `MAX` and an integer
`AVG` are within the argument's values, and the other measures are doubles. All but
`COUNT` may be NULL, unless a group has a value (`grouped`, #372). -/
def Measure.abs (env : List AVal) (fs : List Fact) (m : Measure) (grouped : Bool := false)
    (rows : Option Nat := none) : AVal :=
  let a := m.arg.absD env fs
  -- A group has a row (`grouped`), so a measure of a never-NULL argument
  -- without a filter has a value: `COUNT(*)` per group is at least 1.
  let valued := grouped && m.filter.isNone && !a.null
  match m.fn with
  | .count => { int := some (Bound.ge (if valued then 1 else 0)), nk := some .int }
  -- A sum is over at least one input (none: NULL), so with integer inputs
  -- it is at least the smallest one, if that is not negative.
  -- With at most `rows` rows, at most `rows` times the largest value (#470).
  | .sum =>
    let b := match a.int with
      | some b => (if a.unscaledOnly then sumBoundPos b else sumBound b).meet
          (match rows with
            | some n => sumCap b n
            | none => Bound.top)
      | none => Bound.top
    { null := !valued, int := some b, nk := sumKind a }
  -- Doubles round: within the proved error bound of the exact sum or mean
  -- when the values are finite and there are at most `rows` of them (#85).
  | .fsum =>
    let b := if a.kindOnly .float then floatBound false (a.int.getD Bound.top) rows else Bound.top
    { null := !valued, int := some b, nk := some .float }
  | .avg =>
    let b := if a.kindOnly .float then floatBound true (a.int.getD Bound.top) rows else Bound.top
    { null := !valued, int := some b, nk := some .float }
  -- Between the smallest and the largest value (`AggFn.iavg`, #237).
  | .iavg =>
    { null := !valued, int := some (if a.kindOnly .int then a.int.getD Bound.top else Bound.top),
      nk := some .int }
  | .cov _ | .corr => AVal.double
  -- Some double that is not negative (NaN is above every number), or NULL.
  | .var _ _ => { null := true, int := some ⟨some 0, none⟩, nk := some .float }
  | .bit _ => { null := true, int := some Bound.top, nk := some .int }
  | .min | .max => if valued then a else a.nullable
  -- One of the values, in the measure's order (#55).
  | .pick _ => a.nullable
  -- A string, or NULL without values.
  | .concat _ => { null := true, str := true }
  -- One of the values (#53).
  | .quantile false _ _ | .mode => a.nullable
  -- A double between two of the values: within the argument's interval.
  | .quantile true _ _ => { null := true, int := a.int, nk := some .float }
  -- A list of the argument's non-NULL values, at least one; NULL without (#925).
  | .collect =>
    { null := true, list := true, elems := some { a with null := false }, card := .ge 1 }
  -- A black box's laws over values; its `empty` value without (#325).
  | .bbox n => BlackBox.aggAbs n valued

/-- `ROW_NUMBER` and the ranks are positive integers, at most `Text.rowCap`
by the size hypothesis for relations (`Rel.Small`) when `sz` says to use
it; `LAG`/`LEAD` read a
value of the same column of another input row, or give the default;
`PERCENT_RANK` and `CUME_DIST` are doubles. An aggregate over a frame is
described like one over a group (`Measure.abs`); `FIRST_VALUE` and friends
may be anything. -/
def WinFn.abs (sz : Bool) (env : List AVal) : WinFn → AVal
  | .rowNumber | .rank _ | .denseRank _ | .ntile _ =>
    { int := some ⟨some 1, if sz then some Text.rowCap else none⟩, nk := some .int }
  | .percentRank _ | .cumeDist _ => { int := some Bound.top, nk := some .float }
  -- An aggregate over a frame, rows of the input: a sum of non-negative
  -- integers is not negative, `MIN` and `MAX` are among the inputs (#229).
  | .agg m _ _ => m.abs env []
  | .firstValue _ _ _ | .lastValue _ _ _ | .nthValue _ _ _ _ => AVal.top
  | .lag c _ d | .lead c _ d => (env.getD c AVal.top).join (AVal.ofValue d)

/-- `ratio` facts for a `SUM` and a `COUNT` of the same values, which a
decimal `AVG` divides (`Parse.decimalAvgs`, #237): the sum is of as many
integers as the count, each within the bound `env` and `fs` give the values. -/
def ratioFacts (g : Nat) (env : List AVal) (fs : List Fact) (ms : List Measure) : List Fact :=
  (List.range ms.length).flatMap fun i => (List.range ms.length).flatMap fun j =>
    match ms[i]?, ms[j]? with
    | some mi, some mj =>
      let a := mi.arg.absD env fs
      if mi.fn = .sum ∧ mj.fn = .count ∧ mj.arg = mi.arg ∧ mj.filter = mi.filter ∧
          mj.distinct = mi.distinct ∧ a.unscaledOnly = true then
        match a.int with
        | some b => [.ratio (g + i) (g + j) b]
        | none => []
      else []
    | _, _ => []


mutual
/-- Abstract evaluation. `A t` describes the columns of table `t`; `F t` holds
facts about its rows. Computed columns use the facts of their input. -/
def Rel.aeval (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys)
    (sz : Bool := false) : Rel → List AVal
  | .read t => useFacts (F t) (fit (cat t).arity (A t))
  | .values n _ => List.replicate n AVal.top
  | .filter r c => useFacts (r.facts cat F T ++ c.factsOf) (c.refine (r.aeval cat A F T sz))
  -- The input's description is bound once: inside the lambda it would be
  -- recomputed per expression, exponentially in the depth of projections (#825).
  | .project r es =>
      let env := r.aeval cat A F T sz
      let fs := r.facts cat F T ++ r.ratioPart cat A F T sz
      env ++ es.map (·.absF env fs)
  | .emit r m => m.map ((r.aeval cat A F T sz).getD · AVal.top)
  | .cross a b => a.aeval cat A F T sz ++ b.aeval cat A F T sz
  | .join a b .inner on => on.refine (a.aeval cat A F T sz ++ b.aeval cat A F T sz)
  | .join a b .left _ => a.aeval cat A F T sz ++ (b.aeval cat A F T sz).map AVal.nullable
  | .fetch r _ _ => r.aeval cat A F T sz
  | .unionAll a b => List.zipWith AVal.join (a.aeval cat A F T sz) (b.aeval cat A F T sz)
  | .window r _ _ fns =>
      let env := r.aeval cat A F T sz
      env ++ fns.map (WinFn.abs sz env)
  | .semi a _ _ _ => a.aeval cat A F T sz
  | .orderBy r _ | .distinct r => r.aeval cat A F T sz
  -- An element of the column's list in its place (#925).
  | .unnest r c =>
      let env := r.aeval cat A F T sz
      env.set c (env.getD c AVal.top).elemsOf
  | .aggregate r gs ms =>
      let env := r.aeval cat A F T sz
      let fs := r.facts cat F T
      let n := r.maxRows
      gs.map (·.absD env fs) ++ ms.map fun m => Measure.abs env fs m (!gs.isEmpty) n

/-- Facts about an aggregate's rows that need its input's description: the
`ratio` facts of its sums and counts, for the decimal `AVG`s a projection
divides (#237). -/
def Rel.ratioPart (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (sz : Bool := false) : Rel → List Fact
  | .aggregate r gs ms => ratioFacts gs.length (r.aeval cat A F T sz) (r.facts cat F T) ms
  | _ => []
end

/-! ### One pass (#903)

`Rel.aeval` asks its input for its facts at every filter and projection, and
`Rel.facts` and `Rel.arity` walk the input again each time: a plan of depth
`d` is walked `O(d)` times per node. `Rel.lane` computes the arity, facts,
description, `ratio` facts and row bound of every subplan once, bottom-up,
from its inputs' lanes. `Rel.lane_eq` proves each field is the analysis it
replaces, and the `@[csimp]` lemmas make compiled code run the lane wherever
it calls `Rel.aeval` or `Rel.ratioPart`. Proofs keep reasoning about the
definitions above. -/

/-- The analyses of one subplan, computed together. -/
structure Rel.Lane where
  arity : Nat
  facts : List Fact
  env : List AVal
  ratio : List Fact
  rows : Option Nat
  deriving Inhabited

/-- One node's lane from its inputs' lanes (`l`, `l₂`; unused ones are ignored). -/
def Rel.laneStep (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys)
    (sz : Bool) : Rel → Rel.Lane → Rel.Lane → Rel.Lane
  | .read t, _, _ => ⟨(cat t).arity, F t, useFacts (F t) (fit (cat t).arity (A t)), [], none⟩
  | .values n rows, _, _ => ⟨n, [], List.replicate n AVal.top, [], some rows.length⟩
  | .filter _ c, l, _ =>
      ⟨l.arity, l.facts ++ c.factsOf, useFacts (l.facts ++ c.factsOf) (c.refine l.env), [], l.rows⟩
  | .project _ es, l, _ =>
      ⟨l.arity + es.length,
        (l.facts.filter (·.inRange l.arity)).flatMap (Fact.rename (copyCols l.arity es)) ++
          linFacts l.arity l.arity es,
        l.env ++ es.map (·.absF l.env (l.facts ++ l.ratio)), [], l.rows⟩
  | .emit _ m, l, _ =>
      ⟨m.length, l.facts.flatMap (Fact.rename (positions m)), m.map (l.env.getD · AVal.top), [],
        l.rows⟩
  | .cross _ _, la, lb =>
      ⟨la.arity + lb.arity, la.facts.filter (·.inRange la.arity) ++ lb.facts.map (·.shift la.arity),
        la.env ++ lb.env, [], la.rows.bind fun n => lb.rows.map (n * ·)⟩
  | .join _ _ .inner on, la, lb =>
      ⟨la.arity + lb.arity,
        la.facts.filter (·.inRange la.arity) ++ lb.facts.map (·.shift la.arity) ++ on.factsOf,
        on.refine (la.env ++ lb.env), [], la.rows.bind fun n => lb.rows.map (n * ·)⟩
  | .join _ _ .left on, la, lb =>
      ⟨la.arity + lb.arity,
        la.facts.filter (·.inRange la.arity) ++
          (lb.facts.filter Fact.intsOnly).map (·.shift la.arity) ++
          on.factsOf.filter (·.rightOf la.arity),
        la.env ++ lb.env.map AVal.nullable, [], none⟩
  | .fetch _ _ cnt, l, _ =>
      ⟨l.arity, l.facts, l.env, [], match cnt, l.rows with
        | some k, some n => some (min k n)
        | some k, none => some k
        | none, n => n⟩
  | .unionAll _ _, la, lb =>
      ⟨la.arity, la.facts.filter (lb.facts.contains ·), List.zipWith AVal.join la.env lb.env, [],
        la.rows.bind fun n => lb.rows.map (n + ·)⟩
  | .window r part sort fns, l, _ =>
      ⟨l.arity + fns.length,
        l.facts.filter (·.inRange l.arity) ++ winFacts part sort (T r part sort) l.arity fns,
        l.env ++ fns.map (WinFn.abs sz l.env), [], l.rows⟩
  | .semi _ _ _ _, l, _ =>
      ⟨l.arity, l.facts, l.env, [], l.rows⟩
  | .orderBy _ _, l, _ | .distinct _, l, _ =>
      ⟨l.arity, l.facts, l.env, [], l.rows⟩
  | .aggregate _ gs ms, l, _ =>
      ⟨gs.length + ms.length, aggFacts gs.length ms,
        gs.map (·.absD l.env l.facts) ++ ms.map fun m => Measure.abs l.env l.facts m (!gs.isEmpty) l.rows,
        ratioFacts gs.length l.env l.facts ms, if gs.isEmpty then some 1 else l.rows⟩
  | .unnest _ c, l, _ =>
      ⟨l.arity, [], l.env.set c (l.env.getD c AVal.top).elemsOf, [], none⟩


/-- The analyses of every subplan in one bottom-up pass. -/
def Rel.lane (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys)
    (sz : Bool) : Rel → Rel.Lane
  | r@(.filter a _) | r@(.project a _) | r@(.emit a _) | r@(.fetch a _ _) | r@(.window a _ _ _)
  | r@(.semi a _ _ _) | r@(.orderBy a _) | r@(.distinct a) | r@(.aggregate a _ _) | r@(.unnest a _) =>
      r.laneStep cat A F T sz (a.lane cat A F T sz) default
  | r@(.cross a b) | r@(.join a b _ _) | r@(.unionAll a b) =>
      r.laneStep cat A F T sz (a.lane cat A F T sz) (b.lane cat A F T sz)
  | r@(.read _) | r@(.values _ _) => r.laneStep cat A F T sz default default

/-- **The lane is the analyses**, field by field. -/
theorem Rel.lane_eq (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (sz : Bool) (r : Rel) :
    r.lane cat A F T sz = ⟨r.arity cat, r.facts cat F T, r.aeval cat A F T sz,
      r.ratioPart cat A F T sz, r.maxRows⟩ := by
  induction r with
  | join a b ty on iha ihb =>
    cases ty <;> simp only [Rel.lane, Rel.laneStep, iha, ihb, Rel.arity, Rel.facts, Rel.aeval, Rel.ratioPart,
      Rel.maxRows]
  | fetch r _ cnt ih =>
    cases cnt <;> simp only [Rel.lane, Rel.laneStep, ih, Rel.arity, Rel.facts, Rel.aeval, Rel.ratioPart,
      Rel.maxRows]
  | _ => simp_all only [Rel.lane, Rel.laneStep, Rel.arity, Rel.facts, Rel.aeval, Rel.ratioPart, Rel.maxRows]

/-- `Rel.aeval` by the lane. -/
def Rel.aevalLane (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (sz : Bool := false) (r : Rel) : List AVal :=
  (r.lane cat A F T sz).env

/-- `Rel.ratioPart` by the lane. -/
def Rel.ratioPartLane (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (sz : Bool := false) (r : Rel) : List Fact :=
  (r.lane cat A F T sz).ratio

@[csimp] theorem Rel.aeval_csimp : @Rel.aeval = @Rel.aevalLane := by
  funext cat A F T sz r; simp only [Rel.aevalLane, Rel.lane_eq]

@[csimp] theorem Rel.ratioPart_csimp : @Rel.ratioPart = @Rel.ratioPartLane := by
  funext cat A F T sz r; simp only [Rel.ratioPartLane, Rel.lane_eq]

theorem Rel.aeval_length {cat : Catalog} {A : String → List AVal} {F : String → List Fact}
    {T : WindowKeys} {sz : Bool} :
    ∀ {r : Rel}, r.WF cat → (r.aeval cat A F T sz).length = r.arity cat
  | .read _, _ => by simp [aeval, fit, arity, useFacts_length]
  | .values _ _, _ => by simp [aeval, arity]
  | .filter r _, h => by
      simp [aeval, arity, useFacts_length, Expr.refine_length, aeval_length (r := r) h.1]
  | .project r _, h => by simp [aeval, arity, aeval_length (r := r) h.1]
  | .emit _ _, _ => by simp [aeval, arity]
  | .cross a b, h => by simp [aeval, arity, aeval_length (r := a) h.1, aeval_length (r := b) h.2]
  | .join a b .inner _, h => by
      simp [aeval, arity, Expr.refine_length, aeval_length (r := a) h.1, aeval_length (r := b) h.2.1]
  | .join a b .left _, h => by
      simp [aeval, arity, aeval_length (r := a) h.1, aeval_length (r := b) h.2.1]
  | .fetch r _ _, h => by simp [aeval, arity, aeval_length (r := r) h]
  | .unionAll a b, h => by
      simp [aeval, arity, aeval_length (r := a) h.1, aeval_length (r := b) h.2.1, h.2.2]
  | .window r _ _ _, h => by simp [aeval, arity, aeval_length (r := r) h.1]
  | .semi a _ _ _, h => by simp [aeval, arity, aeval_length (r := a) h.1]
  | .orderBy r _, h => by simp [aeval, arity, aeval_length (r := r) h.1]
  | .distinct r, h => by simp [aeval, arity, aeval_length (r := r) h]
  | .unnest r _, h => by simp [aeval, arity, aeval_length (r := r) h.1]
  | .aggregate _ _ _, _ => by simp [aeval, arity]

end Substrait
