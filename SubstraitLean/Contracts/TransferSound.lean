import SubstraitLean.Contracts.Transfer

/-!
# Contracts: TransferSound

Soundness of the transfer functions, ending in `Expr.abs_sound`: abstract
expression evaluation over-approximates `Expr.eval`.

Part of `SubstraitLean.Contracts`, which re-exports it. -/

namespace Substrait

/-! ### Intervals of the functions of one number -/

theorem monoAbs_sound {kin kout : NumKind} {g : Int → Int} (hg : ∀ {x y}, x ≤ y → g x ≤ g y)
    {f : UnFn} (hf : ∀ v, f.apply v = Value.mapP kin.is (fun _ => kout) (some ∘ g) v)
    {a : AVal} {v : Value} (h : a.Mem v) : (monoAbs kin kout g a).Mem (f.apply v) :=
  mapAbs_sound hf (fun _ _ r hi hr => by
    simp only [Function.comp, Option.some.injEq] at hr; subst hr; exact Bound.mem_mapMono hg hi)
    (fun _ _ _ hr => by simp at hr) h

theorem ftoiBound_mem {b : Bound} {i r : Int} (hi : b.Mem i) (hr : FloatCode.toInt? i = some r) :
    (ftoiBound b).Mem r := by
  obtain ⟨bl, bh⟩ := b
  unfold ftoiBound
  match bl, bh, hi with
  | some lo, some hi', hc =>
    simp only []
    split
    · rename_i x y hx hy
      exact ⟨fun _ hl => by cases hl; exact FloatCode.toInt?_mono (hc.1 lo rfl) hx hr,
        fun _ hh => by cases hh; exact FloatCode.toInt?_mono (hc.2 hi' rfl) hr hy⟩
    · exact Bound.mem_top _
  | none, _, _ | some _, none, _ => exact Bound.mem_top _

theorem ftoiFails_of {b : Bound} {i : Int} (hi : b.Mem i) (hn : FloatCode.toInt? i = none) :
    ftoiFails (some b) = true := by
  obtain ⟨bl, bh⟩ := b
  match bl, bh, hi with
  | some lo, some hi', hc =>
    simp only [ftoiFails, Bool.or_eq_true, Option.isNone_iff_eq_none]
    cases hx : FloatCode.toInt? lo with
    | none => exact .inl rfl
    | some x =>
      cases hy : FloatCode.toInt? hi' with
      | none => exact .inr rfl
      | some y =>
        obtain ⟨z, hz⟩ := FloatCode.toInt?_between (hc.1 lo rfl) (hc.2 hi' rfl) hx hy
        rw [hz] at hn; cases hn
  | none, _, _ | some _, none, _ => rfl

theorem ftoiAbs_sound {a : AVal} {v : Value} (h : a.Mem v) :
    (ftoiAbs a).Mem (UnFn.apply .ftoi v) :=
  mapAbs_sound (g := FloatCode.toInt?) (fun v => by cases v <;> hf_tac)
    (fun _ _ _ hi hr => ftoiBound_mem hi hr) (fun _ _ hi hn => ftoiFails_of hi hn) h

theorem FMath.inDomain_of_safe {f : FMath} {b : Bound} {c : Int} (hs : f.safeB (some b) = true)
    (hc : b.Mem c) : f.inDomain c = true := by
  simp only [FMath.safeB, Option.all_some, Bool.and_eq_true] at hs
  simp only [FMath.inDomain, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨?_, .inl ?_⟩
  · cases hl : f.lo? with
    | none => rfl
    | some l =>
      simp only [hl, Option.all_some] at hs
      simpa using Bound.allGe_le hs.1 hc
  · cases hh : f.hi? with
    | none => rfl
    | some h =>
      simp only [hh, Option.all_some] at hs
      simpa using Bound.le_allLe hs.2 hc

theorem BinFn.domainSafe_atan2 {x y : Bound} (hs : BinFn.domainSafe .fatan2 (some x) (some y) = true)
    {i j : Int} (hi : x.Mem i) (hj : y.Mem j) :
    (atan2? i j).isSome = true := by
  simp only [BinFn.domainSafe, Option.all_some, Bool.or_eq_true, Bool.not_eq_true'] at hs
  simp only [atan2?]
  split
  · rename_i h0
    rcases hs with hs | hs
    · exact absurd h0.1 (Bound.ne_zero hi hs)
    · exact absurd h0.2 (Bound.ne_zero hj hs)
  · rfl

theorem BinFn.domainSafe_logb {x y : Bound} (hs : BinFn.domainSafe .flogb (some x) (some y) = true)
    {i j : Int} (hi : x.Mem i) (hj : y.Mem j) :
    (logb? i j).isSome = true := by
  simp only [BinFn.domainSafe, Option.all_some, Bool.and_eq_true, Bool.or_eq_true] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  have := Bound.allGe_le h1 hi
  have := Bound.allGe_le h2 hj
  have hne : j ≠ FloatCode.one := by
    rcases h3 with h3 | h3
    · have := Bound.allGe_le h3 hj; omega
    · have := Bound.le_allLe h3 hj; omega
  have hc : 0 < i ∧ 0 < j ∧ j ≠ FloatCode.one := ⟨by omega, by omega, hne⟩
  simp only [logb?, hc, ne_eq, not_false_eq_true, and_self, ↓reduceIte, Option.isSome_some]

theorem BinFn.domainSafe_bit {op : BitOp} {ox : Option Bound} {y : Bound}
    (hs : BinFn.domainSafe (.bit op) ox (some y) = true) {i j : Int} (hj : y.Mem j) :
    (op.apply i j).isSome = true := by
  cases op <;> simp only [BinFn.domainSafe, BitOp.isShift, Option.all_some, Bool.not_true,
    Bool.false_or, Bool.and_eq_true] at hs <;> simp only [BitOp.apply, Option.isSome_some]
  all_goals
    have := Bound.allGe_le hs.1 hj
    have := Bound.le_allLe hs.2 hj
    have hc : 0 ≤ j ∧ j < 64 := ⟨by omega, by omega⟩
    simp only [hc, and_self, ↓reduceIte, Option.isSome_some]

theorem partBound_mem (p : Time.DatePart) {b : Bound} {ts r : Int} (hi : b.Mem ts)
    (hr : Time.datePart p ts = some r) : (partBound p b).Mem r := by
  simp only [Time.datePart] at hr
  split at hr
  · rename_i hr'
    simp only [Option.some.injEq] at hr; subst hr
    simp only [partBound]
    split
    · rename_i lo hi hp
      have := Time.partOf_range hp ts
      exact ⟨fun l hl => by simp at hl; omega, fun u hu => by simp at hu; omega⟩
    · rename_i hp
      have hy : p = .year := by cases p <;> simp_all [Time.DatePart.range]
      subst hy
      exact Bound.mem_mapMono Time.year_mono (Bound.mem_clamp hi hr'.1 hr'.2)
  · cases hr

theorem partFails_of (p : Time.DatePart) {b : Bound} {ts : Int} (hi : b.Mem ts)
    (hn : Time.datePart p ts = none) : (!(some b).all (·.within Time.partMin Time.partMax)) = true := by
  simp only [Time.datePart] at hn
  split at hn
  · cases hn
  · rename_i hr
    simp only [Option.all_some, Bool.not_eq_true']
    cases hw : b.within Time.partMin Time.partMax
    · rfl
    · have := Bound.within_mem hw hi
      simp only [between, Bool.and_eq_true, decide_eq_true_eq] at this
      exact absurd this hr

theorem datePartAbs_sound (p : Time.DatePart) {a : AVal} {v : Value} (h : a.Mem v) :
    (datePartAbs p a).Mem (UnFn.apply (.datePart p) v) :=
  mapAbs_sound (g := Time.datePart p) (fun v => by cases v <;> hf_tac)
    (fun _ _ _ hi hr => partBound_mem p hi hr) (fun _ _ hi hn => partFails_of p hi hn) h

theorem Text.strpos_nonneg (s t : String) : 0 ≤ Text.strpos s t := by
  unfold Text.strpos; apply Text.capped_nonneg; split <;> omega

theorem Text.strpos_le (s t : String) : Text.strpos s t ≤ Text.sizeCap := Text.capped_le _

theorem Text.capped_nat_nonneg (n : Nat) : 0 ≤ Text.capped n := Text.capped_nonneg (by omega)

theorem Text.ascii_nonneg (s : String) : 0 ≤ Text.ascii s := by
  unfold Text.ascii; split <;> omega

theorem convBound_mem (c : FloatCode.FiniteMonoConv) {b : Bound} {i : Int} (hi : b.Mem i) :
    (convBound c b).Mem (c.conv i) := by
  have : FloatCode.negInf < c.conv i ∧ c.conv i < FloatCode.posInf := c.bounds i
  refine ⟨?_, ?_⟩ <;> intro x hx <;> simp only [convBound, Option.some.injEq] at hx <;> subst hx
  · cases hl : b.lo with
    | none => simp only [Option.elim]; omega
    | some l => exact c.mono (hi.1 l hl)
  · cases hh : b.hi with
    | none => simp only [Option.elim]; omega
    | some u => exact c.mono (hi.2 u hh)

theorem convAbs_sound {ok : NumKind → Bool} (c : FloatCode.FiniteMonoConv) {f : UnFn}
    (hf : ∀ v, f.apply v = Value.mapP ok (fun _ => .float) (some ∘ c.conv) v) {a : AVal} {v : Value}
    (h : a.Mem v) : (convAbs ok c a).Mem (f.apply v) :=
  mapAbs_sound hf (fun _ _ _ hi hr => by
    simp only [Function.comp, Option.some.injEq] at hr; subst hr; exact convBound_mem c hi)
    (fun _ _ _ hr => by simp at hr) h

/-- `CAST(x AS INT)` of `n` bits: the integer, or NULL where it does not fit. -/
theorem narrowAbs_sound {n : Nat} {f : UnFn}
    (hf : ∀ v, f.apply v = Value.mapP NumKind.int.is (fun _ => .int)
      (fun i => if fitsBits n i then some i else none) v)
    {a : AVal} {v : Value} (h : a.Mem v) : (narrowAbs n a).Mem (f.apply v) :=
  mapAbs_sound hf (fun _ _ _ hi hr => by split at hr <;> simp_all)
    (fun b _ hi hn => by
      split at hn
      · cases hn
      · rename_i hfit
        simp only [Option.all_some, Bool.not_eq_true']
        cases hw : b.within (-2 ^ (n - 1)) (2 ^ (n - 1) - 1)
        · rfl
        · exact absurd (Bound.within_mem hw hi) hfit) h

/-- A function whose result is any number of its kind (or NULL). -/
theorem topAbs_sound {ok : NumKind → Bool} {kout : NumKind → NumKind} {g : Int → Int} {f : UnFn}
    (hf : ∀ v, f.apply v = Value.mapP ok kout (some ∘ g) v) {a : AVal} {v : Value} (h : a.Mem v) :
    (mapAbs ok kout (fun _ => Bound.top) (fun _ => false) a).Mem (f.apply v) :=
  mapAbs_sound hf (fun _ _ _ _ _ => Bound.mem_top _) (fun _ _ _ hr => by simp at hr) h

/-! ### Lists and structs (#925) -/

theorem AVal.nonStruct_of_mem {a : AVal} {v : Value} (h : a.Mem v) (hv : ∀ vs, v ≠ .struct vs) :
    a.nonStruct = true := by
  mem_cases h with i b hb hi
  all_goals simp_all [AVal.nonStruct, AVal.nested, AVal.Mem]

theorem AVal.memFields_getD {i : Nat} : ∀ {fs : List AVal} {vs : List Value}, AVal.MemFields fs vs →
    (fs.getD i { null := true }).Mem (vs.getD i .null)
  | [], [], _ => rfl
  | f :: fs, v :: vs, ⟨hf, hfs⟩ => by
    cases i with
    | zero => exact hf
    | succ i => simpa using AVal.memFields_getD (i := i) hfs

theorem AVal.fieldAbs_sound (i : Nat) {a : AVal} {v : Value} (h : a.Mem v) :
    (a.fieldAbs i).Mem (UnFn.apply (.structField i) v) := by
  have hf : ∀ vs, a.Mem (.struct vs) →
      (match a.fields with
        | some fs => fs.getD i { null := true }
        | none => AVal.top).Mem (vs.getD i .null) := by
    intro vs hv
    obtain ⟨_, hm⟩ := hv
    cases hfs : a.fields with
    | none => exact AVal.mem_top _
    | some fs => simp only [hfs] at hm; exact AVal.memFields_getD hm
  unfold AVal.fieldAbs
  cases v
  case struct vs =>
    simp only [UnFn.apply]
    split
    · exact AVal.mem_nullable (hf vs h)
    · exact hf vs h
  all_goals
    simp only [UnFn.apply, AVal.nonStruct_of_mem h (by simp), ↓reduceIte]
    rfl

theorem List.getD_null_mem (vs : List Value) (n : Nat) :
    vs.getD n .null = .null ∨ vs.getD n .null ∈ vs := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : n < vs.length
  · right; rw [List.getElem?_eq_getElem h]; exact List.getElem_mem h
  · left; rw [List.getElem?_eq_none (by omega)]; rfl

/-- Element `off` of `vs` is `NULL` or one of them. -/
theorem Value.listElement_mem (off : Int) (vs : List Value) :
    Value.listElement off vs = .null ∨ Value.listElement off vs ∈ vs := by
  simp only [Value.listElement]
  split <;> split <;> first | exact List.getD_null_mem vs _ | exact .inl rfl

/-- One of them where every length in `card` has element `off`. -/
theorem Value.listElement_mem_of {off : Int} {vs : List Value} {card : Bound}
    (hc : card.Mem vs.length) (h : card.hasElem off = true) : Value.listElement off vs ∈ vs := by
  have hl := Bound.allGe_le h hc
  simp only [Value.listElement]
  by_cases ho : off < 0
  · simp only [ho, ite_true] at hl ⊢
    rw [ite_eq_left (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  · simp only [ho, ite_false] at hl ⊢
    rw [ite_eq_left (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _

theorem AVal.elementAbs_sound (off : Int) {a : AVal} {v : Value} (h : a.Mem v) :
    (a.elementAbs off).Mem (UnFn.apply (.listElement off) v) := by
  unfold AVal.elementAbs
  cases v
  case list vs =>
    obtain ⟨_, hc, he⟩ := AVal.mem_list.mp h
    simp only [UnFn.apply]
    split
    · rcases Value.listElement_mem off vs with hn | hm
      · rw [hn]; rfl
      · exact AVal.mem_nullable (he _ hm)
    · rename_i hn
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hn
      exact he _ (Value.listElement_mem_of hc (by simpa using hn.2))
  all_goals
    simp only [UnFn.apply, AVal.nonList_of_mem h (by simp), Bool.true_or, ↓reduceIte]
    rfl

theorem AVal.cardAbs_sound {a : AVal} {v : Value} (h : a.Mem v) :
    a.cardAbs.Mem (UnFn.apply .cardinality v) := by
  cases v
  case list vs =>
    obtain ⟨_, hc, _⟩ := AVal.mem_list.mp h
    exact ⟨_, rfl, Bound.mem_meet hc ⟨fun l hl => by simp [Bound.ge] at hl; omega,
      fun u hu => by simp [Bound.ge] at hu⟩, rfl⟩
  all_goals exact AVal.nonList_of_mem h (by simp)

theorem AVal.flattenAbs_sound {a : AVal} {v : Value} (h : a.Mem v) :
    a.flattenAbs.Mem (UnFn.apply .flatten v) := by
  cases v
  case list vs =>
    obtain ⟨hl, _, he⟩ := AVal.mem_list.mp h
    simp only [UnFn.apply, Value.flatten, AVal.flattenAbs, AVal.Mem, AVal.MemR]
    refine ⟨hl, Bound.mem_top _, ?_⟩
    cases hf : a.elemsOf.elems with
    | none => trivial
    | some f =>
      simp only [AVal.memAll_iff, List.mem_flatMap]
      rintro w ⟨u, hu, hw⟩
      have hu' := he u hu
      cases u
      case list ws =>
        have : (a.elemsOf.elems.getD AVal.top).Mem w := (AVal.mem_list.mp hu').2.2 w hw
        rwa [hf] at this
      all_goals simp at hw
  all_goals exact AVal.nonList_of_mem h (by simp)

theorem UnFn.abs_sound (f : UnFn) {a : AVal} {v : Value} (h : a.Mem v) :
    (f.abs a).Mem (f.apply v) := by
  cases f
  case bbox n =>
    refine BlackBox.scalarAbs_mem fun hs => ?_
    cases v <;> simp_all [AVal.Mem]
  case ffloor => exact monoAbs_sound FloatCode.floor_mono (fun v => by cases v <;> hf_tac) h
  case fceil => exact monoAbs_sound FloatCode.ceil_mono (fun v => by cases v <;> hf_tac) h
  case fround => exact monoAbs_sound FloatCode.round_mono (fun v => by cases v <;> hf_tac) h
  case ftoi => exact ftoiAbs_sound h
  case narrow n | narrowOrNull n => exact narrowAbs_sound (fun v => by cases v <;> hf_tac) h
  case ftoiOrNull =>
    exact mapAbs_sound (g := fun c => (FloatCode.toInt? c).bind fun i =>
        if fitsBits 64 i then some i else none)
      (fun v => by
        cases v <;> simp only [UnFn.apply, Value.mapP, Value.numOf?] <;> try rfl
        rename_i c
        cases FloatCode.toInt? c <;> simp only [Option.bind] <;> split <;> rfl)
      (fun _ i r hi hr => by
        cases hc : FloatCode.toInt? i with
        | none => simp [hc] at hr
        | some z =>
          simp only [hc, Option.bind_some] at hr
          split at hr
          · cases hr; exact ftoiBound_mem hi hc
          · cases hr)
      (fun _ _ _ _ => rfl) h
  case neg =>
    exact mapAbs_sound (g := fun i => some (-i)) (fun v => by cases v <;> hf_tac)
      (fun _ _ _ hi hr => by cases hr; exact Bound.mem_neg hi) (fun _ _ _ hr => by cases hr) h
  case fneg =>
    exact mapAbs_sound (g := fun i => some (FloatCode.neg i)) (fun v => by cases v <;> hf_tac)
      (fun _ _ _ hi hr => by cases hr; simpa [FloatCode.neg] using Bound.mem_neg hi)
      (fun _ _ _ hr => by cases hr) h
  case wrap => simpa [UnFn.abs, UnFn.apply] using h
  case widen => simpa [UnFn.abs, UnFn.apply] using h
  case decimal p s | dkind p s =>
    exact mapAbs_sound (g := some) (fun v => by cases v <;> hf_tac)
      (fun _ _ _ hi hr => by cases hr; exact hi) (fun _ _ _ hr => by cases hr) h
  case dround k => exact topAbs_sound (g := roundDiv10 k) (fun v => by cases v <;> hf_tac) h
  case dtrunc k => exact topAbs_sound (g := fun i => i.tdiv (10 ^ k)) (fun v => by cases v <;> hf_tac) h
  case dtof s => exact convAbs_sound _ (fun v => by cases v <;> hf_tac) h
  case ftod s =>
    refine mapAbs_sound (g := fun c => FloatCode.toDecimal? c s) (fun v => by cases v <;> hf_tac)
      (fun b i r hi hr => ?_) (fun b i hi hn => ?_) h
    · obtain ⟨bl, bh⟩ := b
      unfold ftodBound
      match bl, bh, hi with
      | some l, some u, hc =>
        simp only []
        split
        · rename_i x y hx hy
          obtain ⟨q, hq, hxq, hqy⟩ := FloatCode.toDecimal?_between (hc.1 l rfl) (hc.2 u rfl) hx hy
          rw [hr] at hq; cases hq
          exact ⟨fun z hz => by cases hz; exact hxq, fun z hz => by cases hz; exact hqy⟩
        · exact Bound.mem_top _
      | none, _, _ | some _, none, _ => exact Bound.mem_top _
    · obtain ⟨bl, bh⟩ := b
      match bl, bh, hi with
      | some l, some u, hc =>
        simp only [ftodFails, Bool.or_eq_true, Option.isNone_iff_eq_none]
        cases hx : FloatCode.toDecimal? l s with
        | none => exact .inl rfl
        | some x =>
          cases hy : FloatCode.toDecimal? u s with
          | none => exact .inr rfl
          | some y =>
            obtain ⟨q, hq, _⟩ := FloatCode.toDecimal?_between (hc.1 l rfl) (hc.2 u rfl) hx hy
            rw [hq] at hn; cases hn
      | none, _, _ | some _, none, _ => rfl
  case itof => exact convAbs_sound _ (fun v => by cases v <;> hf_tac) h
  case froundTo d => exact topAbs_sound (g := FloatCode.roundTo d) (fun v => by cases v <;> hf_tac) h
  case fmath f =>
    refine mapAbs_sound (g := f.apply) (fun v => by cases v <;> hf_tac)
      (fun _ _ _ _ _ => Bound.mem_top _) (fun b i hi hn => ?_) h
    simp only [Bool.not_eq_true']
    cases hs : f.safeB (some b)
    · rfl
    · simp [FMath.apply, FMath.inDomain_of_safe hs hi] at hn
  case itos =>
    mem_cases h with i b hb hi
    · simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonNum, AVal.nonInt]
    · cases k <;> simp only [UnFn.abs, UnFn.apply, NumKind.val]
      · simp [AVal.Mem, hb]
      all_goals
        show (AVal.nonNum .int a) = true
        exact AVal.nonNum_of_memNum ⟨b, hb, hi, hk⟩ (by intro h; cases h)
    all_goals simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonNum, AVal.nonInt]
  case strftime fmt =>
    mem_cases h with i b hb hi
    · simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonNum, AVal.nonInt]
    · cases k <;> simp only [UnFn.abs, UnFn.apply, NumKind.val]
      case ts => simp [AVal.Mem, hb]
      all_goals
        show (AVal.nonNum .ts a) = true
        exact AVal.nonNum_of_memNum ⟨b, hb, hi, hk⟩ (by intro h; cases h)
    all_goals simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonNum, AVal.nonInt]
  case datePart p => exact datePartAbs_sound p h
  case dayPart p =>
    exact mapAbs_sound (g := Time.datePartDay p) (fun v => by cases v <;> hf_tac)
      (fun _ _ _ hi hr => partBound_mem p
        (Bound.mem_mapMono (fun hxy => Int.mul_le_mul_of_nonneg_right hxy (by decide)) hi) hr)
      (fun _ _ hi hn => partFails_of p
        (Bound.mem_mapMono (fun hxy => Int.mul_le_mul_of_nonneg_right hxy (by decide)) hi) hn) h
  case dateTrunc u =>
    exact mapAbs_sound (g := fun t => some (Time.trunc u t)) (fun v => by cases v <;> hf_tac)
      (fun _ _ _ hi hr => by cases hr; exact Bound.mem_mapMono (Time.trunc_mono u) hi)
      (fun _ _ _ hr => by cases hr) h
  case toDate => exact monoAbs_sound Time.days_mono (fun v => by cases v <;> hf_tac) h
  case dayTrunc u => exact monoAbs_sound (Time.truncDay_mono u) (fun v => by cases v <;> hf_tac) h
  case addMonths m t =>
    cases t
    · exact monoAbs_sound (Time.addMonths_mono m) (fun v => by cases v <;> hf_tac) h
    · exact topAbs_sound (g := Time.addMonthsUs m) (fun v => by cases v <;> hf_tac) h
  case asTime => exact monoAbs_sound (fun h => h) (fun v => by cases v <;> hf_tac) h
  case dateTime =>
    exact monoAbs_sound (fun hxy => Int.mul_le_mul_of_nonneg_right hxy (by decide))
      (fun v => by cases v <;> hf_tac) h
  case epochUs => exact monoAbs_sound (fun h => h) (fun v => by cases v <;> hf_tac) h
  case bucket k o => exact monoAbs_sound (Time.bucket_mono k o) (fun v => by cases v <;> hf_tac) h
  case timeOfDay =>
    exact mapAbs_sound (g := fun t => some (Time.timeOfDay t)) (fun v => by cases v <;> hf_tac)
      (fun _ i _ _ hr => by
        cases hr
        have := Time.timeOfDay_range i
        exact ⟨fun l hl => by simp at hl; omega, fun u hu => by simp at hu; omega⟩)
      (fun _ _ _ hr => by cases hr) h
  case upper | lower | length | reverse | ascii | replace | regexExtract | regexReplace | md5 | sha256 =>
    mem_cases h with i b hb hi <;> (try cases k) <;>
      simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonStr, Bound.Mem, Text.ascii_nonneg,
        Text.capped_le, Text.capped_nonneg, NumKind.val, AVal.MemNum]
  case structField i => exact AVal.fieldAbs_sound i h
  case listElement off => exact AVal.elementAbs_sound off h
  case flatten => exact AVal.flattenAbs_sound h
  case fit => exact AVal.mem_top _
  case raise => cases v <;> rfl
  case isNum k => simp only [UnFn.apply]; cases v.isNum k <;> rfl
  case cardinality => exact AVal.cardAbs_sound h
  case regexMatch p =>
    mem_cases h with i b hb hi <;> (try cases k) <;>
      simp only [UnFn.abs, UnFn.apply, AVal.Mem, AVal.MemR, NumKind.val]
    all_goals (try cases Text.regexMatch s p) <;>
      simp_all [Bound.ge, Bound.Mem, AVal.Mem, AVal.MemNum] <;> omega
  all_goals
    mem_cases h with i b hb hi <;> (try cases k) <;>
      simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonBool, NumKind.val]

theorem arith_sound {tbl : NumKind → NumKind → Option NumKind} {op : Bound → Bound → Bound}
    {f : Int → Int → Int}
    (hop : ∀ {x y : Bound} {i j : Int}, x.Mem i → y.Mem j → (op x y).Mem (f i j))
    {g : BinFn} (hg : ∀ v w, g.apply v w = Value.mapP₂ tbl (fun i j => some (f i j)) v w)
    {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (arith tbl op a b).Mem (g.apply v w) :=
  mapAbs₂_sound hg (fun _ _ _ _ _ hi hj hr => by cases hr; exact hop hi hj)
    (fun _ _ _ _ _ _ hr => by cases hr) ha hb

theorem canGe_of_le {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) (h : j ≤ i) :
    canGe x y = true := by
  obtain ⟨xl, xh⟩ := x
  obtain ⟨yl, yh⟩ := y
  simp only [Bound.Mem] at hx hy
  unfold canGe
  cases xh <;> cases yl <;> simp_all <;> omega

theorem intEq_of {a b : AVal} {x y : Bound} {i : Int} (ha : a.int = some x) (hb : b.int = some y)
    (hx : x.Mem i) (hy : y.Mem i) : intEq a b = true := by
  simp [intEq, ha, hb, canEq, canGe_of_le hx hy (Int.le_refl i), canGe_of_le hy hx (Int.le_refl i)]

theorem intNe_of {a b : AVal} {x y : Bound} {i j : Int} (ha : a.int = some x)
    (hb : b.int = some y) (hx : x.Mem i) (hy : y.Mem j) (h : i ≠ j) : intNe a b = true := by
  simp only [intNe, ha, hb, canNe]
  split
  · rename_i k k' hk hk'
    rw [← Bound.point_mem hk hx, ← Bound.point_mem hk' hy]
    simpa using h
  · rfl

theorem divBound_sound {x y : Bound} {i j : Int} (hi : x.Mem i) (hj : y.Mem j) (_ : j ≠ 0) :
    (divBound x y).Mem (i.tdiv j) := by
  unfold divBound
  split
  · rename_i k hk
    split
    · rename_i hk0
      rw [Bound.point_mem hk hj]
      exact Bound.mem_mapMono (fun h => Int.tdiv_le_tdiv hk0 h) hi
    · split
      · rename_i _ hkn
        rw [Bound.point_mem hk hj]
        have hneg : i.tdiv k = -(i.tdiv (-k)) := by rw [Int.tdiv_neg, Int.neg_neg]
        rw [hneg]
        exact Bound.mem_neg (Bound.mem_mapMono (fun h => Int.tdiv_le_tdiv (by omega) h) hi)
      · exact Bound.mem_absHull hi (Int.natAbs_tdiv_le_natAbs i j)
  · split
    · rename_i hpos
      obtain ⟨yl, yh⟩ := y
      cases yl with
      | none => simp at hpos
      | some l =>
        simp only [Option.any_some, decide_eq_true_eq] at hpos
        have hj1 := hj.1 l rfl
        obtain ⟨h₁, h₂⟩ := tdiv_between (a := i) (b := j) (by omega)
        obtain ⟨xl, xh⟩ := x
        refine ⟨fun l' hl' => ?_, fun u' hu' => ?_⟩
        · simp only [Bound.signHull, Option.map_eq_some_iff] at hl'
          obtain ⟨l₀, h₀, rfl⟩ := hl'; have := hi.1 l₀ h₀; omega
        · simp only [Bound.signHull, Option.map_eq_some_iff] at hu'
          obtain ⟨u₀, h₀, rfl⟩ := hu'; have := hi.2 u₀ h₀; omega
    · exact Bound.mem_absHull hi (Int.natAbs_tdiv_le_natAbs i j)

theorem ddivBound_sound {x y : Bound} {i j : Int} (hi : x.Mem i) (hj : y.Mem j) (hj0 : j ≠ 0) :
    (ddivBound x y).Mem (roundDiv i j) := by
  unfold ddivBound
  split
  · rename_i hpos
    obtain ⟨yl, yh⟩ := y
    cases yl with
    | none => simp at hpos
    | some l =>
      simp only [Option.any_some, decide_eq_true_eq] at hpos
      have hj1 := hj.1 l rfl
      obtain ⟨h₁, h₂⟩ := roundDiv_between (a := i) (b := j) (by omega)
      obtain ⟨xl, xh⟩ := x
      refine ⟨fun l' hl' => ?_, fun u' hu' => ?_⟩
      · simp only [Bound.signHull, Option.map_eq_some_iff] at hl'
        obtain ⟨l₀, h₀, rfl⟩ := hl'; have := hi.1 l₀ h₀; omega
      · simp only [Bound.signHull, Option.map_eq_some_iff] at hu'
        obtain ⟨u₀, h₀, rfl⟩ := hu'; have := hi.2 u₀ h₀; omega
  · exact Bound.mem_absHull hi (roundDiv_natAbs_le hj0)

theorem modBound_sound {x y : Bound} {i j : Int} (hi : x.Mem i) (hj : y.Mem j) (hj0 : j ≠ 0) :
    (modBound x y).Mem (i.tmod j) := by
  have hlt : (i.tmod j).natAbs < j.natAbs := by rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (by omega)
  have hnn : x.lo.any (0 ≤ ·) = true → 0 ≤ i.tmod j := by
    intro h
    obtain ⟨xl, xh⟩ := x
    cases xl with
    | none => simp at h
    | some l => simp at h; exact Int.tmod_nonneg _ (by have := hi.1 l rfl; omega)
  obtain ⟨yl, yh⟩ := y
  have hj' := hj
  simp only [Bound.Mem] at hj'
  unfold modBound
  cases yl <;> cases yh <;> simp only []
  case some.some l u =>
    have h₁ := hj'.1 l rfl; have h₂ := hj'.2 u rfl
    constructor
    · intro b hb
      simp only [Option.some.injEq] at hb; subst hb
      split
      · exact hnn ‹_›
      · omega
    · intro b hb
      simp only [Option.some.injEq] at hb; subst hb
      omega
  all_goals
    split
    · exact ⟨fun l hl => by simp at hl; subst hl; exact hnn ‹_›, fun _ h => by simp at h⟩
    · exact Bound.mem_top _

theorem divAbs_sound {tbl : NumKind → NumKind → Option NumKind} {bound : Bound → Bound → Bound}
    {op : Int → Int → Int} {g : BinFn}
    (hbound : ∀ {x y : Bound} {i j : Int}, x.Mem i → y.Mem j → j ≠ 0 → (bound x y).Mem (op i j))
    (hg : ∀ v w, g.apply v w =
      Value.mapP₂ tbl (fun i j => if j = 0 then none else some (op i j)) v w)
    {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (divAbs tbl bound a b).Mem (g.apply v w) :=
  mapAbs₂_sound hg
    (fun _ _ _ j _ hi hj hr => by
      by_cases hj0 : j = 0
      · simp [hj0] at hr
      · simp only [hj0, ↓reduceIte, Option.some.injEq] at hr; subst hr; exact hbound hi hj hj0)
    (fun _ y _ j _ hj hr => by
      by_cases hj0 : j = 0
      · subst hj0
        simp only [mayZero, Option.all_some]
        cases h0 : y.has0
        · exact absurd rfl (Bound.ne_zero hj h0)
        · rfl
      · simp [hj0] at hr) ha hb

theorem powAbs_sound {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (powAbs a b).Mem (BinFn.apply .ipow v w) := by
  refine mapAbs₂_sound (g := fun i j =>
      if j < 0 ∨ (64 < j ∧ 1 < i.natAbs) then none else some (i ^ j.toNat))
    (fun v w => by cases v <;> cases w <;> hf_tac) (fun _ y i j r _ hj hr => ?_)
    (fun _ y i j _ hj hr => ?_) ha hb
  · split at hr
    · cases hr
    · simp only [Option.some.injEq] at hr; subst hr
      unfold powBound
      split
      · rename_i hsq
        rw [Bound.point_mem (by simpa using hsq) hj]
        constructor
        · intro l hl; cases hl
          show 0 ≤ i ^ (2 : Int).toNat
          rw [show (2 : Int).toNat = 2 from rfl, Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
          rcases Int.le_total 0 i with h | h
          · exact Int.mul_nonneg h h
          · exact Int.mul_nonneg_of_nonpos_of_nonpos h h
        · intro _ h; cases h
      · exact Bound.mem_top _
  · split at hr
    · rename_i hout
      obtain ⟨yl, yh⟩ := y
      cases yl <;> cases yh <;> simp only [powFails, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not] <;>
        first | rfl | (simp only [Bound.Mem] at hj; have := hj.1 _ rfl; have := hj.2 _ rfl; omega)
    · cases hr

/-- A comparison of two lists may be TRUE, FALSE or NULL; so may a value
whose abstraction allows all three. -/
theorem Value.ofLt3_ne_int (o : Option Bool) (i : Int) : Value.ofLt3 o ≠ .int i := by
  cases o <;> simp [Value.ofLt3]

theorem Value.ofLt3_ne_str (o : Option Bool) (s : String) : Value.ofLt3 o ≠ .str s := by
  cases o <;> simp [Value.ofLt3]

theorem Value.ofLt3_ne_list (o : Option Bool) (vs : List Value) : Value.ofLt3 o ≠ .list vs := by
  cases o <;> simp [Value.ofLt3]

theorem AVal.mem_ofLt3 {a : AVal} {o : Option Bool} (hn : a.null = true)
    (ht : a.tt = true) (hf : a.ff = true) : a.Mem (Value.ofLt3 o) := by
  cases o with
  | none => exact hn
  | some r => cases r <;> assumption

theorem joinInt_mem_left {x y : Option Bound} {i : Int} (h : ∃ b, x = some b ∧ b.Mem i) :
    ∃ b, joinInt x y = some b ∧ b.Mem i := by
  obtain ⟨b, rfl, hm⟩ := h
  cases y <;> simp [joinInt, hm, Bound.mem_join_left hm]

theorem joinInt_mem_right {x y : Option Bound} {i : Int} (h : ∃ b, y = some b ∧ b.Mem i) :
    ∃ b, joinInt x y = some b ∧ b.Mem i := by
  obtain ⟨b, rfl, hm⟩ := h
  cases x <;> simp [joinInt, hm, Bound.mem_join_right hm]

theorem joinNk_all_left {a b : AVal} {k : NumKind} {x : Bound} (hx : a.int = some x)
    (ha : a.nk.all (· == k) = true) : (joinNk a b).all (· == k) = true := by
  unfold joinNk
  simp only [hx, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  split
  · exact ha
  · split
    · exact ha
    · rfl

theorem joinNk_all_right {a b : AVal} {k : NumKind} {y : Bound} (hy : b.int = some y)
    (hb : b.nk.all (· == k) = true) : (joinNk a b).all (· == k) = true := by
  unfold joinNk
  split
  · exact hb
  · simp only [hy, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i he; rw [he]; exact hb
    · rfl

/-- Two numbers of different kinds: their abstractions have no common kind. -/
theorem sameNk_false {a b : AVal} {k k' : NumKind} (ha : a.nk.all (· == k) = true)
    (hb : b.nk.all (· == k') = true) (hk : k ≠ k') : sameNk a b = false := by
  unfold sameNk
  cases hA : a.nk <;> cases hB : b.nk <;> simp only [hA, hB, Option.all_some, beq_iff_eq] at ha hb
  all_goals first | rfl | (subst ha hb; simpa using hk)

theorem Value.pick_null_left (better : Value → Value → Bool) (w : Value) :
    Value.pick better .null w = w := by
  cases w <;> rfl

theorem Value.pick_eq_left {better : Value → Value → Bool} {v w : Value} (hv : v ≠ .null)
    (hw : w = .null ∨ better v w = false) : Value.pick better v w = v := by
  rcases hw with rfl | hw
  · cases v <;> simp_all [Value.pick]
  · cases v <;> cases w <;> simp_all [Value.pick]

theorem Value.pick_vals (better : Value → Value → Bool) (k k' : NumKind) (i j : Int) :
    Value.pick better (k.val i) (k'.val j) =
      if better (k.val i) (k'.val j) then k'.val j else k.val i := by
  cases k <;> cases k' <;> rfl

theorem pickAbs_int_pair {both : Bound → Bound → Bound} {a b : AVal} {x y : Bound}
    (hx : a.int = some x) (hy : b.int = some y) {r : Int}
    (hr : (if sameNk a b then both x y else x.join y).Mem r) :
    ∃ c, (pickAbs both a b).int = some c ∧ c.Mem r := by
  simp only [pickAbs, hx, hy]; exact joinInt_mem_right (joinInt_mem_right ⟨_, rfl, hr⟩)

theorem pickAbs_int_left {both : Bound → Bound → Bound} {a b : AVal} {x : Bound}
    (hx : a.int = some x) (hn : b.nonInt = true) {r : Int} (hr : x.Mem r) :
    ∃ c, (pickAbs both a b).int = some c ∧ c.Mem r := by
  simp only [pickAbs, hn, hx, ↓reduceIte]; exact joinInt_mem_left ⟨x, rfl, hr⟩

theorem pickAbs_int_right {both : Bound → Bound → Bound} {a b : AVal} {y : Bound}
    (hy : b.int = some y) (hn : a.null = true) {r : Int} (hr : y.Mem r) :
    ∃ c, (pickAbs both a b).int = some c ∧ c.Mem r := by
  simp only [pickAbs, hn, hy, ↓reduceIte]; exact joinInt_mem_right (joinInt_mem_left ⟨y, rfl, hr⟩)

theorem Value.ltB_vals (k : NumKind) (i j : Int) : Value.ltB (k.val i) (k.val j) = decide (i < j) := by
  cases k <;> simp [Value.ltB, NumKind.val, Value.numPair]

theorem Value.ltB_diff (k k' : NumKind) (i j : Int) (hk : k ≠ k') :
    Value.ltB (k.val i) (k'.val j) = false := by
  cases k <;> cases k' <;> simp_all [Value.ltB, NumKind.val, Value.numPair]

theorem Value.ltB_mix (k : NumKind) {i : Int} {w : Value} (hw : w.numOf? = none) :
    Value.ltB (k.val i) w = false := by
  cases k <;> cases w <;> simp_all [Value.ltB, NumKind.val, Value.numPair, Value.numOf?]

theorem Value.ltB_mix' (k : NumKind) {j : Int} {v : Value} (hv : v.numOf? = none) :
    Value.ltB v (k.val j) = false := by
  cases k <;> cases v <;> simp_all [Value.ltB, NumKind.val, Value.numPair, Value.numOf?]

/-- A value that is not a number, kept by `GREATEST`/`LEAST`. -/
theorem pickAbs_other_left {both : Bound → Bound → Bound} {a b : AVal} {v : Value} (h : a.Mem v)
    (hv : v.numOf? = none) (hn : v ≠ .null) : (pickAbs both a b).Mem v := by
  have := AVal.mem_join_left (b := b) h
  cases v <;> (try rename_i bb; cases bb) <;> simp_all [AVal.Mem, pickAbs, Value.numOf?]

theorem pickAbs_other_right {both : Bound → Bound → Bound} {a b : AVal} {w : Value} (h : b.Mem w)
    (hw : w.numOf? = none) (hn : w ≠ .null) : (pickAbs both a b).Mem w := by
  have := AVal.mem_join_right (a := a) h
  cases w <;> (try rename_i bb; cases bb) <;> simp_all [AVal.Mem, pickAbs, Value.numOf?]

/-- A value that is not a number makes `nonInt`. -/
theorem AVal.nonInt_of_other {a : AVal} {w : Value} (h : a.Mem w) (hw : w.numOf? = none) :
    a.nonInt = true := by
  cases w <;> (try rename_i bb; cases bb) <;>
    simp_all [AVal.Mem, AVal.nonInt, AVal.nested, Value.numOf?]

theorem pickAbs_sound {both : Bound → Bound → Bound} {better : Value → Value → Bool}
    (hboth : ∀ {x y : Bound} {i j : Int} (k : NumKind), x.Mem i → y.Mem j →
      (both x y).Mem (if better (k.val i) (k.val j) then j else i))
    (hdiff : ∀ (k k' : NumKind) (i j : Int), k ≠ k' → better (k.val i) (k'.val j) = false)
    (hmix : ∀ (k : NumKind) i w, w.numOf? = none → better (k.val i) w = false)
    (hmix' : ∀ v (k : NumKind) j, v.numOf? = none → better v (k.val j) = false)
    {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (pickAbs both a b).Mem (Value.pick better v w) := by
  cases hv : v.numOf? with
  | some p =>
    obtain ⟨k, i⟩ := p
    rw [Value.numOf?_some hv] at ha ⊢
    obtain ⟨x, hx, hi, hk⟩ := AVal.mem_val.mp ha
    cases hw : w.numOf? with
    | some q =>
      obtain ⟨k', j⟩ := q
      rw [Value.numOf?_some hw] at hb ⊢
      obtain ⟨y, hy, hj, hk'⟩ := AVal.mem_val.mp hb
      rw [Value.pick_vals]
      by_cases hkk : k = k'
      · subst hkk
        have hpair : (if sameNk a b then both x y else x.join y).Mem
            (if better (k.val i) (k.val j) then j else i) := by
          split
          · exact hboth k hi hj
          · split
            · exact Bound.mem_join_right hj
            · exact Bound.mem_join_left hi
        obtain ⟨c, hc, hcm⟩ := pickAbs_int_pair (both := both) hx hy hpair
        have hv' : (if better (k.val i) (k.val j) then k.val j else k.val i) =
            k.val (if better (k.val i) (k.val j) then j else i) := by split <;> rfl
        rw [hv', AVal.mem_val]
        exact ⟨c, hc, hcm, joinNk_all_left hx hk⟩
      · rw [hdiff k k' i j hkk]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hs := sameNk_false hk hk' hkk
        obtain ⟨c, hc, hcm⟩ := pickAbs_int_pair (both := both) (r := i) hx hy
          (by simp only [hs, Bool.false_eq_true, ↓reduceIte]; exact Bound.mem_join_left hi)
        rw [AVal.mem_val]
        exact ⟨c, hc, hcm, joinNk_all_left hx hk⟩
    | none =>
      have hpick : Value.pick better (k.val i) w = k.val i := by
        by_cases hn : w = .null
        · exact Value.pick_eq_left (NumKind.val_ne_null k i) (.inl hn)
        · exact Value.pick_eq_left (NumKind.val_ne_null k i) (.inr (hmix k i w hw))
      rw [hpick, AVal.mem_val]
      obtain ⟨c, hc, hcm⟩ := pickAbs_int_left (both := both) hx (AVal.nonInt_of_other hb hw) hi
      exact ⟨c, hc, hcm, joinNk_all_left hx hk⟩
  | none =>
    by_cases hn : v = .null
    · subst hn
      rw [Value.pick_null_left]
      cases hw : w.numOf? with
      | some q =>
        obtain ⟨k', j⟩ := q
        rw [Value.numOf?_some hw] at hb ⊢
        obtain ⟨y, hy, hj, hk'⟩ := AVal.mem_val.mp hb
        rw [AVal.mem_val]
        obtain ⟨c, hc, hcm⟩ := pickAbs_int_right (both := both) hy ha hj
        exact ⟨c, hc, hcm, joinNk_all_right hy hk'⟩
      | none =>
        by_cases hwn : w = .null
        · subst hwn; show (pickAbs both a b).null = true; simp_all [pickAbs, AVal.Mem]
        · exact pickAbs_other_right hb hw hwn
    · cases hw : w.numOf? with
      | some q =>
        obtain ⟨k', j⟩ := q
        rw [Value.numOf?_some hw,
          Value.pick_eq_left hn (.inr (hmix' v k' j hv))]
        exact pickAbs_other_left ha hv hn
      | none =>
        by_cases hwn : w = .null
        · rw [Value.pick_eq_left hn (.inl hwn)]; exact pickAbs_other_left ha hv hn
        · rcases Value.pick_mem (better := better) v w with he | he <;> rw [he]
          · exact pickAbs_other_left ha hv hn
          · exact pickAbs_other_right hb hw hwn

theorem le_of_natAbs_le {z : Int} {n : Nat} (h : z.natAbs ≤ n) : -(n : Int) ≤ z ∧ z ≤ n := by
  omega

theorem natAbs_le_endsMag {l h s : Int} (h1 : l ≤ s) (h2 : s ≤ h) : s.natAbs ≤ endsMag l h := by
  unfold endsMag; omega

theorem finEnds_mem {x : Bound} {i la ha : Int} (hx : x.Mem i) (h : finEnds x = some (la, ha)) :
    FloatCode.IsFin i ∧ la ≤ FloatCode.scaled i ∧ FloatCode.scaled i ≤ ha ∧
      (FloatCode.scaled i).natAbs ≤ endsMag la ha := by
  unfold finEnds at h
  cases hxl : x.lo with
  | none => simp [hxl] at h
  | some l =>
    cases hxh : x.hi with
    | none => simp [hxl, hxh] at h
    | some hh =>
      simp only [hxl, hxh] at h
      by_cases hc : FloatCode.negInf < l ∧ hh < FloatCode.posInf
      · simp only [hc, and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h1 := hx.1 l hxl
        have h2 := hx.2 hh hxh
        have m1 := FloatCode.scaled_mono h1
        have m2 := FloatCode.scaled_mono h2
        exact ⟨⟨by omega, by omega⟩, m1, m2, natAbs_le_endsMag m1 m2⟩
      · simp [hc] at h

theorem codeBound_mem {l h s : Int} {c : Int} (hs : FloatCode.scaled c = s) (hl : l ≤ s) (hh : s ≤ h) :
    (codeBound l h).Mem c := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · cases hx; exact FloatCode.codeLo_le (by omega)
  · cases hx; exact FloatCode.le_codeHi (by omega)

theorem add_ends {la ha lb hb si sj sr : Int} {k e : Nat} (li : la ≤ si) (hi : si ≤ ha)
    (lj : lb ≤ sj) (hj : sj ≤ hb) (he : -(k : Int) ≤ sr - (si + sj) ∧ sr - (si + sj) ≤ k)
    (hke : k ≤ e) : la + lb - e ≤ sr ∧ sr ≤ ha + hb + e := by omega

theorem sub_ends {la ha lb hb si sj sr : Int} {k e : Nat} (li : la ≤ si) (hi : si ≤ ha)
    (lj : lb ≤ sj) (hj : sj ≤ hb) (he : -(k : Int) ≤ sr - (si - sj) ∧ sr - (si - sj) ≤ k)
    (hke : k ≤ e) : la - hb - e ≤ sr ∧ sr ≤ ha - lb + e := by omega

theorem faddBound_mem' (sub : Bool) {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j)
    {r : Int} (hr : sub = false → r = FloatCode.fadd i j)
    (hr' : sub = true → r = FloatCode.fsub i j) :
    (faddBound sub x y).Mem r := by
  unfold faddBound
  split
  · rename_i la ha lb hb hfa hfb
    obtain ⟨fi, li, hi, mi⟩ := finEnds_mem hx hfa
    obtain ⟨fj, lj, hj, mj⟩ := finEnds_mem hy hfb
    dsimp only
    split
    · rename_i hS
      have hle : (FloatCode.scaled i).natAbs + (FloatCode.scaled j).natAbs ≤
          endsMag la ha + endsMag lb hb := Nat.add_le_add mi mj
      have hke := Nat.add_le_add_right (Nat.div_le_div_right (c := 2 ^ 50) hle) 1
      cases sub
      · obtain ⟨-, he⟩ := FloatCode.add_scaled fi fj (Nat.le_trans hle hS)
        obtain ⟨b1, b2⟩ := add_ends li hi lj hj (le_of_natAbs_le he) hke
        rw [hr rfl]
        exact codeBound_mem rfl b1 b2
      · obtain ⟨-, he⟩ := FloatCode.sub_scaled fi fj (Nat.le_trans hle hS)
        obtain ⟨b1, b2⟩ := sub_ends li hi lj hj (le_of_natAbs_le he) hke
        rw [hr' rfl]
        exact codeBound_mem rfl b1 b2
    · exact Bound.mem_top _
  · exact Bound.mem_top _

theorem mul_ends {l h p q : Int} {k E : Nat} {K : Int} (hK : 0 < K) (hl : l ≤ p) (hh : p ≤ h)
    {sr : Int} (hq : K * sr = q) (he : -(k : Int) ≤ q - p ∧ q - p ≤ k) (hkE : k ≤ E) :
    (l - E) / K ≤ sr ∧ sr ≤ (h + E) / K := by
  have a1 : l - E ≤ sr * K := by rw [Int.mul_comm, hq]; omega
  have a2 : sr * K ≤ h + E := by rw [Int.mul_comm, hq]; omega
  exact ⟨Int.ediv_le_of_le_mul hK a1, Int.le_ediv_of_mul_le hK a2⟩

theorem fmulBound_mem {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) :
    (fmulBound x y).Mem (FloatCode.fmul i j) := by
  unfold fmulBound
  split
  · rename_i la ha lb hb hfa hfb
    obtain ⟨fi, li, hi, mi⟩ := finEnds_mem hx hfa
    obtain ⟨fj, lj, hj, mj⟩ := finEnds_mem hy hfb
    dsimp only
    split
    · rename_i hP
      have hle : (FloatCode.scaled i).natAbs * (FloatCode.scaled j).natAbs ≤
          endsMag la ha * endsMag lb hb := Nat.mul_le_mul mi mj
      have hkE := Nat.add_le_add_right (Nat.div_le_div_right (c := 2 ^ 50) hle) (2 ^ 1074)
      obtain ⟨-, he⟩ := FloatCode.mul_scaled fi fj (Nat.le_trans hle hP)
      have hm : (Bound.mul ⟨some la, some ha⟩ ⟨some lb, some hb⟩).Mem
          (FloatCode.scaled i * FloatCode.scaled j) :=
        Bound.mem_mul ⟨fun _ h => by cases h; exact li, fun _ h => by cases h; exact hi⟩
          ⟨fun _ h => by cases h; exact lj, fun _ h => by cases h; exact hj⟩
      split
      · rename_i l h hb'
        rw [hb'] at hm
        have hK : (0 : Int) < ((2 ^ 1074 : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos 1074
        have hc : ((2 ^ 1074 : Nat) : Int) = 2 ^ 1074 := Int.natCast_pow 2 1074
        obtain ⟨b1, b2⟩ := mul_ends hK (hm.1 l rfl) (hm.2 h rfl) (by rw [hc]) (le_of_natAbs_le he) hkE
        exact codeBound_mem rfl b1 b2
      · exact Bound.mem_top _
    · exact Bound.mem_top _
  · exact Bound.mem_top _

theorem endsMin_le {lb hb s : Int} (hl : lb ≤ s) (hh : s ≤ hb) : endsMin lb hb ≤ s.natAbs := by
  unfold endsMin; split
  · omega
  · split <;> omega

set_option exponentiation.threshold 3200 in
theorem fdivBound_mem {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) :
    (fdivBound x y).Mem (FloatCode.fdiv i j) := by
  unfold fdivBound
  split
  · rename_i la ha lb hb hfa hfb
    obtain ⟨fi, li, hi, mi⟩ := finEnds_mem hx hfa
    obtain ⟨fj, lj, hj, mj⟩ := finEnds_mem hy hfb
    dsimp only
    split
    · rename_i hc
      obtain ⟨hmb, hM⟩ := hc
      have hmin := endsMin_le lj hj
      have hj0 : FloatCode.scaled j ≠ 0 := by
        intro h0; rw [h0] at hmin; simp at hmin; omega
      have hguard : (FloatCode.scaled i).natAbs * 2 ^ 1074 ≤ 2 ^ 2097 * (FloatCode.scaled j).natAbs :=
        Nat.le_trans (Nat.mul_le_mul_right _ mi) (Nat.le_trans hM (Nat.mul_le_mul_left _ hmin))
      obtain ⟨-, he⟩ := FloatCode.div_scaled fi fj hj0 hguard
      have h1 : (FloatCode.scaled i).natAbs * (2 ^ 1074 + 2 ^ 1024) / (FloatCode.scaled j).natAbs ≤
          endsMag la ha * (2 ^ 1074 + 2 ^ 1024) / endsMin lb hb :=
        Nat.le_trans (Nat.div_le_div_right (Nat.mul_le_mul_right _ mi))
          (Nat.div_le_div_left hmin hmb)
      obtain ⟨b1, b2⟩ := le_of_natAbs_le (Nat.le_trans he (Nat.add_le_add_right h1 1))
      exact codeBound_mem rfl b1 b2
    · exact Bound.mem_top _
  · exact Bound.mem_top _

set_option exponentiation.threshold 3200 in
theorem faddOk_guard {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j)
    (hok : faddOk x y = true) : FloatCode.IsFin i ∧ FloatCode.IsFin j ∧
      (FloatCode.scaled i).natAbs + (FloatCode.scaled j).natAbs ≤ 2 ^ 2097 := by
  unfold faddOk at hok
  split at hok
  · rename_i la ha lb hb hfa hfb
    obtain ⟨fi, -, -, mi⟩ := finEnds_mem hx hfa
    obtain ⟨fj, -, -, mj⟩ := finEnds_mem hy hfb
    exact ⟨fi, fj, Nat.le_trans (Nat.add_le_add mi mj) (of_decide_eq_true hok)⟩
  · simp at hok

set_option exponentiation.threshold 3200 in
theorem fmulOk_guard {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j)
    (hok : fmulOk x y = true) : FloatCode.IsFin i ∧ FloatCode.IsFin j ∧
      (FloatCode.scaled i).natAbs * (FloatCode.scaled j).natAbs ≤ 2 ^ 3171 := by
  unfold fmulOk at hok
  split at hok
  · rename_i la ha lb hb hfa hfb
    obtain ⟨fi, -, -, mi⟩ := finEnds_mem hx hfa
    obtain ⟨fj, -, -, mj⟩ := finEnds_mem hy hfb
    exact ⟨fi, fj, Nat.le_trans (Nat.mul_le_mul mi mj) (of_decide_eq_true hok)⟩
  · simp at hok

set_option exponentiation.threshold 3200 in
theorem fdivOk_guard {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j)
    (hok : fdivOk x y = true) : FloatCode.IsFin i ∧ FloatCode.IsFin j ∧ FloatCode.scaled j ≠ 0 ∧
      (FloatCode.scaled i).natAbs * 2 ^ 1074 ≤ 2 ^ 2097 * (FloatCode.scaled j).natAbs := by
  unfold fdivOk at hok
  split at hok
  · rename_i la ha lb hb hfa hfb
    obtain ⟨fi, -, -, mi⟩ := finEnds_mem hx hfa
    obtain ⟨fj, lj, hj, -⟩ := finEnds_mem hy hfb
    obtain ⟨hmb, hM⟩ := of_decide_eq_true hok
    have hmin := endsMin_le lj hj
    have hj0 : FloatCode.scaled j ≠ 0 := by
      intro h0; rw [h0] at hmin; simp at hmin; omega
    exact ⟨fi, fj, hj0,
      Nat.le_trans (Nat.mul_le_mul_right _ mi) (Nat.le_trans hM (Nat.mul_le_mul_left _ hmin))⟩
  · simp at hok

theorem faddBoundS_mem (sub : Bool) {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j)
    {r : Int} (hr : sub = false → r = FloatCode.fadd i j)
    (hr' : sub = true → r = FloatCode.fsub i j) :
    (faddBoundS sub x y).Mem r := by
  have hm := faddBound_mem' sub hx hy hr hr'
  unfold faddBoundS
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨hs, hxn⟩, hyn⟩, hok⟩ := hc
    obtain ⟨fi, fj, hg⟩ := faddOk_guard hx hy hok
    have h0 : 0 ≤ r := by
      rw [hr hs]
      exact FloatCode.add_nonneg fi fj hg (Bound.nonneg_mem hx hxn) (Bound.nonneg_mem hy hyn)
    exact Bound.mem_atLeast0 hm h0
  · exact hm

theorem fmulBoundS_mem {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) :
    (fmulBoundS x y).Mem (FloatCode.fmul i j) := by
  have hm := fmulBound_mem hx hy
  unfold fmulBoundS
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hxn, hyn⟩, hok⟩ := hc
    obtain ⟨fi, fj, hg⟩ := fmulOk_guard hx hy hok
    exact Bound.mem_atLeast0 hm
      (FloatCode.mul_nonneg fi fj hg (Bound.nonneg_mem hx hxn) (Bound.nonneg_mem hy hyn))
  · exact hm

theorem fdivBoundS_mem {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) :
    (fdivBoundS x y).Mem (FloatCode.fdiv i j) := by
  have hm := fdivBound_mem hx hy
  unfold fdivBoundS
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hxn, hyn⟩, hok⟩ := hc
    obtain ⟨fi, fj, hj0, hg⟩ := fdivOk_guard hx hy hok
    exact Bound.mem_atLeast0 hm
      (FloatCode.div_nonneg fi fj hj0 hg (Bound.nonneg_mem hx hxn) (Bound.nonneg_mem hy hyn))
  · exact hm

theorem BinFn.eq_vals (k k' : NumKind) (i j : Int) :
    BinFn.apply .eq (k.val i) (k'.val j) = if k = k' then .bool (i == j) else .null := by
  cases k <;> cases k' <;> simp [BinFn.apply, NumKind.val, Value.numPair]
  all_goals (split <;> simp_all)

theorem BinFn.lt_vals (k k' : NumKind) (i j : Int) :
    BinFn.apply .lt (k.val i) (k'.val j) = if k = k' then .bool (decide (i < j)) else .null := by
  cases k <;> cases k' <;> simp [BinFn.apply, NumKind.val, Value.numPair]
  all_goals (split <;> simp_all)

theorem BinFn.cmp_num_other {f : BinFn} (hf : f = .eq ∨ f = .lt) (k : NumKind) (i : Int)
    {w : Value} (hw : w.numOf? = none) : BinFn.apply f (k.val i) w = .null := by
  rcases hf with rfl | rfl <;> cases k <;> cases w <;>
    simp_all [BinFn.apply, NumKind.val, Value.numPair, Value.numOf?]

theorem BinFn.cmp_other_num {f : BinFn} (hf : f = .eq ∨ f = .lt) (k : NumKind) (j : Int)
    {v : Value} (hv : v.numOf? = none) : BinFn.apply f v (k.val j) = .null := by
  rcases hf with rfl | rfl <;> cases k <;> cases v <;>
    simp_all [BinFn.apply, NumKind.val, Value.numPair, Value.numOf?]

set_option maxHeartbeats 1000000 in
theorem eqAbs_sound {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (BinFn.abs .eq a b).Mem (BinFn.apply .eq v w) := by
  cases hv : v.numOf? with
  | some p =>
    obtain ⟨k, i⟩ := p
    rw [Value.numOf?_some hv] at ha ⊢
    obtain ⟨x, hx, hi, hk⟩ := AVal.mem_val.mp ha
    cases hw : w.numOf? with
    | some q =>
      obtain ⟨k', j⟩ := q
      rw [Value.numOf?_some hw] at hb ⊢
      obtain ⟨y, hy, hj, hk'⟩ := AVal.mem_val.mp hb
      rw [BinFn.eq_vals]
      split
      · rename_i hkk; subst hkk
        by_cases hij : i = j
        · subst hij; simp [BinFn.abs, AVal.Mem, intEq_of hx hy hi hj]
        · have : (i == j) = false := by simpa using hij
          rw [this]; simp [BinFn.abs, AVal.Mem, intNe_of hx hy hi hj hij]
      · rename_i hkk
        show (BinFn.abs .eq a b).null = true
        simp [BinFn.abs, hx, hy, sameNk_false hk hk' hkk]
    | none =>
      rw [BinFn.cmp_num_other (.inl rfl) k i hw]
      show (BinFn.abs .eq a b).null = true
      cases w <;> (try rename_i bb; cases bb) <;> simp_all [BinFn.abs, AVal.Mem, AVal.nested, Value.numOf?]
  | none =>
    cases hw : w.numOf? with
    | some q =>
      obtain ⟨k', j⟩ := q
      rw [Value.numOf?_some hw] at hb ⊢
      obtain ⟨y, hy, hj, hk'⟩ := AVal.mem_val.mp hb
      rw [BinFn.cmp_other_num (.inl rfl) k' j hv]
      show (BinFn.abs .eq a b).null = true
      cases v <;> (try rename_i bb; cases bb) <;> simp_all [BinFn.abs, AVal.Mem, AVal.nested, Value.numOf?]
    | none =>
      cases v <;> cases w <;> simp only [Value.numOf?, reduceCtorEq] at hv hw
      case str.str s s' =>
        simp only [AVal.Mem, AVal.MemR, Bool.and_eq_true] at ha hb
        simp only [BinFn.apply]
        by_cases hss : s = s'
        · subst hss; simp [BinFn.abs, AVal.Mem, strMayEq_of ha hb]
        · have : (s == s') = false := by simpa using hss
          rw [this]; simp [BinFn.abs, AVal.Mem, strMayNe_of ha hb hss]
      case list.list vs ws | struct.struct vs ws =>
        simp only [BinFn.abs, BinFn.apply, AVal.Mem, AVal.MemR] at ha hb ⊢
        by_cases hvw : vs = ws <;> simp_all
      all_goals (try rename_i b1 b2; cases b1 <;> cases b2) <;> (try rename_i b1; cases b1) <;>
        simp_all [BinFn.abs, BinFn.apply, AVal.Mem, AVal.nested]

set_option maxHeartbeats 1000000 in
theorem ltAbs_sound {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (BinFn.abs .lt a b).Mem (BinFn.apply .lt v w) := by
  cases hv : v.numOf? with
  | some p =>
    obtain ⟨k, i⟩ := p
    rw [Value.numOf?_some hv] at ha ⊢
    obtain ⟨x, hx, hi, hk⟩ := AVal.mem_val.mp ha
    cases hw : w.numOf? with
    | some q =>
      obtain ⟨k', j⟩ := q
      rw [Value.numOf?_some hw] at hb ⊢
      obtain ⟨y, hy, hj, hk'⟩ := AVal.mem_val.mp hb
      rw [BinFn.lt_vals]
      simp only [BinFn.abs, hx, hy]
      split
      · cases hlt : decide (i < j)
        · show (canGe x y || _) = true
          simp only [decide_eq_false_iff_not] at hlt
          simp [canGe_of_le hi hj (by omega)]
        · show (canLt x y || _) = true
          simp only [decide_eq_true_eq] at hlt
          obtain ⟨xl, xh⟩ := x
          obtain ⟨yl, yh⟩ := y
          simp only [Bound.Mem] at hi hj
          cases xl <;> cases yh <;> simp_all [canLt] <;> omega
      · rename_i hkk
        show (_ || _ || !sameNk a b) = true
        simp [sameNk_false hk hk' hkk]
    | none =>
      rw [BinFn.cmp_num_other (.inr rfl) k i hw]
      show (BinFn.abs .lt a b).null = true
      simp only [BinFn.abs, hx]
      split <;> (try rfl)
      have := AVal.nonInt_of_other hb hw
      simp_all
  | none =>
    cases hw : w.numOf? with
    | some q =>
      obtain ⟨k', j⟩ := q
      rw [Value.numOf?_some hw] at hb ⊢
      obtain ⟨y, hy, hj, hk'⟩ := AVal.mem_val.mp hb
      rw [BinFn.cmp_other_num (.inr rfl) k' j hv]
      show (BinFn.abs .lt a b).null = true
      simp only [BinFn.abs, hy]
      split <;> (try rfl)
      have := AVal.nonInt_of_other ha hv
      simp_all
    | none =>
      have hna := AVal.nonInt_of_other ha hv
      cases v <;> cases w <;> simp only [Value.numOf?, reduceCtorEq] at hv hw
      case str.str s s' =>
        simp only [AVal.Mem, AVal.MemR, Bool.and_eq_true] at ha hb
        simp only [BinFn.abs, BinFn.apply, ha.1, hb.1, Bool.true_and, Bool.true_or]
        split <;> (cases decide (s < s') <;> simp [AVal.Mem])
      case list.list vs ws | struct.struct vs ws =>
        simp only [AVal.Mem, AVal.MemR] at ha hb
        simp only [BinFn.abs, BinFn.apply]
        split <;> apply AVal.mem_ofLt3 <;> simp_all [AVal.nonInt, AVal.nested]
      all_goals (try rename_i b1 b2; cases b1 <;> cases b2) <;> (try rename_i b1; cases b1) <;>
        simp only [BinFn.abs, BinFn.apply] <;> split <;> simp_all [AVal.Mem, AVal.nonInt, AVal.nested]

/-! ### Functions of strings

`BinFn.abs_sound` proves each string function from its shape: a function of
two strings (or of a string and an integer) is `NULL` on anything else, so
its abstraction is sound where it is on those arguments. -/

theorem AVal.nonStr_of_mem {a : AVal} {v : Value} (h : a.Mem v) (hv : ∀ s, v ≠ .str s) :
    a.nonStr = true := by
  mem_cases h with i b hb hi
  all_goals simp_all [AVal.nonStr, AVal.nested]

theorem AVal.nonNumInt_of_mem {a : AVal} {v : Value} (h : a.Mem v) (hv : ∀ i, v ≠ .int i) :
    a.nonNum .int = true := by
  mem_cases h with i b hb hi
  · simp [AVal.nonNum, AVal.nonInt, hn]
  · cases k
    case int => exact absurd rfl (hv i)
    all_goals exact AVal.nonNum_of_memNum (AVal.mem_val.mp h) (by simp)
  all_goals simp_all [AVal.nonNum, AVal.nonInt, AVal.nested]

/-- A function of two strings: `g` on them, `NULL` on anything else. -/
theorem str₂_sound {f : BinFn} {g : String → String → Value} {R a b : AVal} {v w : Value}
    (hf : ∀ v w, f.apply v w = match v, w with | .str s, .str t => g s t | _, _ => .null)
    (hR : R.null = (a.nonStr || b.nonStr)) (hg : a.str = true → b.str = true → ∀ s t, R.Mem (g s t))
    (ha : a.Mem v) (hb : b.Mem w) : R.Mem (f.apply v w) := by
  rw [hf]
  split
  · rename_i s t
    simp only [AVal.Mem, AVal.MemR, Bool.and_eq_true] at ha hb
    exact hg ha.1 hb.1 s t
  · rename_i hne
    show R.null = true
    rw [hR]
    by_cases hv : ∃ s, v = .str s
    · obtain ⟨s, rfl⟩ := hv
      simp [AVal.nonStr_of_mem hb fun t ht => hne s t rfl ht]
    · simp [AVal.nonStr_of_mem ha fun s hs => hv ⟨s, hs⟩]

/-- A function of a string and an integer: `g` on them, `NULL` on anything else. -/
theorem strInt_sound {f : BinFn} {g : String → Int → Value} {R a b : AVal} {v w : Value}
    (hf : ∀ v w, f.apply v w = match v, w with | .str s, .int n => g s n | _, _ => .null)
    (hR : R.null = (a.nonStr || b.nonNum .int))
    (hg : a.str = true → b.int.isSome = true → ∀ s n, R.Mem (g s n))
    (ha : a.Mem v) (hb : b.Mem w) : R.Mem (f.apply v w) := by
  rw [hf]
  split
  · rename_i s n
    simp only [AVal.Mem, AVal.MemR, Bool.and_eq_true] at ha
    obtain ⟨x, hx, -⟩ := hb
    exact hg ha.1 (by simp [hx]) s n
  · rename_i hne
    show R.null = true
    rw [hR]
    by_cases hv : ∃ s, v = .str s
    · obtain ⟨s, rfl⟩ := hv
      simp [AVal.nonNumInt_of_mem hb fun n hn => hne s n rfl hn]
    · simp [AVal.nonStr_of_mem ha fun s hs => hv ⟨s, hs⟩]

set_option maxHeartbeats 4000000 in
theorem BinFn.abs_sound (f : BinFn) {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (f.abs a b).Mem (f.apply v w) := by
  cases f
  case bbox2 n =>
    refine BlackBox.scalarAbs_mem fun hs => ?_
    cases v <;> cases w <;> simp_all [AVal.Mem]
  case pair => exact AVal.mem_top _
  case listFn => exact AVal.mem_top _
  case greatest =>
    exact pickAbs_sound (fun k hx hy => by rw [Value.ltB_vals]; simpa using Bound.mem_greatest hx hy)
      Value.ltB_diff (fun k _ w hw => Value.ltB_mix k hw) (fun v k _ hv => Value.ltB_mix' k hv) ha hb
  case least =>
    exact pickAbs_sound (fun k hx hy => by rw [Value.ltB_vals]; simpa using Bound.mem_least hx hy)
      (fun k k' i j hk => Value.ltB_diff k' k j i (Ne.symm hk))
      (fun k _ w hw => Value.ltB_mix' k hw) (fun v k _ hv => Value.ltB_mix k hv) ha hb
  case add => exact arith_sound Bound.mem_add (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case sub => exact arith_sound Bound.mem_sub (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case dateDiff => exact arith_sound Bound.mem_sub (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case dateAdd => exact arith_sound Bound.mem_add (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case mul => exact arith_sound Bound.mem_mul (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case dadd => exact arith_sound Bound.mem_add (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case dsub => exact arith_sound Bound.mem_sub (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case dmul => exact arith_sound Bound.mem_mul (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case ddiv =>
    refine mapAbs₂_sound (g := roundDivInt?) (fun v w => by cases v <;> cases w <;> hf_tac)
      (fun _ _ i j r hi hj hr => ?_) (fun _ y i j _ hj hr => ?_) ha hb
    · have hj0 : j ≠ 0 := by intro h; simp [roundDivInt?, h] at hr
      have : r = roundDiv i j := by simp [roundDiv, hr]
      subst this; exact ddivBound_sound hi hj hj0
    · have hj0 : j = 0 := if h : j = 0 then h else by simp [roundDivInt?, h] at hr
      subst hj0
      simp only [mayZero, Option.all_some]
      cases h0 : y.has0
      · exact absurd rfl (Bound.ne_zero hj h0)
      · rfl
  case fadd =>
    exact arith_sound (f := FloatCode.fadd)
      (fun hx hy => faddBoundS_mem false hx hy (fun _ => rfl) (fun h => by cases h))
      (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case fsub =>
    exact arith_sound (f := FloatCode.fsub)
      (fun hx hy => faddBoundS_mem true hx hy (fun h => by cases h) (fun _ => rfl))
      (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case fmul => exact arith_sound fmulBoundS_mem (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case fdiv => exact arith_sound fdivBoundS_mem (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case fmod => exact arith_sound (fun _ _ => Bound.mem_top _) (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case fpow => exact arith_sound (fun _ _ => Bound.mem_top _) (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case idiv => exact divAbs_sound divBound_sound (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case imod => exact divAbs_sound modBound_sound (fun v w => by cases v <;> cases w <;> hf_tac) ha hb
  case ipow => exact powAbs_sound ha hb
  case fatan2 =>
    refine mapAbs₂_sound (g := atan2?) (fun v w => by cases v <;> cases w <;> hf_tac)
      (fun _ _ _ _ _ _ _ _ => Bound.mem_top _) (fun x y i j hi hj hr => ?_) ha hb
    cases hs : BinFn.domainSafe .fatan2 (some x) (some y)
    · rfl
    · have := BinFn.domainSafe_atan2 hs hi hj; rw [hr] at this; cases this
  case flogb =>
    refine mapAbs₂_sound (g := logb?) (fun v w => by cases v <;> cases w <;> hf_tac)
      (fun _ _ _ _ _ _ _ _ => Bound.mem_top _) (fun x y i j hi hj hr => ?_) ha hb
    cases hs : BinFn.domainSafe .flogb (some x) (some y)
    · rfl
    · have := BinFn.domainSafe_logb hs hi hj; rw [hr] at this; cases this
  case bit op =>
    refine mapAbs₂_sound (g := op.apply) (fun v w => by cases v <;> cases w <;> hf_tac)
      (fun _ _ _ _ _ _ _ _ => Bound.mem_top _) (fun x y i j _ hj hr => ?_) ha hb
    cases hs : BinFn.domainSafe (.bit op) (some x) (some y)
    · rfl
    · have := BinFn.domainSafe_bit (i := i) hs hj; rw [hr] at this; cases this
  case concat | trim =>
    exact str₂_sound (fun v w => by cases v <;> cases w <;> rfl) rfl
      (fun hs ht _ _ => by simp [BinFn.abs, BinFn.apply, AVal.Mem, hs, ht]) ha hb
  case strpos =>
    refine str₂_sound (fun v w => by cases v <;> cases w <;> rfl) rfl (fun hs ht s t => ?_) ha hb
    exact ⟨⟨some 0, some Text.sizeCap⟩, by simp [BinFn.abs, hs, ht],
      ⟨fun _ h => by cases h; exact Text.strpos_nonneg s t,
        fun _ h => by cases h; exact Text.strpos_le s t⟩, rfl⟩
  case levenshtein =>
    refine str₂_sound (fun v w => by cases v <;> cases w <;> rfl) rfl (fun hs ht s t => ?_) ha hb
    exact ⟨⟨some 0, some Text.sizeCap⟩, by simp [BinFn.abs, hs, ht],
      ⟨fun _ h => by cases h; exact Text.capped_nat_nonneg _,
        fun _ h => by cases h; exact Text.capped_le _⟩, rfl⟩
  case startsWith | endsWith | like | ilike =>
    exact str₂_sound (fun v w => by cases v <;> cases w <;> rfl) rfl
      (fun hs ht _ _ => by simp [BinFn.abs, BinFn.apply, AVal.Mem, hs, ht]) ha hb
  case substr | strRepeat =>
    exact strInt_sound (fun v w => by cases v <;> cases w <;> rfl) rfl
      (fun hs hn _ _ => by simp [BinFn.abs, BinFn.apply, AVal.Mem, hs, hn]) ha hb
  case eq => exact eqAbs_sound ha hb
  case lt => exact ltAbs_sound ha hb
  all_goals
    mem_cases₂ ha hb <;> (try cases k) <;> (try cases k') <;>
    try simp_all [BinFn.abs, BinFn.apply, and3, or3, AVal.Mem, AVal.nonBool,
      NumKind.val, AVal.MemNum]

theorem Value.eq_true_of_isTrue {v : Value} (h : v.isTrue = true) : v = .bool true := by
  cases v with
  | bool b => cases b <;> simp_all [Value.isTrue]
  | _ => simp_all [Value.isTrue]

/-- Abstract values describe a row: column `i` lies in `env.getD i top`. -/
def EnvMem (env : List AVal) (row : Row) : Prop :=
  ∀ i, (env.getD i AVal.top).Mem (row.getD i .null)

/-- A lambda's body reads its parameter in front of the row (D28). -/
theorem EnvMem.cons {env : List AVal} {row : Row} {e : AVal} {x : Value} (hx : e.Mem x)
    (h : EnvMem env row) : EnvMem (e :: env) (x :: row)
  | 0 => hx
  | i + 1 => h i

theorem Expr.abs_sound {env : List AVal} {row : Row} (h : EnvMem env row) :
    ∀ e : Expr, (e.abs env).Mem (e.eval row)
  | .lit v => AVal.mem_ofValue v
  | .field i => h i
  | .un f a => UnFn.abs_sound f (Expr.abs_sound h a)
  | .bin f a b => BinFn.abs_sound f (Expr.abs_sound h a) (Expr.abs_sound h b)
  | .ifThen c t e => by
      have hc := Expr.abs_sound h c
      simp only [abs, eval]
      by_cases hct : (c.eval row).isTrue = true
      · rw [ite_eq_left hct]
        rw [Value.eq_true_of_isTrue hct] at hc
        have htt : (c.abs env).tt = true := hc
        apply AVal.mem_join_left
        rw [ite_eq_left htt]
        exact Expr.abs_sound h t
      · rw [ite_eq_right hct]
        apply AVal.mem_join_right
        have : ((c.abs env).nonBool || (c.abs env).ff) = true := by
          rcases AVal.mem_cases hc with ⟨_, hn⟩ | ⟨_, _, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hf⟩ | ⟨_, _, hs⟩ |
            ⟨_, _, hs⟩
          · simp [AVal.nonBool, hn]
          · simp [AVal.nonBool, hb]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp [hf]
          · simp [AVal.nonBool, hs]
          · simp [AVal.nonBool, hs]
        rw [ite_eq_left this]
        exact Expr.abs_sound h e
  | .hof f l b => HoFn.abs_sound f (Expr.abs_sound h l) fun _ hx => Expr.abs_sound (h.cons hx) b

end Substrait
