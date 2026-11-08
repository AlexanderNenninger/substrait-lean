import SubstraitLean.Obligations
import SubstraitLean.PolarsShims
import SubstraitLean.SparkShims
import SubstraitLean.PolarsProfile
import SubstraitLean.SparkProfile
import SubstraitLean.Transfer
import SubstraitLean.EngineTables

/-!
# The Engine object (#900)

One Lean value describes an engine: its profile (scalar functions and
raises), its option table (choices), its observation rows, its translation,
the functions its run computes (`impl`), and the proof that those functions
are ones the table allows (`within`). `Rel.AllowedE E` is what `E` may return
for a plan: the table's choices with `E.impl`'s functions, inside
`Rel.AllowedP E.table`.

* `Profile.WithinOk p t`: where a call of `p` does not raise, its value is
  the reference's, or `t` allows the call another behaviour (`CallExtra`).
  `Profile.okImpl p` is `p`'s value where the call does not raise and the
  reference's where it does: within `t` (`Profile.okImpl_within`), and the
  same as `p.impl` on every plan that does not raise (`Rel.eval_okImpl`).
* `Engine.reference` and `Engine.spark` take Lean's functions (`Profile.spark`
  is the reference); `Engine.duckdb` (IEEE operations, `ieee_floating_point_ops`
  on, the default) takes `impl := profile.okImpl`; `Engine.polars`
  takes the functions of the written plan (`Polars.written`).
* `Engine.Refines E r tested`: every observation row the plan relies on is
  proved, or `tested` (the trusted layer's claim, D16): the per-plan
  certificate of which tested rows a result rests on.
-/

namespace Substrait

/-! ## A table's allowance, decidably -/

/-- Does `t` allow `c`'s group, at its option `o` (one the aggregate semantics
does not interpret), a behaviour the reference's table does not? -/
def extraAtB (t : ProfileTable) (c : Functions.Ctor) (o : String) : Bool :=
  match Functions.rowOf c with
  | some r => match Functions.groups.lookup r.group with
    | some os => os.contains o && !aggInterpreted.contains o &&
        (t.allows r.group o []).any fun b => !(Profile.reference.table.allows r.group o []).contains b
    | none => false
  | none => false

/-- `CallExtra` at the option `o`, from the table and the call's scope (D34). -/
theorem callExtra_of_at {t : ProfileTable} {c : Functions.Ctor} {o : String} {args : List Value}
    (h : extraAtB t c o = true) (hs : optionScope o c args = true) : CallExtra t c args := by
  unfold extraAtB at h
  split at h
  · rename_i r hr
    split at h
    · rename_i os hos
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hmem, hagg⟩, hb⟩ := h
      obtain ⟨b, hb, hnb⟩ := List.any_eq_true.1 hb
      exact ⟨r, hr, os, hos, o, by simpa using hmem, by simpa using hagg,
        ⟨b, hb, by simpa using hnb⟩, hs⟩
    · cases h
  · cases h

/-! ## Functions within a table, where they do not raise -/

/-- **Where a call of `p` does not raise, `t` allows its value**: the
reference's, or a behaviour `t` allows the call in its option's scope
(`CallExtra`). -/
def Profile.WithinOk (p : Profile) (t : ProfileTable) : Prop :=
  (∀ f v w, p.un f v = .ok w → w = f.apply v ∨ CallExtra t (.un f) [v]) ∧
    ∀ f v w x, p.bin f v w = .ok x → x = f.apply v w ∨ CallExtra t (.bin f) [v, w]

/-- `p`'s functions where a call does not raise, the reference's where it
does. -/
def Profile.okImpl (p : Profile) : Impl :=
  ⟨fun f v => match p.un f v with | .ok w => w | .error _ => f.apply v,
   fun f v w => match p.bin f v w with | .ok x => x | .error _ => f.apply v w⟩

theorem Profile.okImpl_within {p : Profile} {t : ProfileTable} (h : p.WithinOk t) :
    p.okImpl.Within t := by
  refine ⟨fun f v => ?_, fun f v w => ?_⟩
  · show (match p.un f v with | .ok w => w | .error _ => f.apply v) = f.apply v ∨ _
    cases hu : p.un f v with
    | ok w => exact h.1 f v w hu
    | error _ => exact .inl rfl
  · show (match p.bin f v w with | .ok x => x | .error _ => f.apply v w) = f.apply v w ∨ _
    cases hb : p.bin f v w with
    | ok x => exact h.2 f v w x hb
    | error _ => exact .inl rfl

theorem raiseIf_ok {k : Option Issue} {v w : Value} (h : raiseIf k v = .ok w) : w = v := by
  unfold raiseIf at h
  split at h
  · split at h <;> simp_all
  · simp_all

/-- Lean's functions are within every table. -/
theorem Impl.lean_within (t : ProfileTable) : Impl.lean.Within t :=
  ⟨fun _ _ => .inl rfl, fun _ _ _ => .inl rfl⟩

/-- **DuckDB's functions are within its table**, with IEEE operations on:
each value `duckBin` and `duckUn` change is in the scope of an option the
table allows another behaviour (D34): a domain error's NaN, a zero divisor's
`±∞` or NaN or NULL, a created NaN, a shift out of range. With
`ieee_floating_point_ops` off, `(-∞) ^ y` has no row (#900). -/
theorem Profile.duckdb_withinOk {s : DuckDBSettings} (hs : s.ieeeOps = true) :
    (Profile.duckdb s).WithinOk (Profile.duckdb.table s) := by
  obtain ⟨e, i⟩ := s
  simp only at hs; subst hs
  refine ⟨fun f v w h => ?_, fun f v w x h => ?_⟩
  · simp only [Profile.duckdb] at h
    cases v with
    | float a =>
      simp only at h
      cases hd : duckUn ⟨e, true⟩ f a with
      | none => rw [hd] at h; exact .inl (raiseIf_ok h)
      | some o =>
        right
        cases f <;> simp only [duckUn, reduceCtorEq] at hd
        rename_i g
        split at hd
        · rename_i hc
          refine callExtra_of_at (o := "on_domain_error") (by cases e <;> cases g <;> decide) ?_
          simp [optionScope, Functions.Ctor.issue, UnFn.issueAll, UnFn.issue, domainIssue, hc.2]
        · cases hd
    | _ => exact .inl (raiseIf_ok h)
  · -- Each deviation, with the option whose scope it is in.
    have hfl : ∀ {a b : Int}, f.onFloats = true →
        (duckBin ⟨e, true⟩ f a b).getD (Profile.reference.bin f (.float a) (.float b)) = .ok x →
        x = f.apply (.float a) (.float b) ∨
          CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin f) [.float a, .float b] := by
      intro a b hf h
      cases hd : duckBin ⟨e, true⟩ f a b with
      | none => rw [hd] at h; exact .inl (raiseIf_ok h)
      | some o =>
        right
        have nanC : nanCase f a b = true → extraAtB (Profile.duckdb.table ⟨e, true⟩) (.bin f)
            "nan_creation" = true → CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin f)
              [.float a, .float b] := fun hn hx => callExtra_of_at hx (by simp [optionScope, hn])
        have dom : (f.issue (.float a) (.float b)) = some .domain → extraAtB
            (Profile.duckdb.table ⟨e, true⟩) (.bin f) "on_domain_error" = true →
            CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin f) [.float a, .float b] :=
          fun hi hx => callExtra_of_at hx (by
            simp [optionScope, Functions.Ctor.issue, BinFn.issueAll, hi])
        have zero : b = 0 → extraAtB (Profile.duckdb.table ⟨e, true⟩) (.bin f)
            "on_division_by_zero" = true → CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin f)
              [.float a, .float b] := fun hb hx => callExtra_of_at hx (by
            subst hb; simp [optionScope, divisorZero])
        cases f <;> simp only [BinFn.onFloats, Bool.false_eq_true] at hf <;>
          simp only [duckBin] at hd
        case fadd | fsub | fmul =>
          split at hd
          · exact nanC (by assumption) (by cases e <;> decide)
          · cases hd
        case fdiv =>
          split at hd
          · exact zero (by assumption) (by cases e <;> decide)
          · split at hd
            · exact nanC (by assumption) (by cases e <;> decide)
            · cases hd
        case fmod =>
          split at hd
          · rename_i hb
            exact callExtra_of_at (o := "nan_creation") (by cases e <;> decide)
              (by simp [optionScope, hb])
          · split at hd
            · exact nanC (by assumption) (by cases e <;> decide)
            · cases hd
        case fpow =>
          split at hd
          · exact dom (by simp_all [BinFn.issue]) (by cases e <;> decide)
          · split at hd
            · rename_i hn hn'
              exact dom (by simp [BinFn.issue, nanIssue, hn', Bool.not_eq_true _ |>.mp hn])
                (by cases e <;> decide)
            · cases hd
        case fatan2 =>
          split at hd
          · rename_i hz
            obtain ⟨rfl, rfl⟩ := hz
            exact dom (by simp [BinFn.issue, domainIssue, atan2?]) (by cases e <;> decide)
          · cases hd
    have hint : ∀ {a b : Int}, f.onFloats = false →
        (duckBin ⟨e, true⟩ f a b).getD (Profile.reference.bin f (.int a) (.int b)) = .ok x →
        x = f.apply (.int a) (.int b) ∨
          CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin f) [.int a, .int b] := by
      intro a b hnf h
      cases hd : duckBin ⟨e, true⟩ f a b with
      | none => rw [hd] at h; exact .inl (raiseIf_ok h)
      | some o =>
        rw [hd] at h
        simp only [Option.getD] at h
        have zero : b = 0 → extraAtB (Profile.duckdb.table ⟨e, true⟩) (.bin f)
            "on_division_by_zero" = true → CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin f)
              [.int a, .int b] := fun hb hx => callExtra_of_at hx (by
            subst hb; simp [optionScope, divisorZero])
        cases f
        case idiv =>
          simp only [duckBin] at hd
          split at hd
          · rename_i hb
            cases hd; cases e <;> simp only [duckZero, reduceCtorEq, Bool.false_eq_true,
              ↓reduceIte, Except.ok.injEq] at h
            exact .inr (zero hb (by decide))
          · cases hd
        case imod =>
          simp only [duckBin] at hd
          split at hd
          · rename_i hb
            cases hd; cases e <;> simp only [duckZero, reduceCtorEq, Bool.false_eq_true,
              ↓reduceIte, Except.ok.injEq] at h
            exact .inr (zero hb (by decide))
          · split at hd
            · cases hd; simp at h
            · cases hd
        case bit g =>
          have sh : CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin (.bit g)) [.int a, .int b] →
              x = (BinFn.bit g).apply (.int a) (.int b) ∨
                CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin (.bit g)) [.int a, .int b] := .inr
          cases g with
          | shl => exact sh (callExtra_of_at (o := "shift_range") (by cases e <;> decide)
              (by simp [optionScope]))
          | shr => exact sh (callExtra_of_at (o := "shift_range") (by cases e <;> decide)
              (by simp [optionScope]))
          | _ => simp [duckBin] at hd
        all_goals first
          | (simp [BinFn.onFloats] at *; done)
          | simp [duckBin] at hd
    simp only [Profile.duckdb] at h
    cases v <;> cases w <;> simp only at h <;> try exact .inl (raiseIf_ok h)
    case float.float a b =>
      split at h
      · exact hfl (by assumption) h
      · exact .inl (raiseIf_ok h)
    case int.int a b =>
      split at h
      · exact .inl (raiseIf_ok h)
      · exact hint (by simp_all) h

/-- **The written Polars plan's functions are within Polars's table**:
wrapping `+ - *` past 64 bits (`overflow`), `//` and `%` by zero
(`on_division_by_zero`), and NaN for `∞ - ∞`, `0 · ∞`, `∞ / ∞`
(`nan_creation`), each in its option's scope (D34). -/
theorem Polars.written_within : Polars.written.Within Profile.polars.table := by
  have ovf : ∀ {f : BinFn} {a b : Int}, f.issue (.int a) (.int b) = some .wraps →
      extraAtB Profile.polars.table (.bin f) "overflow" = true →
      CallExtra Profile.polars.table (.bin f) [.int a, .int b] := fun hi hx =>
    callExtra_of_at hx (by simp [optionScope, Functions.Ctor.issue, BinFn.issueAll, hi])
  have zero : ∀ {f : BinFn} {a : Int}, extraAtB Profile.polars.table (.bin f)
      "on_division_by_zero" = true →
      CallExtra Profile.polars.table (.bin f) [.int a, .int 0] := fun hx =>
    callExtra_of_at hx (by simp [optionScope, divisorZero])
  have wrap : ∀ {f : BinFn} {a b r : Int}, f.apply (.int a) (.int b) = .int r →
      extraAtB Profile.polars.table (.bin f) "overflow" = true →
      f.issue (.int a) (.int b) = wrapIf r →
      Value.int (Polars.wrap64 r) = f.apply (.int a) (.int b) ∨
        CallExtra Profile.polars.table (.bin f) [.int a, .int b] := by
    intro f a b r hr hx hi
    by_cases h64 : inI64 r = true
    · exact .inl (by rw [hr, Polars.wrap64_of_inI64 h64])
    · exact .inr (ovf (by rw [hi]; simp [wrapIf, h64]) hx)
  refine ⟨fun _ _ => .inl rfl, fun f v w => ?_⟩
  show Polars.bin f v w = f.apply v w ∨ _
  unfold Polars.bin
  split
  · exact wrap rfl (by decide) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · exact wrap rfl (by decide) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · exact wrap rfl (by decide) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · rename_i a b
    split
    · rename_i hb; subst hb; exact .inr (zero (by decide))
    · rename_i hb; left; simp only [BinFn.apply, hb, ↓reduceIte]; rw [Polars.int_div_trunc a hb]
  · rename_i a b
    split
    · rename_i hb; subst hb; exact .inr (zero (by decide))
    · rename_i hb; left; simp only [BinFn.apply, hb, ↓reduceIte]; rw [Polars.int_mod_trunc a hb]
  · rename_i a b
    split
    · rename_i hn
      right
      -- `power` has no `nan_creation`: its NaN is a domain error's.
      by_cases hp : f = .fpow
      · subst hp
        refine callExtra_of_at (o := "on_domain_error") (by decide) ?_
        have : BinFn.issue .fpow (.float a) (.float b) = some .domain := by
          simp only [BinFn.issue, nanIssue, hn]; split <;> rfl
        simp [optionScope, Functions.Ctor.issue, BinFn.issueAll, this]
      · refine callExtra_of_at (o := "nan_creation") ?_ (by simp [optionScope, hn])
        cases f <;> simp [nanCase] at hn <;> first | decide | exact absurd rfl hp
    · exact .inl rfl
  · exact .inl rfl

/-! ## `okImpl` computes the engine's run where nothing raises -/

/-- Where `p` does not raise on `e`, `okImpl` gives its value (as `impl` does,
`Expr.evalI_of_evalP`). -/
theorem Expr.evalOk_of_evalP {p : Profile} :
    ∀ {e : Expr} {row : Row} {v : Value}, e.evalP p row = .ok v → e.eval row p.okImpl = v
  | .lit _, _, _, h | .field _, _, _, h => by
    simp only [Expr.evalP, Except.ok.injEq] at h; subst h; rfl
  | .un f a, row, v, h => by
    cases ha : a.evalP p row with
    | error k => simp [Expr.evalP, ha, bind, Except.bind] at h
    | ok x =>
      simp only [Expr.evalP, ha, bind, Except.bind] at h
      simp only [Expr.eval]; rw [evalOk_of_evalP ha]
      simp only [Profile.okImpl, h]
  | .bin f a b, row, v, h => by
    cases ha : a.evalP p row with
    | error k => simp [Expr.evalP, ha, bind, Except.bind] at h
    | ok x =>
      cases hb : b.evalP p row with
      | error k => simp [Expr.evalP, ha, hb, bind, Except.bind] at h
      | ok y =>
        simp only [Expr.evalP, ha, hb, bind, Except.bind] at h
        simp only [Expr.eval]; rw [evalOk_of_evalP ha, evalOk_of_evalP hb]
        simp only [Profile.okImpl, h]
  | .ifThen c t e, row, v, h => by
    cases hc : c.evalP p row with
    | error k => simp [Expr.evalP, hc, bind, Except.bind] at h
    | ok x =>
      simp only [Expr.evalP, hc, bind, Except.bind] at h
      simp only [Expr.eval, evalOk_of_evalP hc]
      split
      · rename_i hx; simp only [hx, ↓reduceIte] at h; exact evalOk_of_evalP h
      · rename_i hx
        simp only [hx, Bool.false_eq_true, ↓reduceIte] at h; exact evalOk_of_evalP h
  | .hof f l b, row, v, h => by
    cases hl : l.evalP p row with
    | error k => simp [Expr.evalP, hl, bind, Except.bind] at h
    | ok w =>
      simp only [Expr.evalP, hl, bind, Except.bind, HoFn.applyP] at h
      split at h
      · cases h
      · rename_i hn
        simp only [Except.ok.injEq] at h; subst h
        simp only [Expr.eval, evalOk_of_evalP hl]
        refine HoFn.apply_congr f _ fun x hx => ?_
        have := (List.findSome?_eq_none_iff.mp hn) x hx
        cases hb : b.evalP p (x :: row) with
        | error k => simp [hb, Outcome.err?] at this
        | ok y => rw [evalOk_of_evalP hb]; rfl

theorem hasMatch_congr {I J : Impl} {on : Expr} {x : Row} :
    ∀ {ys : Relation}, (∀ y ∈ ys, on.eval (x ++ y) I = on.eval (x ++ y) J) →
      hasMatch on ys x I = hasMatch on ys x J
  | [], _ => rfl
  | y :: ys, h => by
    have ih := hasMatch_congr (ys := ys) fun z hz => h z (by simp [hz])
    simp only [hasMatch, List.any_cons] at ih ⊢
    rw [h y (by simp), ih]

theorem leftJoinRow_congr {I J : Impl} {on : Expr} {n : Nat} {ys : Relation} {x : Row}
    (h : ∀ y ∈ ys, on.eval (x ++ y) I = on.eval (x ++ y) J) :
    leftJoinRow on n ys x I = leftJoinRow on n ys x J := by
  have : ((ys.map (x ++ ·)).filter fun row => (on.eval row I).isTrue) =
      (ys.map (x ++ ·)).filter fun row => (on.eval row J).isTrue :=
    List.filter_congr fun row hr => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
      rw [h y hy]
  simp only [leftJoinRow, this]

/-- `aggregateEval` under two functions that agree on every expression it
evaluates. -/
theorem aggregateEval_congr {I J : Impl} {gs : List Expr} {ms : List Measure} {rows : Relation}
    (h : ∀ row ∈ rows, ∀ e ∈ gs ++ ms.flatMap Measure.exprs, e.eval row I = e.eval row J) :
    aggregateEval gs ms rows I = aggregateEval gs ms rows J := by
  have hk : ∀ row ∈ rows, groupKey gs row I = groupKey gs row J := fun row hr =>
    List.map_congr_left fun g hg => h row hr g (List.mem_append_left _ hg)
  have hin : ∀ m ∈ ms, ∀ sub : Relation, (∀ row ∈ sub, row ∈ rows) →
      m.inputs sub I = m.inputs sub J := by
    intro m hm sub hsub
    have he : ∀ row ∈ sub, ∀ e ∈ m.exprs, e.eval row I = e.eval row J := fun row hr e he =>
      h row (hsub row hr) e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨m, hm, he⟩))
    have hkept : m.kept sub I = m.kept sub J := by
      cases hc : m.filter with
      | none => simp only [Measure.kept, hc]
      | some c =>
        simp only [Measure.kept, hc]
        exact List.filter_congr fun row hr => by
          rw [he row hr c (by simp [Measure.exprs, hc])]
    have hsub' : ∀ row ∈ m.kept sub J, row ∈ sub := fun row hr => by
      unfold Measure.kept at hr; split at hr
      · exact hr
      · exact (List.mem_filter.mp hr).1
    simp only [Measure.inputs, hkept]
    rw [List.map_congr_left fun row hr =>
      (show m.arg.eval row I = m.arg.eval row J from he row (hsub' row hr) m.arg (by simp [Measure.exprs]))]
  have hm : ∀ m ∈ ms, ∀ sub : Relation, (∀ row ∈ sub, row ∈ rows) →
      m.eval sub I = m.eval sub J := by
    intro m hm sub hsub
    cases hf : m.fn
    all_goals simp only [Measure.eval, hf]
    case collect => rw [hin m hm _ fun row hr => hsub row (List.mem_mergeSort.mp hr)]
    case pick => rw [hin m hm _ fun row hr => hsub row (List.mem_mergeSort.mp hr)]
    case concat => rw [hin m hm _ fun row hr => hsub row (List.mem_mergeSort.mp hr)]
    case mode => rw [hin m hm _ fun row hr => hsub row (List.mem_mergeSort.mp hr)]
    all_goals rw [hin m hm sub hsub]
  unfold aggregateEval
  split
  · exact congrArg (fun x => [x]) (List.map_congr_left fun m hmm => hm m hmm rows fun _ h => h)
  · rw [List.map_congr_left hk]
    refine List.map_congr_left fun k _ => ?_
    have hf : groupRows gs rows k I = groupRows gs rows k J :=
      List.filter_congr fun row hr => by rw [hk row hr]
    rw [hf]
    exact congrArg (k ++ ·) (List.map_congr_left fun m hmm =>
      hm m hmm _ fun _ hr => (List.mem_filter.mp hr).1)

/-- **A plan that does not raise computes the same rows with any functions
that agree with `p` where it does not raise.** `Rel.Raises` names the calls
whose value `Rel.eval` uses: a `CASE` evaluates only the branch it takes
(`Expr.evalP`), so a discarded branch's call need not agree. -/
theorem Rel.eval_congr_ok {p : Profile} {I : Impl}
    (hI : ∀ {e : Expr} {row : Row} {v : Value}, e.evalP p row = .ok v → e.eval row I = v)
    {cat : Catalog} : ∀ {r : Rel}, ¬r.Raises p cat → r.eval cat I = r.eval cat p.impl
  | .read _, _ | .values _ _, _ => rfl
  | .filter r c, h => by
    simp only [Raises, not_or, not_exists, not_and] at h
    have ih := eval_congr_ok hI (r := r) h.1
    simp only [eval, ih]
    exact List.filter_congr fun row hr => by
      obtain ⟨v, hv⟩ := Expr.ok_of_not_raises (h.2 row hr)
      rw [hI hv, Expr.evalI_of_evalP hv]
  | .project r es, h => by
    simp only [Raises, not_or, not_exists, not_and] at h
    have ih := eval_congr_ok hI (r := r) h.1
    simp only [eval, ih]
    exact List.map_congr_left fun row hr => congrArg (row ++ ·) (List.map_congr_left fun e he => by
      obtain ⟨v, hv⟩ := Expr.ok_of_not_raises (h.2 row hr e he)
      rw [hI hv, Expr.evalI_of_evalP hv])
  | .emit r _, h | .orderBy r _, h | .distinct r, h | .unnest r _, h | .window r _ _ _, h => by
    simp only [Raises] at h
    simp only [eval, eval_congr_ok hI (r := r) h]
  | .fetch r _ cnt, h => by
    simp only [Raises] at h
    have ih := eval_congr_ok hI (r := r) h
    cases cnt <;> simp only [eval, ih]
  | .cross a b, h | .unionAll a b, h => by
    simp only [Raises, not_or] at h
    simp only [eval, eval_congr_ok hI (r := a) h.1, eval_congr_ok hI (r := b) h.2]
  | .join a b .inner on, h => by
    simp only [Raises, not_or, not_exists, not_and] at h
    have iha := eval_congr_ok hI (r := a) h.1
    have ihb := eval_congr_ok hI (r := b) h.2.1
    simp only [eval, iha, ihb]
    exact List.filter_congr fun row hr => by
      obtain ⟨x, hx', y, hy, rfl⟩ := mem_crossRows.mp hr
      obtain ⟨v, hv⟩ := Expr.ok_of_not_raises (h.2.2 x hx' y hy)
      rw [hI hv, Expr.evalI_of_evalP hv]
  | .join a b .left on, h => by
    simp only [Raises, not_or, not_exists, not_and] at h
    have iha := eval_congr_ok hI (r := a) h.1
    have ihb := eval_congr_ok hI (r := b) h.2.1
    simp only [eval, iha, ihb]
    exact flatMap_congr fun x hx' => leftJoinRow_congr fun y hy => by
      obtain ⟨v, hv⟩ := Expr.ok_of_not_raises (h.2.2 x hx' y hy)
      rw [hI hv, Expr.evalI_of_evalP hv]
  | .semi a b _ on, h => by
    simp only [Raises, not_or, not_exists, not_and] at h
    have iha := eval_congr_ok hI (r := a) h.1
    have ihb := eval_congr_ok hI (r := b) h.2.1
    simp only [eval, iha, ihb]
    exact List.filter_congr fun x hx' => by
      rw [hasMatch_congr fun y hy => by
        obtain ⟨v, hv⟩ := Expr.ok_of_not_raises (h.2.2 x hx' y hy)
        exact (hI hv).trans (Expr.evalI_of_evalP hv).symm]
  | .aggregate r gs ms, h => by
    simp only [Raises, not_or, not_exists, not_and] at h
    have ih := eval_congr_ok hI (r := r) h.1
    simp only [eval, ih]
    exact aggregateEval_congr fun row hr e he => by
      obtain ⟨v, hv⟩ := Expr.ok_of_not_raises (h.2 row hr e he)
      rw [hI hv, Expr.evalI_of_evalP hv]

/-- **`okImpl` is the engine's run where nothing raises** (#900): on a plan
that does not raise under `p` (no call whose value `Rel.eval` uses raises,
`Rel.Raises`), `p.okImpl` and `p.impl` give the same rows. -/
theorem Rel.eval_okImpl {p : Profile} {cat : Catalog} {r : Rel} (h : ¬r.Raises p cat) :
    r.eval cat p.okImpl = r.eval cat p.impl :=
  Rel.eval_congr_ok Expr.evalOk_of_evalP h

/-! ## The Engine object -/

/-- **An engine**: what it computes (`profile`, from its facts, raising where
it raises), its option table and observation rows, its translation (`none`
where it refuses the plan), and the proof that where a call does not raise
the table allows its value. The functions a run computes, `E.impl`, are the
profile's (`Profile.okImpl`). The semantics a user verifies a plan under
(`Profile.polars`, `Profile.spark`, D21) is a choice of the user's and not
part of the engine. -/
structure Engine where
  name : String
  profile : Profile
  table : ProfileTable
  obs : ObsTable
  lower : Rel → Option Rel
  withinOk : profile.WithinOk table

/-- The functions `E`'s run computes: its profile's, where a call does not raise. -/
def Engine.impl (E : Engine) : Impl := E.profile.okImpl

theorem Engine.within (E : Engine) : E.impl.Within E.table := Profile.okImpl_within E.withinOk

/-- What `E` may return for `r`: the table's choices, with `E`'s functions. -/
def Rel.AllowedE (E : Engine) (cat : Catalog) (r : Rel) (out : Relation) : Prop :=
  r.AllowedI E.table E.impl cat out

theorem Rel.AllowedE.allowedP {E : Engine} {cat : Catalog} {r : Rel} {out : Relation}
    (h : r.AllowedE E cat out) : r.AllowedP E.table cat out :=
  ⟨E.impl, E.within, h⟩

/-- The profile whose calls never raise and give `I`'s values. -/
def Profile.ofImpl (I : Impl) : Profile where
  un f v := .ok (I.un f v)
  bin f v w := .ok (I.bin f v w)

theorem Profile.okImpl_ofImpl (I : Impl) : (Profile.ofImpl I).okImpl = I := rfl

theorem Profile.ofImpl_withinOk {I : Impl} {t : ProfileTable} (h : I.Within t) :
    (Profile.ofImpl I).WithinOk t :=
  ⟨fun f v w hw => by cases hw; exact h.1 f v, fun f v w x hx => by cases hx; exact h.2 f v w⟩

theorem Profile.reference_withinOk (t : ProfileTable) : Profile.reference.WithinOk t :=
  ⟨fun _ _ _ h => .inl (raiseIf_ok h), fun _ _ _ _ h => .inl (raiseIf_ok h)⟩

/-- The reference's functions where they do not raise, and theirs where they do:
Lean's own. -/
theorem Profile.reference_okImpl : Profile.reference.okImpl = Impl.lean := by
  have hu : ∀ f v, (match Profile.reference.un f v with | .ok w => w | .error _ => f.apply v) =
      UnFn.apply f v := fun f v => by
    cases h : Profile.reference.un f v with
    | ok w => exact raiseIf_ok h
    | error _ => rfl
  have hb : ∀ f v w, (match Profile.reference.bin f v w with | .ok x => x | .error _ => f.apply v w) =
      BinFn.apply f v w := fun f v w => by
    cases h : Profile.reference.bin f v w with
    | ok x => exact raiseIf_ok h
    | error _ => rfl
  simp only [Profile.okImpl, Impl.lean]
  congr 1 <;> funext <;> simp only [hu, hb]

/-- **What Spark computes is within its table**: its two zeros, its NaN for
`∞ - ∞` and a domain error each have a row; every other value it gives is
the reference's (`Profile.sparkRun`). -/
theorem Profile.sparkRun_withinOk : Profile.sparkRun.WithinOk Profile.spark.table := by
  have ce : ∀ c, callExtraB Profile.spark.table c = true → CallExtra Profile.spark.table c :=
    fun _ => callExtra_of_B
  refine ⟨fun f v w h => ?_, fun f v w x h => ?_⟩
  · simp only [Profile.sparkRun, Spark.runUn] at h
    split at h
    · exact .inr (ce _ (by decide))
    · exact .inr (ce _ (by decide))
    · split at h
      · cases h
      · exact .inl (raiseIf_ok h)
    · split at h
      · exact .inl (raiseIf_ok h)
      · cases h
  · simp only [Profile.sparkRun, Spark.runBin] at h
    split at h
    · exact .inr (ce _ (by decide))
    · exact .inr (ce _ (by decide))
    · exact .inr (ce _ (by decide))
    · exact .inr (ce _ (by decide))
    · exact .inr (ce _ (by decide))
    · split at h
      · exact .inl (raiseIf_ok h)
      · cases h
    · split at h
      · exact .inl (raiseIf_ok h)
      · cases h
    · split at h
      · exact .inl (raiseIf_ok h)
      · cases h

/-- The reference. -/
def Engine.reference : Engine where
  name := "reference"
  profile := Profile.reference
  table := Profile.reference.table
  obs := Profile.reference.obs
  lower := some
  withinOk := Profile.reference_withinOk _

/-- DuckDB with IEEE operations (`ieee_floating_point_ops`, the default),
through its lowering (`Lowering.duckdb`, written for the default settings). -/
def Engine.duckdb (s : DuckDBSettings) (hs : s.ieeeOps = true) : Engine where
  name := "duckdb"
  profile := Profile.duckdb s
  table := Profile.duckdb.table s
  obs := Profile.duckdb.obs
  lower r := some (Lowering.duckdb.lowerRel r)
  withinOk := Profile.duckdb_withinOk hs

/-- Polars, as the translation writes the plan (`Polars.written`), until its
run profile and lowering are generated (#271 2b). -/
def Engine.polars : Engine where
  name := "polars"
  profile := Profile.ofImpl Polars.written
  table := Profile.polars.table
  obs := Profile.polars.obs
  lower := some
  withinOk := Profile.ofImpl_withinOk Polars.written_within

/-- Spark under ANSI: the reference's functions (`Profile.spark`), its own
choices. -/
def Engine.spark : Engine where
  name := "spark"
  profile := Profile.ofImpl Impl.lean
  table := Profile.spark.table
  obs := Profile.spark.obs
  lower := some
  withinOk := Profile.ofImpl_withinOk (Impl.lean_within _)

/-! ## The rows a plan relies on -/

/-- The observation rows of `E` at the options `r` reads. -/
def Engine.rowsUsed (E : Engine) (r : Rel) : List ObsRow :=
  r.reads.filterMap fun (g, o, _) => E.obs.row? g o

/-- Is the evidence a Lean theorem? -/
def Evidence.isProved : Evidence → Bool
  | .proved _ _ => true
  | _ => false

/-- **The certificate of a plan on `E`**: every option the plan reads has
an observation row of `E` (an uncharacterized option has none, and leaves the
certificate unprovable), and that row is proved, or `tested` holds of it.
`tested` is the trusted layer's claim (D16), never asserted inside the core:
the certificate lists exactly the tested rows a result rests on. -/
def Engine.Refines (E : Engine) (r : Rel) (tested : ObsRow → Prop) : Prop :=
  ∀ rd ∈ r.reads, ∃ row, E.obs.row? rd.1 rd.2.1 = some row ∧
    (row.evidence.isProved = true ∨ tested row)

theorem Engine.Refines.rowsUsed {E : Engine} {r : Rel} {tested : ObsRow → Prop}
    (h : E.Refines r tested) : ∀ row ∈ E.rowsUsed r, row.evidence.isProved = true ∨ tested row := by
  intro row hr
  obtain ⟨⟨g, o, ps⟩, hrd, hrow⟩ := List.mem_filterMap.1 hr
  obtain ⟨row', h1, h2⟩ := h _ hrd
  simp only at h1 hrow
  rw [h1] at hrow; cases hrow; exact h2

/-- The rows of `E` a plan may rely on whose evidence is not a theorem. -/
def Engine.testedRows (E : Engine) : List ObsRow :=
  E.obs.filterMap fun (_, _, row) => if row.evidence.isProved then none else some row

-- No engine's certificate is empty: each but the reference has rows that
-- are not theorems (so `Refines` is a real hypothesis, which `#print axioms`
-- cannot show).
#guard !(Engine.duckdb {} rfl).testedRows.isEmpty && !Engine.polars.testedRows.isEmpty &&
  !Engine.spark.testedRows.isEmpty && Engine.reference.testedRows.isEmpty

end Substrait
