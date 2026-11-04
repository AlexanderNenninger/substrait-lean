import Lean.Data.Json
import SubstraitLean.EngineTables

/-!
# The options a plan meets, and the option-wise transfer check (#444, step 3c)

`Rel.AllowedP t` reads `t` only at the options the plan meets
(`Rel.reads`), each with the preferences it reads it for: its calls' groups'
options and its aggregates' (with none: the parser has resolved the plan's
own), and an `ORDER BY`'s `null_order` (with the key's placement) and
`clustered` (where a key is). So a result one profile allows
for a plan, another allows too when, at each of those options, its choices
are within the first's (`Rel.AllowedP_transfer`). Whatever is proved of every
result one profile allows then holds of every result the other allows: the
option-wise transfer check of `docs/core-semantics.md` ("Which plans run on
an engine"), decided by `transferB` for the plan at hand.

`Rel.reads` is the options a plan meets. The proof of a plan under the
reference uses at most these: an upper bound on step 3c's option dependency
report, which `verify` can narrow by checking the plan again with each of
them left open. -/

namespace Substrait

open Functions (Ctor rowOf groups)

/-! ## What a plan meets -/

/-- The calls of an expression, by constructor. -/
def Expr.ctors : Expr → List Ctor
  | .lit _ | .field _ => []
  | .un f a => .un f :: a.ctors
  | .bin f a b => .bin f :: (a.ctors ++ b.ctors)
  | .ifThen c t e => c.ctors ++ t.ctors ++ e.ctors
  | .hof _ l b => l.ctors ++ b.ctors

/-- A read of a profile's table: a group, an option and the plan's preferences. -/
abbrev Read := String × String × List Behaviour

/-- The options of a call's group, with the group. -/
def ctorReads (c : Ctor) : List Read :=
  match rowOf c with
  | some r => ((groups.lookup r.group).getD []).map (r.group, ·, [])
  | none => []

def Expr.reads (e : Expr) : List Read := e.ctors.flatMap ctorReads

/-- The options an aggregate meets: its group's, and those `AggFn.AllowedChoice` reads. -/
def AggFn.reads (f : AggFn) : List Read :=
  ctorReads (.agg f) ++ match f with
    | .fsum | .avg => [("agg.fsum", "sum_order", [])]
    | .var _ _ => [("agg.var", "stat_algo", [])]
    | .cov _ | .corr => [("agg.stat", "stat_algo", [])]
    | .quantile true _ _ => [("agg.quant", "quantile_interp", [])]
    | _ => []

def Measure.ctors (m : Measure) : List Ctor := m.arg.ctors ++ (m.filter.map Expr.ctors).getD []

def Measure.reads (m : Measure) : List Read :=
  m.arg.reads ++ (m.filter.map Expr.reads).getD [] ++ m.fn.reads

/-- An `ORDER BY`'s options: each key's NULL placement, and clustering where a key asks for it. -/
def sortReads (keys : List SortKey) : List Read :=
  keys.map (fun k => ("rel.sort", "null_order", k.nullPrefs)) ++
    if keys.any (·.clustered) then [("rel.sort", "clustered", [])] else []

/-- Rows compared as keys (grouping, `DISTINCT`, a join's equality): NaN and the zeros. -/
def keyReads : List Read := [("rel.keys", "nan_equality", []), ("rel.keys", "zero_sign", [])]

/-- A join's: its keys, and whether NULL keys match. -/
def joinReads : List Read := keyReads ++ [("rel.join", "null_join_keys", [])]

/-- The calls of a plan's expressions. -/
def Rel.ctors : Rel → List Ctor
  | .read _ | .values _ _ => []
  | .filter r c => r.ctors ++ c.ctors
  | .project r es => r.ctors ++ es.flatMap Expr.ctors
  | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _ | .distinct r | .unnest r _ => r.ctors
  | .cross a b | .unionAll a b => a.ctors ++ b.ctors
  | .join a b _ on | .semi a b _ on => a.ctors ++ b.ctors ++ on.ctors
  | .aggregate r gs ms => r.ctors ++ gs.flatMap Expr.ctors ++ ms.flatMap Measure.ctors

/-- **The options a plan meets**, by group. -/
def Rel.reads : Rel → List Read
  | .read _ | .values _ _ => []
  | .filter r c => r.reads ++ c.reads
  | .project r es => r.reads ++ es.flatMap Expr.reads
  | .emit r _ | .fetch r _ _ | .window r _ _ _ | .unnest r _ => r.reads
  | .distinct r => r.reads ++ keyReads
  | .orderBy r keys => r.reads ++ sortReads keys
  | .cross a b | .unionAll a b => a.reads ++ b.reads
  | .join a b _ on | .semi a b _ on => a.reads ++ b.reads ++ on.reads ++ joinReads
  | .aggregate r gs ms => r.reads ++ gs.flatMap Expr.reads ++ ms.flatMap Measure.reads ++
      if gs.isEmpty then [] else keyReads

theorem Expr.ctorReads_sub {e : Expr} {c : Ctor} (hc : c ∈ e.ctors) : ∀ p ∈ ctorReads c, p ∈ e.reads :=
  fun _ hp => List.mem_flatMap.mpr ⟨c, hc, hp⟩

theorem Rel.ctorReads_sub : ∀ {r : Rel} {c : Ctor}, c ∈ r.ctors → ∀ p ∈ ctorReads c, p ∈ r.reads
  | .read _, _, h, _, _ | .values _ _, _, h, _, _ => by simp [Rel.ctors] at h
  | .filter r e, c, h, p, hp => by
    simp only [Rel.ctors, List.mem_append] at h
    simp only [Rel.reads, List.mem_append]
    rcases h with h | h
    · exact .inl (Rel.ctorReads_sub h p hp)
    · exact .inr (Expr.ctorReads_sub h p hp)
  | .project r es, c, h, p, hp => by
    simp only [Rel.ctors, List.mem_append, List.mem_flatMap] at h
    simp only [Rel.reads, List.mem_append, List.mem_flatMap]
    rcases h with h | ⟨e, he, h⟩
    · exact .inl (Rel.ctorReads_sub h p hp)
    · exact .inr ⟨e, he, Expr.ctorReads_sub h p hp⟩
  | .emit r _, c, h, p, hp | .fetch r _ _, c, h, p, hp | .window r _ _ _, c, h, p, hp
  | .unnest r _, c, h, p, hp => by
    simp only [Rel.ctors] at h; simp only [Rel.reads]; exact Rel.ctorReads_sub h p hp
  | .distinct r, c, h, p, hp => by
    simp only [Rel.ctors] at h; simp only [Rel.reads, List.mem_append]
    exact .inl (Rel.ctorReads_sub h p hp)
  | .orderBy r _, c, h, p, hp => by
    simp only [Rel.ctors] at h; simp only [Rel.reads, List.mem_append]
    exact .inl (Rel.ctorReads_sub h p hp)
  | .cross a b, c, h, p, hp | .unionAll a b, c, h, p, hp => by
    simp only [Rel.ctors, List.mem_append] at h
    simp only [Rel.reads, List.mem_append]
    rcases h with h | h
    · exact .inl (Rel.ctorReads_sub h p hp)
    · exact .inr (Rel.ctorReads_sub h p hp)
  | .join a b _ on, c, h, p, hp | .semi a b _ on, c, h, p, hp => by
    simp only [Rel.ctors, List.mem_append] at h
    simp only [Rel.reads, List.mem_append]
    rcases h with (h | h) | h
    · exact .inl (.inl (.inl (Rel.ctorReads_sub h p hp)))
    · exact .inl (.inl (.inr (Rel.ctorReads_sub h p hp)))
    · exact .inl (.inr (Expr.ctorReads_sub h p hp))
  | .aggregate r gs ms, c, h, p, hp => by
    simp only [Rel.ctors, List.mem_append, List.mem_flatMap] at h
    simp only [Rel.reads, List.mem_append, List.mem_flatMap]
    rcases h with (h | ⟨e, he, h⟩) | ⟨m, hm, h⟩
    · exact .inl (.inl (.inl (Rel.ctorReads_sub h p hp)))
    · exact .inl (.inl (.inr ⟨e, he, Expr.ctorReads_sub h p hp⟩))
    · refine .inl (.inr ⟨m, hm, ?_⟩)
      simp only [Measure.ctors, List.mem_append] at h
      simp only [Measure.reads, List.mem_append]
      rcases h with h | h
      · exact .inl (.inl (Expr.ctorReads_sub h p hp))
      · refine .inl (.inr ?_)
        cases hf : m.filter with
        | none => simp [hf] at h
        | some e => simp only [hf, Option.map_some, Option.getD_some] at h ⊢
                    exact Expr.ctorReads_sub h p hp

/-! ## Functions that agree on a plan's calls -/

/-- `I` and `J` agree on the calls `cs`. -/
def Impl.AgreeOn (cs : List Ctor) (I J : Impl) : Prop :=
  (∀ f, .un f ∈ cs → ∀ v, I.un f v = J.un f v) ∧
    ∀ f, .bin f ∈ cs → ∀ v w, I.bin f v w = J.bin f v w

theorem Impl.AgreeOn.sub {cs ds : List Ctor} {I J : Impl} (h : Impl.AgreeOn ds I J)
    (hs : ∀ c ∈ cs, c ∈ ds) : Impl.AgreeOn cs I J :=
  ⟨fun f hf => h.1 f (hs _ hf), fun f hf => h.2 f (hs _ hf)⟩

theorem Expr.evalI_congr {I J : Impl} : ∀ {e : Expr}, Impl.AgreeOn e.ctors I J →
    ∀ row, e.evalI I row = e.evalI J row
  | .lit _, _, _ | .field _, _, _ => rfl
  | .un f a, h, row => by
    simp only [Expr.evalI]
    rw [Expr.evalI_congr (h.sub fun c hc => List.mem_cons_of_mem _ hc) row]
    exact h.1 f (List.mem_cons_self ..) _
  | .bin f a b, h, row => by
    simp only [Expr.evalI]
    rw [Expr.evalI_congr (h.sub fun c hc => List.mem_cons_of_mem _ (List.mem_append_left _ hc)) row,
      Expr.evalI_congr (h.sub fun c hc => List.mem_cons_of_mem _ (List.mem_append_right _ hc)) row]
    exact h.2 f (List.mem_cons_self ..) _ _
  | .ifThen c t e, h, row => by
    simp only [Expr.evalI]
    rw [Expr.evalI_congr (h.sub fun _ hc => by simp [Expr.ctors, hc]) row,
      Expr.evalI_congr (h.sub fun _ hc => by simp [Expr.ctors, hc]) row,
      Expr.evalI_congr (h.sub fun _ hc => by simp [Expr.ctors, hc]) row]
  | .hof f l b, h, row => by
    simp only [Expr.evalI]
    rw [Expr.evalI_congr (h.sub fun _ hc => by simp [Expr.ctors, hc]) row]
    congr 1; funext x
    exact Expr.evalI_congr (h.sub fun _ hc => by simp [Expr.ctors, hc]) [x]

theorem evalI_congr_list {I J : Impl} {es : List Expr}
    (h : Impl.AgreeOn (es.flatMap Expr.ctors) I J) (row : Row) :
    es.map (·.evalI I row) = es.map (·.evalI J row) :=
  List.map_congr_left fun e he =>
    Expr.evalI_congr (h.sub fun _ hc => List.mem_flatMap.mpr ⟨e, he, hc⟩) row

theorem Measure.inputsI_congr {I J : Impl} {m : Measure} (h : Impl.AgreeOn m.ctors I J) :
    m.inputsI I = m.inputsI J := by
  have ha := Expr.evalI_congr (h.sub fun _ hc => List.mem_append_left _ hc)
  have hk : m.keptI I = m.keptI J := by
    funext rows
    unfold Measure.keptI
    cases hf : m.filter with
    | none => rfl
    | some c =>
      have hc := Expr.evalI_congr (e := c) (h.sub fun _ hc =>
        List.mem_append_right _ (by simp [hf, hc]))
      simp only [hc]
  funext rows
  unfold Measure.inputsI
  rw [hk]
  have : m.arg.evalI I = m.arg.evalI J := funext ha
  rw [this]

theorem Measure.allowedP_congr {t : ProfileTable} {I J : Impl} {m : Measure}
    (h : Impl.AgreeOn m.ctors I J) : m.AllowedP t I = m.AllowedP t J := by
  funext rows v; simp only [Measure.AllowedP, Measure.inputsI_congr h]

theorem Forall2.imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, (∀ a ∈ l, ∀ b, R a b → S a b) → Forall2 R l l' → Forall2 S l l'
  | _, _, _, .nil => .nil
  | _, _, h, .cons hab t =>
    .cons (h _ (List.mem_cons_self ..) _ hab)
      (Forall2.imp_mem (fun a ha => h a (List.mem_cons_of_mem _ ha)) t)

theorem forall₂_congr_mem {α β : Type} {R S : α → β → Prop} {l : List α} {l' : List β}
    (h : ∀ a ∈ l, ∀ b, R a b ↔ S a b) : Forall2 R l l' ↔ Forall2 S l l' :=
  ⟨Forall2.imp_mem fun a ha b => (h a ha b).mp, Forall2.imp_mem fun a ha b => (h a ha b).mpr⟩

theorem aggAllowedP_congr {t : ProfileTable} {I J : Impl} {gs : List Expr} {ms : List Measure}
    (hg : Impl.AgreeOn (gs.flatMap Expr.ctors) I J) (hm : Impl.AgreeOn (ms.flatMap Measure.ctors) I J)
    (rows out : Relation) : aggAllowedP t I gs ms rows out ↔ aggAllowedP t J gs ms rows out := by
  have hk : groupKeyI I gs = groupKeyI J gs := funext fun row => evalI_congr_list hg row
  have hr : groupRowsI I gs = groupRowsI J gs := by
    funext rows k; simp only [groupRowsI, hk]
  have hms : ∀ m ∈ ms, m.AllowedP t I = m.AllowedP t J := fun m hmem =>
    Measure.allowedP_congr (hm.sub fun _ hc => List.mem_flatMap.mpr ⟨m, hmem, hc⟩)
  unfold aggAllowedP
  rw [hk, hr]
  split
  · exact exists_congr fun vs => and_congr_right fun _ =>
      forall₂_congr_mem fun m hmem v => by rw [hms m hmem]
  · exact forall₂_congr_mem fun k _ row => exists_congr fun vs => and_congr_right fun _ =>
      forall₂_congr_mem fun m hmem v => by rw [hms m hmem]

/-- **`AllowedI` reads the functions only at the plan's calls.** -/
theorem Rel.allowedI_congr {t : ProfileTable} {I J : Impl} {cat : Catalog} :
    ∀ {r : Rel}, Impl.AgreeOn r.ctors I J → ∀ out, r.AllowedI t I cat out ↔ r.AllowedI t J cat out
  | .read _, _, _ | .values _ _, _, _ => Iff.rfl
  | .filter r c, h, _ => by
    have ih := Rel.allowedI_congr (t := t) (cat := cat) (r := r) (h.sub fun _ hc => List.mem_append_left _ hc)
    have hc := Expr.evalI_congr (e := c) (h.sub fun _ hc => List.mem_append_right _ hc)
    simp only [Rel.AllowedI, ih, hc]
  | .project r es, h, _ => by
    have ih := Rel.allowedI_congr (t := t) (cat := cat) (r := r) (h.sub fun _ hc => List.mem_append_left _ hc)
    have he := evalI_congr_list (es := es) (h.sub fun _ hc => List.mem_append_right _ hc)
    simp only [Rel.AllowedI, ih, he]
  | .emit r _, h, _ | .distinct r, h, _ | .unnest r _, h, _ | .window r _ _ _, h, _ => by
    simp only [Rel.AllowedI, Rel.allowedI_congr (t := t) (cat := cat) (r := r) h]
  | .fetch r _ _, h, _ => exists_congr fun i => and_congr_left' (Rel.allowedI_congr (t := t) (cat := cat) (r := r) h i)
  | .orderBy r _, h, _ => by simp only [Rel.AllowedI, Rel.allowedI_congr (t := t) (cat := cat) (r := r) h]
  | .cross a b, h, _ | .unionAll a b, h, _ => by
    simp only [Rel.AllowedI,
      Rel.allowedI_congr (t := t) (cat := cat) (r := a) (h.sub fun _ hc => List.mem_append_left _ hc),
      Rel.allowedI_congr (t := t) (cat := cat) (r := b) (h.sub fun _ hc => List.mem_append_right _ hc)]
  | .join a b .inner on, h, _ => by
    have ho := Expr.evalI_congr (e := on) (h.sub fun _ hc => List.mem_append_right _ hc)
    simp only [Rel.AllowedI, ho,
      Rel.allowedI_congr (t := t) (cat := cat) (r := a) (h.sub fun _ hc => by simp [Rel.ctors, hc]),
      Rel.allowedI_congr (t := t) (cat := cat) (r := b) (h.sub fun _ hc => by simp [Rel.ctors, hc])]
  | .join a b .left on, h, _ => by
    have ho := Expr.evalI_congr (e := on) (h.sub fun _ hc => List.mem_append_right _ hc)
    have hl : leftJoinRowI I on = leftJoinRowI J on := by
      funext n ys x; simp only [leftJoinRowI, ho]
    simp only [Rel.AllowedI, hl,
      Rel.allowedI_congr (t := t) (cat := cat) (r := a) (h.sub fun _ hc => by simp [Rel.ctors, hc]),
      Rel.allowedI_congr (t := t) (cat := cat) (r := b) (h.sub fun _ hc => by simp [Rel.ctors, hc])]
  | .semi a b _ on, h, _ => by
    have ho := Expr.evalI_congr (e := on) (h.sub fun _ hc => List.mem_append_right _ hc)
    have hm : hasMatchI I on = hasMatchI J on := by
      funext ys x; simp only [hasMatchI, ho]
    simp only [Rel.AllowedI, hm,
      Rel.allowedI_congr (t := t) (cat := cat) (r := a) (h.sub fun _ hc => by simp [Rel.ctors, hc]),
      Rel.allowedI_congr (t := t) (cat := cat) (r := b) (h.sub fun _ hc => by simp [Rel.ctors, hc])]
  | .aggregate r gs ms, h, _ => by
    simp only [Rel.AllowedI,
      Rel.allowedI_congr (t := t) (cat := cat) (r := r)
        (h.sub fun _ hc => List.mem_append_left _ (List.mem_append_left _ hc)),
      aggAllowedP_congr (t := t) (gs := gs) (ms := ms)
        (h.sub fun _ hc => List.mem_append_left _ (List.mem_append_right _ hc))
        (h.sub fun _ hc => List.mem_append_right _ hc)]

/-! ## Choices that agree on a plan's options -/

/-- `t` allows no more than `u` at the read `p`. -/
def ProfileTable.LeAt (t u : ProfileTable) (p : Read) : Prop :=
  ∀ b, b ∈ t.allows p.1 p.2.1 p.2.2 → b ∈ u.allows p.1 p.2.1 p.2.2

section MonoOn
variable {t u : ProfileTable}

theorem AggFn.AllowedP.monoOn {f : AggFn} (h : ∀ p ∈ f.reads, t.LeAt u p) {vs : List Value}
    {v : Value} : f.AllowedP t vs v → f.AllowedP u vs v := by
  have hlit : ∀ {g o : String} {P : Behaviour → Prop}, (g, o, []) ∈ f.reads →
      (∃ b ∈ t.allows g o [], P b) → ∃ b ∈ u.allows g o [], P b :=
    fun hp ⟨b, hb, rest⟩ => ⟨b, h _ hp b hb, rest⟩
  rintro (hc | ⟨r, hr, os, hos, o, ho, hi, b, hb, hn⟩)
  · left
    cases f
    case quantile cont num scale =>
      cases cont
      · exact hc
      · simp only [AggFn.AllowedChoice] at hc ⊢
        split at hc
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (by assumption))]; exact hc
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by assumption))]
          exact hlit (by simp [AggFn.reads]) hc
    case fsum | avg =>
      simp only [AggFn.AllowedChoice] at hc ⊢
      split at hc
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by assumption))]; exact hc
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by assumption))]
        exact hlit (by simp [AggFn.reads]) hc
    case var | cov | corr => exact hlit (by simp [AggFn.reads]) hc
    all_goals exact hc
  · right
    have hp : (r.group, o, []) ∈ f.reads := by
      simp only [AggFn.reads, ctorReads, hr, hos, Option.getD_some, List.mem_append, List.mem_map]
      exact .inl ⟨o, ho, rfl⟩
    exact ⟨r, hr, os, hos, o, ho, hi, b, h _ hp b hb, hn⟩

theorem Measure.AllowedP.monoOn {I : Impl} {m : Measure} (h : ∀ p ∈ m.reads, t.LeAt u p)
    {rows : Relation} {v : Value} : m.AllowedP t I rows v → m.AllowedP u I rows v :=
  fun ⟨s, hs, hsort, hf⟩ => ⟨s, hs, hsort, AggFn.AllowedP.monoOn
    (fun p hp => h p (List.mem_append_right _ hp)) hf⟩

theorem aggAllowedP.monoOn {I : Impl} {gs : List Expr} {ms : List Measure}
    (h : ∀ p ∈ ms.flatMap Measure.reads, t.LeAt u p) {rows out : Relation} :
    aggAllowedP t I gs ms rows out → aggAllowedP u I gs ms rows out := by
  have hm : ∀ m ∈ ms, ∀ (rows : Relation) (v : Value), m.AllowedP t I rows v → m.AllowedP u I rows v :=
    fun m hmem _ _ => Measure.AllowedP.monoOn fun p hp => h p (List.mem_flatMap.mpr ⟨m, hmem, hp⟩)
  unfold aggAllowedP
  split
  · rintro ⟨vs, rfl, hv⟩
    exact ⟨vs, rfl, Forall2.imp_mem (fun m hmem v => hm m hmem rows v) hv⟩
  · exact Forall2.imp fun _ _ ⟨vs, hrow, hv⟩ =>
      ⟨vs, hrow, Forall2.imp_mem (fun m hmem v => hm m hmem _ v) hv⟩

theorem SortedP.monoOn {keys : List SortKey} (h : ∀ p ∈ sortReads keys, t.LeAt u p)
    {out : Relation} : SortedP t keys out → SortedP u keys out := fun ⟨cmp, hc, nfs, hn, hcl, hs⟩ =>
  ⟨cmp, hc, nfs,
    Forall2.imp_mem (fun k hk _ hn => h ("rel.sort", "null_order", k.nullPrefs)
      (List.mem_append_left _ (List.mem_map.mpr ⟨k, hk, rfl⟩)) _ hn) hn,
    fun k hk hck => h ("rel.sort", "clustered", [])
      (List.mem_append_right _ (by
        rw [ite_eq_left_of_eq_true _ _ (eq_true (List.any_eq_true.mpr ⟨k, hk, hck⟩))]
        exact List.mem_singleton_self _))
      _ (hcl k hk hck), hs⟩

/-- **`AllowedI` reads the choices only at the plan's options.** -/
theorem Rel.AllowedI.monoOn {I : Impl} {cat : Catalog} :
    ∀ {r : Rel}, (∀ p ∈ r.reads, t.LeAt u p) → ∀ {out : Relation},
      r.AllowedI t I cat out → r.AllowedI u I cat out
  | .read _, _, _, ho | .values _ _, _, _, ho => ho
  | .filter r _, h, _, ⟨i, hi, ho⟩ | .project r _, h, _, ⟨i, hi, ho⟩ =>
    ⟨i, Rel.AllowedI.monoOn (fun p hp => h p (List.mem_append_left _ hp)) hi, ho⟩
  | .distinct r, h, _, ⟨i, hi, ho⟩ =>
    ⟨i, Rel.AllowedI.monoOn (fun p hp => h p (List.mem_append_left _ hp)) hi, ho⟩
  | .emit r _, h, _, ⟨i, hi, ho⟩ | .fetch r _ _, h, _, ⟨i, hi, ho⟩
  | .unnest r _, h, _, ⟨i, hi, ho⟩ | .window r _ _ _, h, _, ⟨i, hi, ho⟩ =>
    ⟨i, Rel.AllowedI.monoOn (r := r) (fun p hp => h p (by simp only [Rel.reads]; exact hp)) hi, ho⟩
  | .orderBy r _, h, _, ⟨i, hi, hp, hs⟩ =>
    ⟨i, Rel.AllowedI.monoOn (fun p hp => h p (List.mem_append_left _ hp)) hi, hp,
      SortedP.monoOn (fun p hp => h p (List.mem_append_right _ hp)) hs⟩
  | .cross a b, h, _, ⟨x, y, hx, hy, ho⟩ | .unionAll a b, h, _, ⟨x, y, hx, hy, ho⟩ =>
    ⟨x, y, Rel.AllowedI.monoOn (fun p hp => h p (List.mem_append_left _ hp)) hx,
      Rel.AllowedI.monoOn (fun p hp => h p (List.mem_append_right _ hp)) hy, ho⟩
  | .join a b .inner _, h, _, ⟨x, y, hx, hy, ho⟩ | .join a b .left _, h, _, ⟨x, y, hx, hy, ho⟩
  | .semi a b _ _, h, _, ⟨x, y, hx, hy, ho⟩ =>
    ⟨x, y, Rel.AllowedI.monoOn (fun p hp => h p (by simp [Rel.reads, hp])) hx,
      Rel.AllowedI.monoOn (fun p hp => h p (by simp [Rel.reads, hp])) hy, ho⟩
  | .aggregate r _ _, h, _, ⟨i, hi, o, hp, ha⟩ =>
    ⟨i, Rel.AllowedI.monoOn (fun p hp => h p (by simp [Rel.reads, hp])) hi, o, hp,
      aggAllowedP.monoOn (fun p hp => h p (by simp [Rel.reads, hp])) ha⟩

end MonoOn

/-! ## The transfer -/

open Classical in
/-- `I` at the plan's calls, Lean's own functions elsewhere. -/
noncomputable def Impl.restrict (cs : List Ctor) (I : Impl) : Impl where
  un f v := if Ctor.un f ∈ cs then I.un f v else f.apply v
  bin f v w := if Ctor.bin f ∈ cs then I.bin f v w else f.apply v w

/-- **The option-wise transfer**: a result `t` allows for `r`, `u` allows
too, when `u`'s choices are within `t`'s at every option `r` meets. -/
theorem Rel.AllowedP_transfer {t u : ProfileTable} {cat : Catalog} {r : Rel}
    (h : ∀ p ∈ r.reads, t.LeAt u p) {out : Relation} :
    r.AllowedP t cat out → r.AllowedP u cat out := by
  rintro ⟨I, ⟨hun, hbin⟩, ho⟩
  classical
  let J := Impl.restrict r.ctors I
  have hag : Impl.AgreeOn r.ctors I J :=
    ⟨fun f hf v => by simp [J, Impl.restrict, hf], fun f hf v w => by simp [J, Impl.restrict, hf]⟩
  have hx : ∀ c ∈ r.ctors, CallExtra t c → CallExtra u c :=
    fun c hc ⟨row, hr, os, hos, o, ho, b, hb, hn⟩ =>
      ⟨row, hr, os, hos, o, ho, b, h _ (Rel.ctorReads_sub hc _ (by
        simp only [ctorReads, hr, hos, Option.getD_some, List.mem_map]; exact ⟨o, ho, rfl⟩)) b hb, hn⟩
  refine ⟨J, ⟨fun f v => ?_, fun f v w => ?_⟩, ?_⟩
  · by_cases hf : Ctor.un f ∈ r.ctors
    · simp only [J, Impl.restrict, hf, ite_true]; exact (hun f v).imp_right (hx _ hf)
    · left; simp [J, Impl.restrict, hf]
  · by_cases hf : Ctor.bin f ∈ r.ctors
    · simp only [J, Impl.restrict, hf, ite_true]; exact (hbin f v w).imp_right (hx _ hf)
    · left; simp [J, Impl.restrict, hf]
  · exact Rel.AllowedI.monoOn h ((Rel.allowedI_congr hag out).mp ho)

/-! ## Deciding it -/

/-- A decidable test of `LeAt`. -/
def ProfileTable.leAtB (t u : ProfileTable) (p : Read) : Bool :=
  (t.allows p.1 p.2.1 p.2.2).all (u.allows p.1 p.2.1 p.2.2).contains

theorem ProfileTable.leAt_of_leAtB {t u : ProfileTable} {p : Read}
    (h : t.leAtB u p = true) : t.LeAt u p := fun b hb => by
  simp only [leAtB, List.all_eq_true, List.contains_iff_mem] at h
  simpa using h b hb

/-- The transfer check for `r`, from the profile `t` to `u`. -/
def transferB (r : Rel) (t u : ProfileTable) : Bool := r.reads.all (u.leAtB t ·)

/-- **What `transferB` says**: whatever holds of every result `t` allows for
`r` holds of every result `u` allows. -/
theorem Rel.transfer_of_transferB {r : Rel} {t u : ProfileTable} (h : transferB r t u = true)
    {cat : Catalog} {out : Relation} (ho : r.AllowedP u cat out) : r.AllowedP t cat out :=
  Rel.AllowedP_transfer (fun p hp => ProfileTable.leAt_of_leAtB
    (List.all_eq_true.mp h p hp)) ho

/-! ## Functions an engine lacks -/

/-- The aggregates of a plan. -/
def Rel.aggFns : Rel → List AggFn
  | .read _ | .values _ _ => []
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _
  | .distinct r | .unnest r _ => r.aggFns
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ => a.aggFns ++ b.aggFns
  | .aggregate r _ ms => r.aggFns ++ ms.map (·.fn)

/-- The Substrait names of the functions a plan calls. -/
def Rel.functions (r : Rel) : List String :=
  ((r.ctors ++ r.aggFns.map Ctor.agg).filterMap rowOf |>.map (·.name)).eraseDups

/-- The functions of `r` that `t`'s engine has no expression for, with the facts. -/
def ProfileTable.missingIn (t : ProfileTable) (fns : List String) : List (String × List String) :=
  fns.filterMap fun f => (t.missing.lookup f).map (f, ·)

/-! ## The report, for Python -/

/-- The profiles a report compares. -/
def reportProfiles : List (ProfileTable × ObsTable) :=
  (Profile.reference.table, Profile.reference.obs) :: engineTables

open Lean (Json toJson) in
/-- `substrait-check --dependencies`: the options the plan meets, each with
every profile's choice and observation row; per pair of profiles whether a
proof under the first holds under the second (`transferB`); and per engine
the shims its translation from the reference needs for this plan. -/
def Rel.dependenciesJson (r : Rel) : Json :=
  let reads := r.reads.eraseDups
  let choiceAt (t : ProfileTable) (p : Read) : Json :=
    match t.choice? p.1 p.2.1 with | some c => c.json | none => Json.null
  let rowAt (obs : ObsTable) (p : Read) : Json :=
    match obs.row? p.1 p.2.1 with | some row => row.json | none => Json.null
  Json.mkObj [
    ("options", Json.arr <| (reads.map fun p => Json.mkObj ([
      ("group", toJson p.1), ("option", toJson p.2.1), ("preferences", toJson p.2.2),
      ("tool", toJson ((Profile.reference.tools.find? (·.option == p.2.1)).map fun t =>
        match t.tool with | .raise => "raise" | .choose => "choose" | .leaveOpen => "leave_open"))] ++
      reportProfiles.map fun (t, obs) => (t.name, Json.mkObj [
        ("choice", choiceAt t p), ("allows", toJson (t.allows p.1 p.2.1 p.2.2)),
        ("row", rowAt obs p)]))).toArray),
    ("transfer", Json.mkObj (reportProfiles.map fun (t, _) => (t.name,
      Json.mkObj (reportProfiles.map fun (u, _) => (u.name, toJson (transferB r t u)))))),
    ("functions", toJson r.functions),
    ("missing", Json.mkObj (engineTables.map fun (t, _) => (t.name,
      Json.arr <| ((t.missingIn r.functions).map fun (f, ids) =>
        Json.mkObj [("function", toJson f), ("facts", toJson ids)]).toArray))),
    -- A shim the plan needs at an option, unless every read there states a
    -- preference the engine gives as stated (a key's `NULLS LAST` on Polars):
    -- the shim is for the reference's default (#444, step 3b).
    ("shims", Json.mkObj (engineTables.map fun (t, obs) => (t.name,
      Json.arr <| ((reads.map fun p => (p.1, p.2.1)).eraseDups.filterMap fun (g, o) =>
        let stated := reads.filter fun p => p.1 == g && p.2.1 == o
        if stated.all (fun p => !p.2.2.isEmpty &&
            (t.allows g o p.2.2).all (Profile.reference.table.allows g o p.2.2).contains) then none
        else (obs.row? g o).bind fun row => row.shim.map fun sh =>
          Json.mkObj [("group", toJson g), ("option", toJson o), ("shim", toJson sh)]).toArray)))]

/-! ## The transfer check, on a dependency report -/

/-- The profiles by name: the reference, the core, and the engines (DuckDB under
its default settings). -/
def profileNamed (name : String) : Option (ProfileTable × ObsTable) :=
  ((Profile.reference.table, Profile.reference.obs) :: (Profile.core.table, []) :: engineTables).find?
    (·.1.name == name)

/-- What `t` allows at `group` (`none`: the row without a group) and `option`. -/
def ProfileTable.allowsAt (t : ProfileTable) (group : Option String) (option : String)
    (ps : List Behaviour) : List Behaviour :=
  match group with
  | some g => t.allows g option ps
  | none => match t.dflt? option, OptionSpec.find? option with
    | some c, some o => c.allows o.core ps
    | _, _ => []

def ObsTable.factsAt (obs : ObsTable) (group : Option String) (option : String) : List String :=
  let row := match group with
    | some g => obs.row? g option
    | none => (obs.find? fun (x : Option String × String × ObsRow) =>
        x.1.isNone && x.2.1 == option).map fun (x : Option String × String × ObsRow) => x.2.2
  match row with
  | some { evidence := .tested ids, .. } | some { evidence := .proved _ ids, .. } => ids
  | _ => []

open Lean (Json toJson) in
/-- `substrait-check --transfer`, on stdin `{"from": P, "to": E, "depends":
[{"group", "option", "preferences"?, "behaviours"?}], "functions"?: [...]}`:
whether a proof under `P` that uses only `depends` holds under `E`. Each row
fails where `E` allows a behaviour outside what the proof used (`behaviours`,
or else all `P` allows there), and each function `E` lacks fails. With
`depends` = `Rel.reads` and no `behaviours`, this is `transferB`, which
`Rel.transfer_of_transferB` proves sound. -/
def transferJson (input : Json) : Except String Json := do
  let name (k : String) : Except String (ProfileTable × ObsTable) := do
    let n ← input.getObjValAs? String k
    match profileNamed n with
    | some p => pure p
    | none => throw s!"unknown profile {n}"
  let (P, _) ← name "from"
  let (E, obsE) ← name "to"
  let rows := (input.getObjValAs? (Array Json) "depends").toOption.getD #[]
  let mut failures : Array Json := #[]
  for row in rows do
    let group := (row.getObjValAs? String "group").toOption
    let option ← row.getObjValAs? String "option"
    let ps := (row.getObjValAs? (List String) "preferences").toOption.getD []
    let used := (row.getObjValAs? (List String) "behaviours").toOption.getD (P.allowsAt group option ps)
    let target := E.allowsAt group option ps
    unless target.all used.contains do
      failures := failures.push (Json.mkObj [("group", toJson group), ("option", toJson option),
        ("from", toJson used), ("to", toJson target), ("facts", toJson (obsE.factsAt group option))])
  let fns := (input.getObjValAs? (List String) "functions").toOption.getD []
  for (f, ids) in E.missingIn fns do
    failures := failures.push (Json.mkObj [("function", toJson f), ("facts", toJson ids)])
  return Json.mkObj [("ok", toJson failures.isEmpty), ("failures", Json.arr failures)]

open Lean (Json toJson) in
/-- The dependency report of a contract's transformation: one row per group
and option it meets, with the reference's behaviours there. -/
def readsJson (reads : List Read) : Json :=
  let keys := (reads.map fun (g, o, _) => (g, o)).eraseDups
  Json.arr <| (keys.map fun (g, o) =>
    let here := reads.filter fun (g', o', _) => g' == g && o' == o
    let bs := here.flatMap fun (_, _, ps) => Profile.reference.table.allows g o ps
    -- Whether every read states its preference (a key's `NULLS FIRST`): an
    -- engine that gives a stated preference as stated needs no shim there.
    Json.mkObj [("group", toJson g), ("option", toJson o), ("behaviours", toJson bs.eraseDups),
      ("stated", toJson (here.all fun (_, _, ps) => !ps.isEmpty))]).toArray

/-- The dependency report of a contract's transformation, from `Rel.reads`. -/
def Rel.dependsJson (r : Rel) : Lean.Json := readsJson r.reads

end Substrait
