import SubstraitLean.TouchedGroups

/-!
# Touched frames: a window row depends only on the rows in its frame

`sverify._touched.Framed` maintains window aggregates over bounded RANGE
frames of one time column by recomputing only the output rows near a
batch's changes (#458, part of #294). This file proves it.

* `valueIn_narrow`: an aggregate (or `FIRST_VALUE`, `LAST_VALUE`,
  `NTH_VALUE`) over a RANGE frame of one ascending key `k`, with bounds in
  `[s, e]`, sees only the rows whose key lies in `[x + s, x + e]` (for a
  NULL key: the other NULLs), peers included.
* `outRow_local`: so the output row of `x` is the same for two inputs that
  hold `x` and the same rows of `x`'s partition in that span.
* `framed_sound`, `framed_batch`: for a change whose rows lie in the
  partitions `K` at times `[t0, t1]`, and `s ≤ 0 ≤ e`, the window after it
  is the old rows outside `[t0 - e, t1 - s]` (or outside `K`), and the rows
  inside from the window over the new input narrowed to `K` and the times
  `[t0 - e + s, t1 - s + e]`.

Like `windowEval_sharded`, it assumes no two input rows tie on the partition
and sort columns, so each input row has one output row (`windowEval_eq_map`).
-/

namespace Substrait
namespace TouchedFrames

/-- `v` lies `start` to `stop` after `u` (integers), or is `u` (anything else). -/
def spanVal (start stop : Int) : Value → Value → Bool
  | .int u, .int v => decide (u + start ≤ v ∧ v ≤ u + stop)
  | a, b => decide (a = b)

/-- `y`'s value of the key `k` lies in `x`'s span `[start, stop]`. -/
def inSpan (k : SortKey) (start stop : Int) (x y : Row) : Bool :=
  spanVal start stop (x.getD k.col .null) (y.getD k.col .null)

theorem sortLe_single (k : SortKey) (x y : Row) : sortLe [k] x y = k.le x y := by
  simp [sortLe, lexLe]

theorem mem_rows_bounds {fr : Frame} {k : SortKey} {a b : Int} {pb pa : List Row} {x y : Row}
    (hr : fr.range = true) (ha : fr.lo.offset = some a) (hb : fr.hi.offset = some b)
    (h : y ∈ fr.rows [k] pb x pa) :
    (if a = 0 then sortLe [k] x y else rangeFrom k a x y) = true ∧
      (if b = 0 then sortLe [k] y x else rangeTo k b x y) = true := by
  obtain ⟨range, lo, hi⟩ := fr
  simp only at hr ha hb
  subst hr
  simp only [Frame.rows, ↓reduceIte, List.mem_filter, Bool.and_eq_true] at h
  obtain ⟨-, hl, hh⟩ := h
  constructor
  · clear hh hb
    cases lo <;> simp only [FrameBound.offset, reduceCtorEq, Option.some.injEq] at ha <;>
      (simp only at hl; split at hl <;> simp_all [FrameBound.offset] <;> omega)
  · clear hl ha
    cases hi <;> simp only [FrameBound.offset, reduceCtorEq, Option.some.injEq] at hb <;>
      (simp only at hh; split at hh <;> simp_all [FrameBound.offset] <;> omega)

theorem bounds_span {k : SortKey} (hk : k.desc = false) {s e a b : Int} (hsa : s ≤ a)
    (hbe : b ≤ e) {x y : Row}
    (hl : (if a = 0 then sortLe [k] x y else rangeFrom k a x y) = true)
    (hh : (if b = 0 then sortLe [k] y x else rangeTo k b x y) = true) :
    inSpan k s e x y = true := by
  have hxy : sortLe [k] x y = true → sortLe [k] y x = true →
      x.getD k.col .null = y.getD k.col .null := fun h₁ h₂ => by
    simpa using sortLe_antisymm h₁ h₂
  have hrx : sortLe [k] x y = true → k.nullRank (x.getD k.col .null) ≤ k.nullRank (y.getD k.col .null) :=
    fun h => by
      rw [sortLe_single] at h
      simpa [natLe] using lexLe_left h
  have hry : sortLe [k] y x = true → k.nullRank (y.getD k.col .null) ≤ k.nullRank (x.getD k.col .null) :=
    fun h => by
      rw [sortLe_single] at h
      simpa [natLe] using lexLe_left h
  have hix : ∀ u v, x.getD k.col .null = .int u → y.getD k.col .null = .int v →
      sortLe [k] x y = true → u ≤ v := fun u v hu hv h => by
    rw [sortLe_single] at h
    simpa [hk] using SortKey.le_int h hu hv
  have hiy : ∀ u v, x.getD k.col .null = .int u → y.getD k.col .null = .int v →
      sortLe [k] y x = true → v ≤ u := fun u v hu hv h => by
    rw [sortLe_single] at h
    simpa [hk] using SortKey.le_int h hv hu
  unfold inSpan
  unfold rangeFrom at hl
  unfold rangeTo at hh
  generalize hu : x.getD k.col .null = u at *
  generalize hv : y.getD k.col .null = v at *
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp only [ha, hb, ↓reduceIte] at hl hh
  · have := hxy hl hh
    subst this
    cases u <;> simp [spanVal] <;> omega
  all_goals
    cases u <;> cases v <;> simp_all [spanVal, SortKey.nullRank] <;>
      (try (cases hn : k.nullsFirst <;> simp_all)) <;> omega

/-- An aggregate (or `FIRST_VALUE`, `LAST_VALUE`, `NTH_VALUE`) over a RANGE
frame of the key `k` whose bounds lie in `[start, stop]`. -/
def _root_.Substrait.WinFn.Framed (k : SortKey) (start stop : Int) : WinFn → Prop
  | .agg _ sort fr | .firstValue _ sort fr | .lastValue _ sort fr | .nthValue _ _ sort fr =>
    sort = [k] ∧ fr.range = true ∧ (∃ a, fr.lo.offset = some a ∧ start ≤ a) ∧
      ∃ b, fr.hi.offset = some b ∧ b ≤ stop
  | _ => False

theorem filter_filter_of {P W : Row → Bool} {l : List Row}
    (h : ∀ y ∈ l, P y = true → W y = true) : (l.filter W).filter P = l.filter P := by
  rw [List.filter_filter]
  exact List.filter_congr fun y hy => by
    cases hP : P y
    · simp
    · simp [h y hy hP]

theorem filter_mid {P W : Row → Bool} {pb pa : List Row} (x : Row)
    (h : ∀ y ∈ pb ++ pa, P y = true → W y = true) :
    (pb ++ x :: pa).filter P = (pb.filter W ++ x :: pa.filter W).filter P := by
  rw [List.filter_append, List.filter_append, List.filter_cons, List.filter_cons,
    filter_filter_of fun y hy => h y (List.mem_append_left _ hy),
    filter_filter_of fun y hy => h y (List.mem_append_right _ hy)]

/-- A RANGE frame's rows are those of its rows that pass any `W` true on them. -/
theorem rows_narrow {fr : Frame} {sort : List SortKey} {pb pa : List Row} {x : Row}
    (hr : fr.range = true) (W : Row → Bool) (hW : ∀ y, y ∈ fr.rows sort pb x pa → W y = true) :
    fr.rows sort pb x pa = fr.rows sort (pb.filter W) x (pa.filter W) := by
  unfold Frame.rows at hW ⊢
  simp only [hr, ↓reduceIte] at hW ⊢
  exact filter_mid x fun y hy hP => hW y (List.mem_filter.mpr ⟨by
    rcases List.mem_append.mp hy with h | h <;> simp [h], hP⟩)

/-- **A framed value depends only on the rows in its span.** -/
theorem valueIn_narrow {k : SortKey} (hk : k.desc = false) {s e : Int} {f : WinFn}
    (hf : f.Framed k s e) (pb : List Row) (x : Row) (pa : List Row) :
    f.valueIn pb x pa = f.valueIn (pb.filter (inSpan k s e x)) x (pa.filter (inSpan k s e x)) := by
  have key : ∀ fr : Frame, fr.range = true → (∃ a, fr.lo.offset = some a ∧ s ≤ a) →
      (∃ b, fr.hi.offset = some b ∧ b ≤ e) →
      fr.rows [k] pb x pa = fr.rows [k] (pb.filter (inSpan k s e x)) x (pa.filter (inSpan k s e x)) := by
    rintro fr hr ⟨a, ha, hsa⟩ ⟨b, hb, hbe⟩
    exact rows_narrow hr _ fun y hy =>
      bounds_span hk hsa hbe (mem_rows_bounds hr ha hb hy).1 (mem_rows_bounds hr ha hb hy).2
  cases f with
  | agg m sort fr | firstValue c sort fr | lastValue c sort fr | nthValue c n sort fr =>
    obtain ⟨rfl, hr, hlo, hhi⟩ := hf
    simp only [WinFn.valueIn, key fr hr hlo hhi]
  | _ => exact hf.elim

/-! ## A window row depends only on the rows in its span -/

section Local

variable {part : List Nat} {k : SortKey} {s e : Int} {fns : List WinFn}

/-- `y` is in `x`'s partition and its key lies in `x`'s span. -/
def near (part : List Nat) (k : SortKey) (s e : Int) (x y : Row) : Bool :=
  samePart part x y && inSpan k s e x y

/-- `x` and the rows near it. -/
def around (part : List Nat) (k : SortKey) (s e : Int) (x y : Row) : Bool :=
  decide (y = x) || near part k s e x y

theorem winRow_around (hk : k.desc = false) (hfns : ∀ f ∈ fns, f.Framed k s e) {S : List Row}
    (hS : S.Nodup) {x : Row} (hx : x ∈ S) :
    winRow part fns S x = winRow part fns (S.filter (around part k s e x)) x := by
  have hxP : x ∈ S.filter (samePart part x) := List.mem_filter.mpr ⟨hx, samePart_refl part x⟩
  obtain ⟨B, A, hBA⟩ := List.append_of_mem hxP
  have hnd : (S.filter (samePart part x)).Nodup := hS.filter _
  have hxB : x ∉ B := by
    rw [hBA] at hnd
    exact fun h => (List.nodup_append.mp hnd).2.2 x h x (by simp) rfl
  have hxB' : x ∉ B.filter (around part k s e x) := fun h => hxB (List.mem_filter.mp h).1
  have hG : (S.filter (around part k s e x)).filter (samePart part x) =
      B.filter (around part k s e x) ++ x :: A.filter (around part k s e x) := by
    have : (S.filter (around part k s e x)).filter (samePart part x) =
        (S.filter (samePart part x)).filter (around part k s e x) := by
      simp only [List.filter_filter, Bool.and_comm]
    rw [this, hBA, List.filter_append, List.filter_cons_of_pos (by simp [around])]
  simp only [winRow]
  rw [hBA, hG, splitAt_eq hxB, splitAt_eq hxB']
  congr 1
  refine List.map_congr_left fun f hf => ?_
  simp only [WinFn.value]
  rw [valueIn_narrow hk (hfns f hf), valueIn_narrow hk (hfns f hf)]
  have hxA : x ∉ A := by
    rw [hBA] at hnd
    exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have hne : ∀ y ∈ B ++ A, y ≠ x := fun y hy h => by
    subst h; rcases List.mem_append.mp hy with h | h
    · exact hxB h
    · exact hxA h
  congr 1 <;> simp only [List.filter_filter] <;> refine List.filter_congr fun y hy => ?_ <;>
    simp only [around, near, decide_eq_false (hne y (by simp [hy]))] <;>
    cases samePart part x y <;> cases inSpan k s e x y <;> simp

theorem keyOf_around {x w : Row} (h : around part k s e x w = true) :
    keyOf part w = keyOf part x := by
  simp only [around, near, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with rfl | ⟨h, -⟩
  · rfl
  · simp only [samePart, decide_eq_true_eq] at h
    exact h.symm

theorem keyOn_sorted {rows : Relation} {K : List Nat} (h : KeyOn K rows) (sort : List SortKey) :
    KeyOn K (rows.mergeSort (sortLe sort)) :=
  h.perm (List.mergeSort_perm rows _).symm fun h => Ne.symm h

/-- Two inputs with the same rows near `x` have the same rows around `x`,
in the same sorted order. -/
theorem sorted_around_eq {rows rows' : Relation} (hK : KeyOn (part ++ [k.col]) rows)
    (hK' : KeyOn (part ++ [k.col]) rows') {x : Row} (hx : x ∈ rows) (hx' : x ∈ rows')
    (hagree : ∀ y, near part k s e x y = true → (y ∈ rows ↔ y ∈ rows')) :
    (rows.mergeSort (sortLe [k])).filter (around part k s e x) =
      (rows'.mergeSort (sortLe [k])).filter (around part k s e x) := by
  have hTP := sortLe_totalPre [k]
  have hsorted : ∀ l : Relation, (l.mergeSort (sortLe [k])).Pairwise (sortLe [k] · · = true) :=
    fun l => List.pairwise_mergeSort hTP.trans hTP.total l
  have hKS := keyOn_sorted hK [k]
  have hKS' := keyOn_sorted hK' [k]
  apply eq_of_perm_of_pairwise
  · refine (List.perm_ext_iff_of_nodup (hKS.nodup.filter _) (hKS'.nodup.filter _)).mpr fun y => ?_
    simp only [List.mem_filter, List.mem_mergeSort]
    constructor <;> rintro ⟨hy, hg⟩ <;> refine ⟨?_, hg⟩ <;>
      simp only [around, Bool.or_eq_true, decide_eq_true_eq] at hg <;> rcases hg with rfl | hg
    · exact hx'
    · exact (hagree y hg).mp hy
    · exact hx
    · exact (hagree y hg).mpr hy
  · exact (hsorted _).filter _
  · exact (hsorted _).filter _
  · intro y hy z hz hyz hzy
    simp only [List.mem_filter] at hy hz
    apply KeyOn.eq_of_keyOf hKS hy.1 hz.1
    have h₁ := keyOf_around hy.2
    have h₂ := keyOf_around hz.2
    have h₃ := sortLe_antisymm hyz hzy
    simp only [keyOf, List.map_append, List.map_cons, List.map_nil] at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]

/-- The output row of the input row `x` in `windowEval part [k] fns rows`
(`windowEval_eq_map`). -/
def outRow (part : List Nat) (k : SortKey) (fns : List WinFn) (rows : Relation) (x : Row) : Row :=
  winRow part fns (rows.mergeSort (sortLe [k])) x

/-- With a key on the partition and sort columns, the window gives each input
row `x`, in sorted order, its output row `outRow … x`. -/
theorem windowEval_eq_map {rows : Relation} (hK : KeyOn (part ++ [k.col]) rows) :
    windowEval part [k] fns rows = (rows.mergeSort (sortLe [k])).map (outRow part k fns rows) :=
  windowRows_eq_map (keyOn_sorted hK [k]).nodup (List.nil_append _)

/-- **A window row depends only on the rows in its frame** (#458). Take
windows of one ascending sort key `k` whose functions are aggregates (or
`FIRST_VALUE`, …) over RANGE frames with bounds in `[s, e]`. The output row
of `x` is the same for two inputs that hold `x` and the same rows of `x`'s
partition whose key lies in `[x + s, x + e]` (for a NULL key: the other
NULLs), given a key on the partition and sort columns. -/
theorem outRow_local (hk : k.desc = false) (hfns : ∀ f ∈ fns, f.Framed k s e)
    {rows rows' : Relation} (hK : KeyOn (part ++ [k.col]) rows)
    (hK' : KeyOn (part ++ [k.col]) rows') {x : Row} (hx : x ∈ rows) (hx' : x ∈ rows')
    (hagree : ∀ y, near part k s e x y = true → (y ∈ rows ↔ y ∈ rows')) :
    outRow part k fns rows x = outRow part k fns rows' x := by
  unfold outRow
  rw [winRow_around hk hfns (keyOn_sorted hK [k]).nodup (List.mem_mergeSort.mpr hx),
    winRow_around hk hfns (keyOn_sorted hK' [k]).nodup (List.mem_mergeSort.mpr hx'),
    sorted_around_eq hK hK' hx hx' hagree]

end Local

/-! ## Touched frames

A batch whose changed rows have keys in `K` and times in `[t0, t1]` changes
the output rows of those partitions with times in `[t0 - e, t1 - s]`
(`inside`), and nothing else. These rows come out the same from the input
narrowed to the touched partitions and the times `[t0 - e + s, t1 - s + e]`
(`narrowed`). -/

section Batch

variable {part : List Nat} {k : SortKey} {s e : Int} {fns : List WinFn}
  {K : List Value → Bool} {t0 t1 : Int}

/-- The key `k` of `r` is an integer in `[lo, hi]`. -/
def timeIn (k : SortKey) (lo hi : Int) (r : Row) : Bool :=
  match r.getD k.col .null with
  | .int t => decide (lo ≤ t ∧ t ≤ hi)
  | _ => false

/-- A row the batch may insert or delete: in a touched partition, at a time in `[t0, t1]`. -/
def changed (part : List Nat) (k : SortKey) (K : List Value → Bool) (t0 t1 : Int) (r : Row) : Bool :=
  K (keyOf part r) && timeIn k t0 t1 r

/-- A row whose frame may hold a changed row: in a touched partition, at a
time in `[t0 - e, t1 - s]`. -/
def inside (part : List Nat) (k : SortKey) (K : List Value → Bool) (s e t0 t1 : Int) (r : Row) :
    Bool :=
  K (keyOf part r) && timeIn k (t0 - e) (t1 - s) r

/-- The input rows the recompute reads: in a touched partition, at a time in
`[t0 - e + s, t1 - s + e]`. -/
def narrowed (part : List Nat) (k : SortKey) (K : List Value → Bool) (s e t0 t1 : Int)
    (rows : Relation) : Relation :=
  rows.filter fun r => K (keyOf part r) && timeIn k (t0 - e + s) (t1 - s + e) r

theorem keyOf_near {x y : Row} (h : near part k s e x y = true) : keyOf part y = keyOf part x :=
  keyOf_around (k := k) (s := s) (e := e) (by simp [around, h])

/-- A changed row is in the frames of `inside` rows only. -/
theorem inside_of_near {x y : Row} (h : near part k s e x y = true)
    (hc : changed part k K t0 t1 y = true) : inside part k K s e t0 t1 x = true := by
  have hkey := keyOf_near h
  simp only [near, inSpan, Bool.and_eq_true] at h
  simp only [changed, inside, timeIn, Bool.and_eq_true, hkey] at hc ⊢
  refine ⟨hc.1, ?_⟩
  have h2 := h.2
  have h3 := hc.2
  generalize x.getD k.col .null = u at *
  generalize y.getD k.col .null = v at *
  cases u <;> cases v <;> simp_all [spanVal] <;> omega

theorem inside_of_changed (hs : s ≤ 0) (he : 0 ≤ e) {y : Row}
    (hc : changed part k K t0 t1 y = true) : inside part k K s e t0 t1 y = true := by
  simp only [changed, inside, timeIn, Bool.and_eq_true] at hc ⊢
  refine ⟨hc.1, ?_⟩
  have := hc.2
  generalize y.getD k.col .null = v at *
  cases v <;> simp_all <;> omega

theorem mem_narrowed (hs : s ≤ 0) (he : 0 ≤ e) {rows : Relation} {x y : Row}
    (hx : inside part k K s e t0 t1 x = true) (h : y = x ∨ near part k s e x y = true) :
    y ∈ narrowed part k K s e t0 t1 rows ↔ y ∈ rows := by
  simp only [narrowed, List.mem_filter, and_iff_left_iff_imp]
  intro _
  rcases h with rfl | h
  · simp only [inside, timeIn, Bool.and_eq_true] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have := hx.2
    generalize y.getD k.col .null = v at *
    cases v <;> simp_all <;> omega
  · have hkey := keyOf_near h
    simp only [near, inSpan, Bool.and_eq_true] at h
    simp only [inside, timeIn, Bool.and_eq_true, hkey] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have h2 := h.2
    have h3 := hx.2
    generalize x.getD k.col .null = u at *
    generalize y.getD k.col .null = v at *
    cases u <;> cases v <;> simp_all [spanVal] <;> omega

/-- `inside` reads columns of the input row, which the output row keeps. -/
theorem inside_append {x : Row} (l : Row) (hw : ∀ i ∈ k.col :: part, i < x.length) :
    inside part k K s e t0 t1 (x ++ l) = inside part k K s e t0 t1 x := by
  have hg : ∀ i ∈ k.col :: part, (x ++ l).getD i .null = x.getD i .null := fun i hi => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hw i hi)]
  have hkey : keyOf part (x ++ l) = keyOf part x :=
    List.map_congr_left fun i hi => hg i (List.mem_cons_of_mem _ hi)
  simp only [inside, timeIn, hkey, hg k.col (List.mem_cons_self ..)]

theorem inside_outRow {rows : Relation} {x : Row} (hw : ∀ i ∈ k.col :: part, i < x.length) :
    inside part k K s e t0 t1 (outRow part k fns rows x) = inside part k K s e t0 t1 x := by
  simp only [outRow, winRow]
  exact inside_append _ hw

theorem filter_map_outRow {rows : Relation} {l : List Row} (p : Bool → Bool)
    (hw : ∀ x ∈ l, ∀ i ∈ k.col :: part, i < x.length) :
    (l.map (outRow part k fns rows)).filter (fun o => p (inside part k K s e t0 t1 o)) =
      (l.filter fun x => p (inside part k K s e t0 t1 x)).map (outRow part k fns rows) := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun x hx => by simp [inside_outRow (fns := fns) (rows := rows) (hw x hx)]

theorem filter_map_outRow_inside {rows : Relation} {l : List Row}
    (hw : ∀ x ∈ l, ∀ i ∈ k.col :: part, i < x.length) :
    (l.map (outRow part k fns rows)).filter (inside part k K s e t0 t1) =
      (l.filter (inside part k K s e t0 t1)).map (outRow part k fns rows) := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun x hx => by simp [inside_outRow (fns := fns) (rows := rows) (hw x hx)]

/-- **Touched frames are sound** (#458, `sverify._touched.Framed`). Take a
window of one ascending sort key `k` whose functions are aggregates (or
`FIRST_VALUE`, …) over RANGE frames with bounds in `[s, e]`, `s ≤ 0 ≤ e`,
and a key on the partition and sort columns before and after a change. If
every row the change inserts or deletes is `changed` (in a partition of `K`,
at a time in `[t0, t1]`), the window after the change is the old window's
rows that are not `inside` (in `K`, at a time in `[t0 - e, t1 - s]`), and the
`inside` rows of the window over the `narrowed` new input (in `K`, at a time
in `[t0 - e + s, t1 - s + e]`). -/
theorem framed_sound (hk : k.desc = false) (hs : s ≤ 0) (he : 0 ≤ e)
    (hfns : ∀ f ∈ fns, f.Framed k s e) {rows rows' : Relation}
    (hK : KeyOn (part ++ [k.col]) rows) (hK' : KeyOn (part ++ [k.col]) rows')
    (hw : ∀ r ∈ rows ++ rows', ∀ i ∈ k.col :: part, i < r.length)
    (hch : ∀ y, (y ∈ rows ↔ y ∈ rows') ∨ changed part k K t0 t1 y = true) :
    (windowEval part [k] fns rows').Perm
      ((windowEval part [k] fns rows).filter (fun o => !inside part k K s e t0 t1 o) ++
        (windowEval part [k] fns (narrowed part k K s e t0 t1 rows')).filter
          (inside part k K s e t0 t1)) := by
  let ins := inside part k K s e t0 t1
  let N := narrowed part k K s e t0 t1 rows'
  have hKN : KeyOn (part ++ [k.col]) N := hK'.sublist List.filter_sublist
  have hw₁ : ∀ x ∈ rows.mergeSort (sortLe [k]), ∀ i ∈ k.col :: part, i < x.length :=
    fun x hx => hw x (List.mem_append_left _ (List.mem_mergeSort.mp hx))
  have hw₂ : ∀ x ∈ rows'.mergeSort (sortLe [k]), ∀ i ∈ k.col :: part, i < x.length :=
    fun x hx => hw x (List.mem_append_right _ (List.mem_mergeSort.mp hx))
  have hw₃ : ∀ x ∈ N.mergeSort (sortLe [k]), ∀ i ∈ k.col :: part, i < x.length :=
    fun x hx => hw x (List.mem_append_right _ (List.mem_filter.mp (List.mem_mergeSort.mp hx)).1)
  -- The new window splits into the rows outside and inside.
  have hsplit : ∀ l : List Row, l.Perm (l.filter (fun o => !ins o) ++ l.filter ins) := fun l => by
    simpa using (List.filter_append_perm (fun o => !ins o) l).symm
  refine (hsplit _).trans (List.Perm.append ?_ ?_)
  · -- Outside: the old rows, unchanged.
    rw [windowEval_eq_map hK', windowEval_eq_map hK,
      filter_map_outRow (fun b => !b) hw₂, filter_map_outRow (fun b => !b) hw₁]
    have hout : ∀ x, ins x = false → (x ∈ rows ↔ x ∈ rows') := fun x hx =>
      (hch x).resolve_right fun hc => by simp [ins, inside_of_changed hs he hc] at hx
    have heq : ∀ x ∈ (rows'.mergeSort (sortLe [k])).filter (fun x => !ins x),
        outRow part k fns rows' x = outRow part k fns rows x := fun x hx => by
      simp only [List.mem_filter, List.mem_mergeSort, Bool.not_eq_true'] at hx
      refine (outRow_local hk hfns hK hK' ((hout x hx.2).mpr hx.1) hx.1 fun y hy => ?_).symm
      exact (hch y).resolve_right fun hc => by
        simp [ins, inside_of_near hy hc] at hx
    rw [List.map_congr_left heq]
    refine List.Perm.map _ ((List.perm_ext_iff_of_nodup
      ((keyOn_sorted hK' [k]).nodup.filter _) ((keyOn_sorted hK [k]).nodup.filter _)).mpr
        fun y => ?_)
    simp only [List.mem_filter, List.mem_mergeSort, Bool.not_eq_true']
    constructor <;> rintro ⟨hy, h⟩ <;> exact ⟨by simpa [hout y h] using hy, h⟩
  · -- Inside: the window over the narrowed input.
    rw [windowEval_eq_map hK', windowEval_eq_map hKN,
      filter_map_outRow_inside hw₂, filter_map_outRow_inside hw₃]
    have heq : ∀ x ∈ (rows'.mergeSort (sortLe [k])).filter ins,
        outRow part k fns rows' x = outRow part k fns N x := fun x hx => by
      simp only [List.mem_filter, List.mem_mergeSort] at hx
      exact outRow_local hk hfns hK' hKN hx.1 ((mem_narrowed hs he hx.2 (.inl rfl)).mpr hx.1)
        fun y hy => (mem_narrowed hs he hx.2 (.inr hy)).symm
    rw [List.map_congr_left heq]
    refine List.Perm.map _ ((List.perm_ext_iff_of_nodup
      ((keyOn_sorted hK' [k]).nodup.filter _) ((keyOn_sorted hKN [k]).nodup.filter _)).mpr
        fun y => ?_)
    simp only [List.mem_filter, List.mem_mergeSort]
    constructor <;> rintro ⟨hy, h⟩
    · exact ⟨(mem_narrowed hs he h (.inl rfl)).mpr hy, h⟩
    · exact ⟨(mem_narrowed hs he h (.inl rfl)).mp hy, h⟩

theorem mem_foldl_erase {y : Row} : ∀ {dels rows : Relation},
    y ∈ dels.foldl List.erase rows → y ∈ rows
  | [], _, h => h
  | _ :: _, _, h => List.mem_of_mem_erase (mem_foldl_erase h)

theorem mem_foldl_erase_iff {y : Row} : ∀ {dels rows : Relation}, y ∉ dels →
    (y ∈ dels.foldl List.erase rows ↔ y ∈ rows)
  | [], _, _ => .rfl
  | d :: _, _, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    rw [mem_foldl_erase_iff h.2, List.mem_erase_of_ne h.1]

/-- `framed_sound` for a batch that deletes `dels` and inserts `ins`, all of
them `changed`, as `TouchedGroups.touched_window_sound` states it for
touched partitions. -/
theorem framed_batch (hk : k.desc = false) (hs : s ≤ 0) (he : 0 ≤ e)
    (hfns : ∀ f ∈ fns, f.Framed k s e) {rows dels ins : Relation}
    (hc : ∀ r ∈ dels ++ ins, changed part k K t0 t1 r = true)
    (hK : KeyOn (part ++ [k.col]) rows)
    (hK' : KeyOn (part ++ [k.col]) (Retention.applyBatch rows dels ins))
    (hw : ∀ r ∈ rows ++ ins, ∀ i ∈ k.col :: part, i < r.length) :
    (windowEval part [k] fns (Retention.applyBatch rows dels ins)).Perm
      ((windowEval part [k] fns rows).filter (fun o => !inside part k K s e t0 t1 o) ++
        (windowEval part [k] fns
          (narrowed part k K s e t0 t1 (Retention.applyBatch rows dels ins))).filter
          (inside part k K s e t0 t1)) := by
  refine framed_sound hk hs he hfns hK hK' (fun r hr => ?_) fun y => ?_
  · simp only [Retention.applyBatch, List.mem_append] at hr
    rcases hr with hr | (hr | hr)
    · exact hw r (List.mem_append_left _ hr)
    · exact hw r (List.mem_append_left _ (mem_foldl_erase hr))
    · exact hw r (List.mem_append_right _ hr)
  · cases hy : changed part k K t0 t1 y
    · left
      have hd : y ∉ dels := fun h => by simp [hc y (List.mem_append_left _ h)] at hy
      have hi : y ∉ ins := fun h => by simp [hc y (List.mem_append_right _ h)] at hy
      simp only [Retention.applyBatch, List.mem_append, mem_foldl_erase_iff hd]
      simp [hi]
    · exact .inr rfl

end Batch

end TouchedFrames
end Substrait
