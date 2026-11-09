/-!
# Distinct elements

`dedup` keeps the first occurrence of every element, in order: `DISTINCT`'s
rows and an aggregate's groups. Every lemma about it lives here.
-/

namespace Substrait

/-- The first occurrence of every element, in order (`n` bounds the length). -/
def dedupN {α : Type} [DecidableEq α] : Nat → List α → List α
  | 0, _ | _, [] => []
  | n + 1, x :: xs => x :: dedupN n (xs.filter (· != x))

def dedup {α : Type} [DecidableEq α] (l : List α) : List α := dedupN l.length l

section

variable {α : Type} [DecidableEq α]

/-- Any fuel of at least the length gives `dedup`. -/
theorem dedupN_eq_dedup : ∀ (n : Nat) (l : List α), l.length ≤ n → dedupN n l = dedup l
  | _, [], _ => by cases ‹Nat› <;> simp [dedupN, dedup]
  | 0, _ :: _, h => by simp at h
  | n + 1, x :: xs, h => by
    have hf : (xs.filter (· != x)).length ≤ n := by
      have := List.length_filter_le (· != x) xs; simp at h; omega
    have hf' : (xs.filter (· != x)).length ≤ xs.length := List.length_filter_le _ _
    simp only [dedup, dedupN, List.length_cons]
    rw [dedupN_eq_dedup n _ hf, dedupN_eq_dedup xs.length _ hf']

theorem dedup_nil : dedup ([] : List α) = [] := by simp [dedup, dedupN]

theorem dedup_cons (x : α) (xs : List α) : dedup (x :: xs) = x :: dedup (xs.filter (· != x)) := by
  conv => lhs; unfold dedup
  simp only [List.length_cons, dedupN]
  rw [dedupN_eq_dedup _ _ (List.length_filter_le _ _)]

theorem dedupN_spec : ∀ (n : Nat) (l : List α), l.length ≤ n →
    (∀ y, y ∈ dedupN n l ↔ y ∈ l) ∧ (dedupN n l).Sublist l ∧ (dedupN n l).Pairwise (· ≠ ·)
  | _, [], _ => by cases ‹Nat› <;> simp [dedupN]
  | 0, _ :: _, h => by simp at h
  | n + 1, x :: xs, h => by
    have hf : (xs.filter (· != x)).length ≤ n := by
      have := List.length_filter_le (· != x) xs; simp at h; omega
    obtain ⟨hm, hs, hp⟩ := dedupN_spec n _ hf
    simp only [dedupN]
    refine ⟨fun y => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, hm, List.mem_filter, bne_iff_ne, ne_eq]
      by_cases hy : y = x <;> simp [hy]
    · exact (hs.trans List.filter_sublist).cons_cons x
    · refine List.Pairwise.cons (fun y hy => ?_) hp
      have := (hm y).mp hy
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at this
      exact fun h => this.2 h.symm

theorem mem_dedup {l : List α} {y : α} : y ∈ dedup l ↔ y ∈ l :=
  (dedupN_spec _ l (Nat.le_refl _)).1 y

theorem dedup_sublist (l : List α) : (dedup l).Sublist l :=
  (dedupN_spec _ l (Nat.le_refl _)).2.1

theorem dedup_length_le (l : List α) : (dedup l).length ≤ l.length := (dedup_sublist l).length_le

theorem dedup_pairwise (l : List α) : (dedup l).Pairwise (· ≠ ·) :=
  (dedupN_spec _ l (Nat.le_refl _)).2.2

theorem nodup_dedup (l : List α) : (dedup l).Nodup := List.nodup_iff_pairwise_ne.mpr (dedup_pairwise l)

theorem dedup_of_nodup : ∀ {l : List α}, l.Nodup → dedup l = l
  | [], _ => dedup_nil
  | x :: xs, h => by
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp h
    have hf : xs.filter (· != x) = xs :=
      List.filter_eq_self.2 fun y hy => by simpa using fun h : y = x => hx (h ▸ hy)
    rw [dedup_cons, hf, dedup_of_nodup hxs]

/-- Lists with the same elements have `dedup`s that are permutations. -/
theorem dedup_perm_of_mem {l l' : List α} (h : ∀ y, y ∈ l ↔ y ∈ l') : (dedup l).Perm (dedup l') :=
  (List.perm_ext_iff_of_nodup (nodup_dedup l) (nodup_dedup l')).mpr fun y => by
    rw [mem_dedup, mem_dedup]; exact h y

theorem dedup_append_disjoint {A B : List α} (h : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) :
    (dedup (A ++ B)).Perm (dedup A ++ dedup B) :=
  (List.perm_ext_iff_of_nodup (nodup_dedup _)
    (List.nodup_append.mpr ⟨nodup_dedup _, nodup_dedup _,
      fun a ha b hb => h a (mem_dedup.mp ha) b (mem_dedup.mp hb)⟩)).mpr fun y => by
    simp only [mem_dedup, List.mem_append]

/-- `DISTINCT` of parts with no row in common: the parts' `DISTINCT`s. -/
theorem dedup_flatten_disjoint :
    ∀ {L : List (List α)}, L.Pairwise (fun A B => ∀ a ∈ A, ∀ b ∈ B, a ≠ b) →
      (dedup L.flatten).Perm (L.map dedup).flatten
  | [], _ => by simp [dedup_nil]
  | A :: L, h => by
    rw [List.pairwise_cons] at h
    simp only [List.flatten_cons, List.map_cons]
    refine (dedup_append_disjoint fun a ha b hb => ?_).trans
      (List.Perm.append_left _ (dedup_flatten_disjoint h.2))
    obtain ⟨B, hB, hb⟩ := List.mem_flatten.mp hb
    exact h.1 B hB a ha b hb

theorem dedup_filter_perm (p : α → Bool) (l : List α) :
    (dedup (l.filter p)).Perm ((dedup l).filter p) :=
  (List.perm_ext_iff_of_nodup (nodup_dedup _) ((nodup_dedup l).filter p)).mpr fun y => by
    simp only [mem_dedup, List.mem_filter]

end

section

variable {α β : Type} [DecidableEq β]

/-- Maps that tell the same elements apart keep the same elements. -/
theorem dedup_parallel {f g : α → β} {l : List α}
    (he : ∀ x ∈ l, ∀ y ∈ l, f x = f y ↔ g x = g y) :
    ∃ L : List α, (∀ x ∈ L, x ∈ l) ∧ dedup (l.map f) = L.map f ∧ dedup (l.map g) = L.map g :=
  go l.length l (Nat.le_refl _) he
where
  go : ∀ (n : Nat) (l : List α), l.length ≤ n → (∀ x ∈ l, ∀ y ∈ l, f x = f y ↔ g x = g y) →
      ∃ L : List α, (∀ x ∈ L, x ∈ l) ∧ dedup (l.map f) = L.map f ∧ dedup (l.map g) = L.map g
  | _, [], _, _ => ⟨[], by simp [dedup_nil]⟩
  | 0, _ :: _, h, _ => by simp at h
  | n + 1, x :: xs, hl, he => by
    have hfg : xs.filter ((· != f x) ∘ f) = xs.filter ((· != g x) ∘ g) :=
      List.filter_congr fun y hy => by
        rw [Bool.eq_iff_iff]
        simp only [Function.comp_apply, bne_iff_ne, ne_eq]
        exact not_congr (he y (by simp [hy]) x (by simp))
    have hlen : (xs.filter ((· != f x) ∘ f)).length ≤ n := by
      have := List.length_filter_le ((· != f x) ∘ f) xs; simp at hl; omega
    obtain ⟨L, hL, hf, hg⟩ := go n _ hlen fun y hy z hz =>
      he y (by simp [(List.mem_filter.mp hy).1]) z (by simp [(List.mem_filter.mp hz).1])
    refine ⟨x :: L, fun y hy => ?_, ?_, ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_filter.mp (hL y hy)).1
    · simp only [List.map_cons, dedup_cons, List.filter_map, hf]
    · simp only [List.map_cons, dedup_cons, List.filter_map, ← hfg, hg]

/-- Filtering by a predicate of the images commutes with `dedup`. -/
theorem dedup_filter_map {f : α → β} {p : α → Bool} {q : β → Bool} :
    ∀ (n : Nat) (l : List α), l.length ≤ n → (∀ x ∈ l, p x = q (f x)) →
      dedup ((l.filter p).map f) = (dedup (l.map f)).filter q
  | _, [], _, _ => by simp [dedup_nil]
  | 0, _ :: _, h, _ => by simp at h
  | n + 1, x :: xs, hl, hpq => by
    have hlen : (xs.filter ((· != f x) ∘ f)).length ≤ n := by
      have := List.length_filter_le ((· != f x) ∘ f) xs; simp at hl; omega
    have ih := dedup_filter_map n _ hlen fun y hy => hpq y (List.mem_cons_of_mem _ (List.mem_filter.mp hy).1)
    rw [List.map_cons, dedup_cons, List.filter_map]
    by_cases hp : p x
    · have hq : q (f x) = true := by rw [← hpq x (by simp)]; exact hp
      rw [List.filter_cons_of_pos hp, List.map_cons, dedup_cons, List.filter_cons_of_pos hq,
        List.filter_map, ← ih, List.filter_filter, List.filter_filter]
      congr 3
      exact List.filter_congr fun y _ => by simp [Bool.and_comm]
    · have hq : q (f x) = false := by rw [← hpq x (by simp)]; simpa using hp
      rw [List.filter_cons_of_neg hp, List.filter_cons_of_neg (by simp [hq]), ← ih, List.filter_filter]
      congr 2
      refine List.filter_congr fun y hy => ?_
      by_cases hpy : p y
      · have hne : f y ≠ f x := fun he => by
          have h1 := hpq y (by simp [hy]); have h2 := hpq x (by simp)
          rw [he] at h1; simp_all
        simp [hpy, hne]
      · simp [hpy]

end


/-! ## Classes and their representatives

`DISTINCT`, `GROUP BY` and `COUNT(DISTINCT)` tell values apart up to a
canonical form `c` (`Value.canonV`: `-0.0` is `0.0`, D31). The deterministic
eval keeps one member of each class, the least in a total order `le` on raw
values, so the member depends only on which values occur and not on their
order; the reference leaves it open (`Rel.Allowed`). -/

section

variable {α : Type}

/-- What `classRep` needs of `le`: a total order. -/
structure RawOrder (le : α → α → Bool) : Prop where
  total : ∀ a b, le a b = true ∨ le b a = true
  trans : ∀ a b c, le a b = true → le b c = true → le a c = true
  antisymm : ∀ a b, le a b = true → le b a = true → a = b

/-- The least of `x` and the members of `l` with `x`'s canonical form. -/
def classRep [DecidableEq α] (c : α → α) (le : α → α → Bool) (l : List α) (x : α) : α :=
  (l.filter (c · == c x)).foldl (fun a b => if le a b then a else b) x

/-- One member of each class of `l`, in the order of first occurrence. -/
def canonReps [DecidableEq α] (c : α → α) (le : α → α → Bool) (l : List α) : List α :=
  dedup (l.map (classRep c le l))

theorem foldlMin_mem (le : α → α → Bool) : ∀ (x : α) (l : List α),
    l.foldl (fun a b => if le a b then a else b) x ∈ x :: l
  | x, [] => List.mem_cons_self
  | x, y :: l => by
    have ih := foldlMin_mem le (if le x y then x else y) l
    simp only [List.foldl_cons] at ih ⊢
    rcases List.mem_cons.mp ih with h | h
    · rw [h]; cases le x y <;> simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem foldlMin_le {le : α → α → Bool} (h : RawOrder le) : ∀ (x : α) (l : List α),
    ∀ y ∈ x :: l, le (l.foldl (fun a b => if le a b then a else b) x) y = true
  | x, [], y, hy => by
    rw [List.mem_singleton.mp hy]; exact (h.total x x).elim id id
  | x, z :: l, y, hy => by
    have ih := foldlMin_le h (if le x z then x else z) l
    simp only [List.foldl_cons] at ih ⊢
    have hrefl : ∀ a, le a a = true := fun a => (h.total a a).elim id id
    have hm := ih _ List.mem_cons_self
    have hx : le (if le x z then x else z) x = true := by
      cases hxz : le x z
      · exact (h.total x z).resolve_left (by simp [hxz])
      · exact hrefl x
    have hz : le (if le x z then x else z) z = true := by
      cases hxz : le x z
      · exact hrefl z
      · exact hxz
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · exact h.trans _ _ _ hm hx
    · exact h.trans _ _ _ hm hz
    · exact ih y (List.mem_cons_of_mem _ hy)

variable [DecidableEq α] {c : α → α} {le : α → α → Bool}

theorem classRep_mem' (l : List α) (x : α) : classRep c le l x ∈ x :: l.filter (c · == c x) :=
  foldlMin_mem le x _

theorem classRep_mem {l : List α} {x : α} (hx : x ∈ l) : classRep c le l x ∈ l := by
  rcases List.mem_cons.mp (classRep_mem' (c := c) (le := le) l x) with h | h
  · rw [h]; exact hx
  · exact (List.mem_filter.mp h).1

theorem classRep_canon (l : List α) (x : α) : c (classRep c le l x) = c x := by
  rcases List.mem_cons.mp (classRep_mem' (c := c) (le := le) l x) with h | h
  · rw [h]
  · simpa using (List.mem_filter.mp h).2

theorem classRep_least (h : RawOrder le) {l : List α} {x y : α} (hy : y ∈ l) (hc : c y = c x) :
    le (classRep c le l x) y = true :=
  foldlMin_le h x _ y (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hy, by simp [hc]⟩))

/-- Members of one class have one representative. -/
theorem classRep_eq (h : RawOrder le) {l : List α} {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hc : c x = c y) : classRep c le l x = classRep c le l y :=
  h.antisymm _ _
    (classRep_least h (classRep_mem hy) (by rw [classRep_canon (c := c), hc]))
    (classRep_least h (classRep_mem hx) (by rw [classRep_canon (c := c), hc]))

theorem classRep_self {l : List α} {x : α} (hx : x ∈ l)
    (hinj : ∀ y ∈ l, c y = c x → y = x) : classRep c le l x = x := by
  have hm := classRep_mem (c := c) (le := le) hx
  exact hinj _ hm (classRep_canon l x)

/-- The representative depends only on which members occur. -/
theorem classRep_perm (h : RawOrder le) {l l' : List α} (hp : l.Perm l') {x : α} (hx : x ∈ l) :
    classRep c le l x = classRep c le l' x :=
  h.antisymm _ _
    (classRep_least h (hp.mem_iff.mpr (classRep_mem (hp.mem_iff.mp hx))) (classRep_canon _ _))
    (classRep_least h (hp.mem_iff.mp (classRep_mem hx)) (classRep_canon _ _))

theorem mem_canonReps {l : List α} {k : α} :
    k ∈ canonReps c le l ↔ ∃ x ∈ l, classRep c le l x = k := by
  simp only [canonReps, mem_dedup, List.mem_map]

theorem canonReps_sub {l : List α} {k : α} (hk : k ∈ canonReps c le l) : k ∈ l := by
  obtain ⟨x, hx, rfl⟩ := mem_canonReps.mp hk; exact classRep_mem hx

theorem canonReps_canon {l : List α} {k : α} (hk : k ∈ canonReps c le l) : ∃ x ∈ l, c k = c x := by
  obtain ⟨x, hx, rfl⟩ := mem_canonReps.mp hk; exact ⟨x, hx, classRep_canon _ _⟩

/-- Every member has its class's representative among the representatives. -/
theorem classRep_mem_canonReps {l : List α} {x : α} (hx : x ∈ l) :
    classRep c le l x ∈ canonReps c le l :=
  mem_canonReps.mpr ⟨x, hx, rfl⟩

/-- The representatives lie in different classes. -/
theorem canonReps_pairwise (h : RawOrder le) (l : List α) :
    (canonReps c le l).Pairwise fun a b => c a ≠ c b := by
  refine (dedup_pairwise _).imp_of_mem fun {a b} ha hb hne hc => hne ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_dedup.mp ha)
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (mem_dedup.mp hb)
  rw [classRep_canon (c := c), classRep_canon (c := c)] at hc
  exact classRep_eq h hx hy hc

theorem canonReps_length_le (l : List α) : (canonReps c le l).length ≤ l.length := by
  simpa [canonReps] using dedup_length_le (l.map (classRep c le l))

theorem canonReps_nodup (l : List α) : (canonReps c le l).Nodup := nodup_dedup _

theorem canonReps_perm (h : RawOrder le) {l l' : List α} (hp : l.Perm l') :
    (canonReps c le l).Perm (canonReps c le l') :=
  dedup_perm_of_mem fun k => by
    simp only [List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hp.mem_iff.mp hx, (classRep_perm h hp hx).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hp.mem_iff.mpr hx, classRep_perm h hp (hp.mem_iff.mpr hx)⟩

/-- A member's class lies in the part it comes from when no member of the
other part shares its canonical form. -/
theorem classRep_append_left {A B : List α} {x : α} (h : ∀ b ∈ B, c b ≠ c x) :
    classRep c le (A ++ B) x = classRep c le A x := by
  unfold classRep
  rw [List.filter_append, List.filter_eq_nil_iff.mpr fun b hb hc => h b hb (by simpa using hc),
    List.append_nil]

theorem classRep_append_right {A B : List α} {x : α} (h : ∀ a ∈ A, c a ≠ c x) :
    classRep c le (A ++ B) x = classRep c le B x := by
  unfold classRep
  rw [List.filter_append, List.filter_eq_nil_iff.mpr fun a ha hc => h a ha (by simpa using hc),
    List.nil_append]

/-- `canonReps` of parts with no class in common: the parts' `canonReps`. -/
theorem canonReps_append_disjoint {A B : List α} (h : ∀ a ∈ A, ∀ b ∈ B, c a ≠ c b) :
    (canonReps c le (A ++ B)).Perm (canonReps c le A ++ canonReps c le B) := by
  refine (List.perm_ext_iff_of_nodup (canonReps_nodup _)
    (List.nodup_append.mpr ⟨canonReps_nodup _, canonReps_nodup _, fun a ha b hb he => ?_⟩)).mpr
    fun k => ?_
  · obtain ⟨x, hx, rfl⟩ := mem_canonReps.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_canonReps.mp hb
    have := congrArg c he
    rw [classRep_canon (c := c), classRep_canon (c := c)] at this
    exact h x hx y hy this
  · simp only [List.mem_append, mem_canonReps, List.mem_append]
    constructor
    · rintro ⟨x, hx | hx, rfl⟩
      · exact .inl ⟨x, hx, (classRep_append_left fun b hb => (h x hx b hb).symm).symm⟩
      · exact .inr ⟨x, hx, (classRep_append_right fun a ha => h a ha x hx).symm⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨x, .inl hx, classRep_append_left fun b hb => (h x hx b hb).symm⟩
      · exact ⟨x, .inr hx, classRep_append_right fun a ha => h a ha x hx⟩

/-- `canonReps` of parts with no class in common: the parts' `canonReps`. -/
theorem canonReps_flatten_disjoint :
    ∀ {L : List (List α)}, L.Pairwise (fun A B => ∀ a ∈ A, ∀ b ∈ B, c a ≠ c b) →
      (canonReps c le L.flatten).Perm (L.map (canonReps c le)).flatten
  | [], _ => by simp [canonReps, dedup_nil]
  | A :: L, h => by
    rw [List.pairwise_cons] at h
    simp only [List.flatten_cons, List.map_cons]
    refine (canonReps_append_disjoint fun a ha b hb => ?_).trans
      (List.Perm.append_left _ (canonReps_flatten_disjoint h.2))
    obtain ⟨B, hB, hb⟩ := List.mem_flatten.mp hb
    exact h.1 B hB a ha b hb

/-- Without two members of one class, the representatives are `dedup`'s. -/
theorem canonReps_of_inj {l : List α} (hinj : ∀ x ∈ l, ∀ y ∈ l, c x = c y → x = y) :
    canonReps c le l = dedup l := by
  unfold canonReps
  have : l.map (classRep c le l) = l.map id :=
    List.map_congr_left fun x hx => classRep_self hx fun y hy hc => hinj y hy x hx hc
  rw [this, List.map_id]

end

end Substrait
