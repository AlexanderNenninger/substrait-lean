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

end Substrait
