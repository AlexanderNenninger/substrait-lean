/-!
# Lists related element by element

`Forall2 R l l'`: `R` relates the lists' elements pairwise. It sits below
the evaluator's modules so that `Rel.OrderAllowed` (`OrderAllowed.lean`)
and the observations (`ObsEquiv.lean`) share it.
-/

namespace Substrait

/-- `R` relates the lists' elements pairwise. -/
inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {a : α} {b : β} {l : List α} {l' : List β} : R a b → Forall2 R l l' →
      Forall2 R (a :: l) (b :: l')

theorem forall₂_map_self {α β : Type} {R : α → β → Prop} {f : α → β} :
    ∀ l : List α, (∀ x ∈ l, R x (f x)) → Forall2 R l (l.map f)
  | [], _ => .nil
  | x :: l, h => .cons (h x (List.mem_cons_self ..))
      (forall₂_map_self l fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem eq_map_of_forall₂ {α β : Type} {f : α → β} :
    ∀ {l : List α} {l' : List β}, Forall2 (fun x y => y = f x) l l' → l' = l.map f
  | _, _, .nil => rfl
  | _, _, .cons h t => by rw [h, eq_map_of_forall₂ t]; rfl

namespace Forall2

variable {α β γ : Type}

theorem refl {R : α → α → Prop} : ∀ {l : List α}, (∀ a ∈ l, R a a) → Forall2 R l l
  | [], _ => .nil
  | _ :: _, h => .cons (h _ (List.mem_cons_self ..)) (refl fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem imp {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → Forall2 S l l'
  | _, _, .nil => .nil
  | _, _, .cons r t => .cons (h _ _ r) (imp h t)

theorem flip {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → Forall2 (fun b a => R a b) l' l
  | _, _, .nil => .nil
  | _, _, .cons r t => .cons r (flip t)

theorem trans {R : α → β → Prop} {S : β → γ → Prop} {T : α → γ → Prop}
    (h : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l : List α} {l' : List β} {l'' : List γ}, Forall2 R l l' → Forall2 S l' l'' → Forall2 T l l''
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons r t, .cons s u => .cons (h _ _ _ r s) (trans h t u)

theorem eq : ∀ {l l' : List α}, Forall2 (· = ·) l l' → l = l'
  | _, _, .nil => rfl
  | _, _, .cons rfl t => by rw [eq t]

/-- A permutation of one side carries over to the other. -/
theorem perm {R : α → β → Prop} {l₁ l₁' : List α} (p : l₁.Perm l₁') :
    ∀ {l₂ : List β}, Forall2 R l₁ l₂ → ∃ l₂', l₂.Perm l₂' ∧ Forall2 R l₁' l₂' := by
  induction p with
  | nil => intro l₂ h; cases h; exact ⟨[], .nil, .nil⟩
  | cons x _ ih =>
    intro l₂ h
    cases h with
    | cons r t =>
      obtain ⟨m, hm, hf⟩ := ih t
      exact ⟨_, hm.cons _, .cons r hf⟩
  | swap x y l =>
    intro l₂ h
    cases h with
    | cons r t =>
      cases t with
      | cons r' t' => exact ⟨_, .swap _ _ _, .cons r' (.cons r t')⟩
  | trans _ _ ih₁ ih₂ =>
    intro l₂ h
    obtain ⟨m₁, h₁, f₁⟩ := ih₁ h
    obtain ⟨m₂, h₂, f₂⟩ := ih₂ f₁
    exact ⟨m₂, h₁.trans h₂, f₂⟩

end Forall2


theorem Forall2.mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → ∀ {b : β}, b ∈ l' → ∃ a ∈ l, R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab t, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨a, ha, hr⟩ := Forall2.mem_right t h
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem Forall2.getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → ∀ i : Nat,
      (∃ a b, l[i]? = some a ∧ l'[i]? = some b ∧ R a b) ∨ (l[i]? = none ∧ l'[i]? = none)
  | _, _, .nil, _ => .inr ⟨rfl, rfl⟩
  | _, _, .cons hab _, 0 => .inl ⟨_, _, rfl, rfl, hab⟩
  | _, _, .cons _ t, i + 1 => by simpa using Forall2.getElem? t i

theorem Forall2.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → l.length = l'.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [Forall2.length_eq t]

theorem Forall2.weaken {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → Forall2 S l l'
  | _, _, .nil => .nil
  | _, _, .cons hab t => .cons (h _ _ hab) (Forall2.weaken h t)

end Substrait
