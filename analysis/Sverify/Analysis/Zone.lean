/-!
# Zones: difference-bound matrices (#959)

A zone over the nodes `0 … n` bounds differences: the entry `(i, j)` is
`some c` for `v j - v i ≤ c` and `none` for no bound (Dill 1989, Miné 2001).
Node `0` is the zero, so the entries `(0, j)` and `(j, 0)` are a column's upper
bound and its negated lower bound.

This module is the domain on its own, over integer valuations `v : Nat → Int`:

* `Zone.close` tightens every entry by the paths through each node
  (Floyd-Warshall), and keeps the valuations a zone admits (`Zone.close_sat`).
* `Zone.add` adds one constraint and closes (`Zone.add_sat`).
* `Zone.empty?` finds a negative cycle after closing; then no valuation is
  admitted (`Zone.empty?_sound`).

Reading the analysis's `Fact.diff` into a zone, and a zone's rows (NULLs
included), come after it (#959's checklist, items 2 to 4).
-/

namespace Substrait

/-- A bound, or none (`+∞`) where there is no bound. -/
abbrev Bnd := Option Int

/-- The smaller bound; no bound is the largest. -/
def Bnd.min : Bnd → Bnd → Bnd
  | none, b => b
  | a, none => a
  | some a, some b => some (Min.min a b)

/-- The sum of two bounds, along a path; none if either is none. -/
def Bnd.add : Bnd → Bnd → Bnd
  | some a, some b => some (a + b)
  | _, _ => none

theorem Bnd.min_eq_some {a b : Bnd} {c : Int} (h : Bnd.min a b = some c) :
    a = some c ∨ b = some c := by
  cases a <;> cases b <;> simp_all [Bnd.min]
  omega

theorem Bnd.min_le_left {a b : Bnd} {x : Int} (h : a = some x) :
    ∃ c, Bnd.min a b = some c ∧ c ≤ x := by
  subst h; cases b <;> simp [Bnd.min]; omega

theorem Bnd.min_le_right {a b : Bnd} {x : Int} (h : b = some x) :
    ∃ c, Bnd.min a b = some c ∧ c ≤ x := by
  subst h; cases a <;> simp [Bnd.min]; omega

theorem Bnd.add_eq_some {a b : Bnd} {c : Int} (h : Bnd.add a b = some c) :
    ∃ x y, a = some x ∧ b = some y ∧ c = x + y := by
  cases a <;> cases b <;> simp_all [Bnd.add]

/-- A zone over the nodes `0 … n`: `m[i][j]` bounds `v j - v i`. Entries
outside the nodes are read as none (`Zone.get`). -/
structure Zone where
  n : Nat
  m : Array (Array Bnd)
  deriving Repr, Inhabited

namespace Zone

/-- The entry `(i, j)`. -/
def get (z : Zone) (i j : Nat) : Bnd := (z.m.getD i #[]).getD j none

/-- The matrix of the nodes `0 … n` given by `f`. -/
def ofFn (n : Nat) (f : Nat → Nat → Bnd) : Zone :=
  ⟨n, Array.ofFn (n := n + 1) fun i => Array.ofFn (n := n + 1) fun j => f i j⟩

theorem get_ofFn {n : Nat} {f : Nat → Nat → Bnd} {i j : Nat} (hi : i ≤ n) (hj : j ≤ n) :
    (ofFn n f).get i j = f i j := by
  simp [get, ofFn, Array.getD, Array.size_ofFn, Nat.lt_succ_of_le hi, Nat.lt_succ_of_le hj]

/-- No bound but `v i - v i ≤ 0`. -/
def top (n : Nat) : Zone := ofFn n fun i j => if i = j then some 0 else none

/-- `v` meets every bound between the nodes `0 … n`. -/
def Sat (z : Zone) (v : Nat → Int) : Prop :=
  ∀ i ≤ z.n, ∀ j ≤ z.n, ∀ c, z.get i j = some c → v j - v i ≤ c

/-! ## Closure -/

/-- Each entry tightened by the path through node `k`. -/
def relax (k : Nat) (z : Zone) : Zone :=
  ofFn z.n fun i j => Bnd.min (z.get i j) (Bnd.add (z.get i k) (z.get k j))

@[simp] theorem relax_n (k : Nat) (z : Zone) : (relax k z).n = z.n := rfl

/-- Relaxing through a node keeps the valuations. -/
theorem relax_sat {k : Nat} {z : Zone} (hk : k ≤ z.n) (v : Nat → Int) :
    (relax k z).Sat v ↔ z.Sat v := by
  constructor
  · intro h i hi j hj c hc
    obtain ⟨c', h', hle⟩ := Bnd.min_le_left (b := Bnd.add (z.get i k) (z.get k j)) hc
    have := h i hi j hj c' (by rw [relax, get_ofFn hi hj]; exact h')
    omega
  · intro h i hi j hj c hc
    rw [relax, get_ofFn (n := z.n) hi hj] at hc
    rcases Bnd.min_eq_some hc with hc | hc
    · exact h i hi j hj c hc
    · obtain ⟨x, y, hx, hy, rfl⟩ := Bnd.add_eq_some hc
      have := h i hi k hk x hx
      have := h k hk j hj y hy
      omega

/-- The zone closed by every path (Floyd-Warshall): `O(n³)`. -/
def close (z : Zone) : Zone := (List.range (z.n + 1)).foldl (fun z k => relax k z) z

theorem foldl_relax_n (ks : List Nat) (z : Zone) :
    (ks.foldl (fun z k => relax k z) z).n = z.n := by
  induction ks generalizing z with
  | nil => rfl
  | cons k ks ih => simp [List.foldl, ih]

theorem foldl_relax_sat (ks : List Nat) (z : Zone) (hks : ∀ k ∈ ks, k ≤ z.n) (v : Nat → Int) :
    (ks.foldl (fun z k => relax k z) z).Sat v ↔ z.Sat v := by
  induction ks generalizing z with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl]
    rw [ih (relax k z) (fun k' hk' => by simpa using hks k' (List.mem_cons_of_mem _ hk'))]
    exact relax_sat (hks k (List.mem_cons_self ..)) v

@[simp] theorem close_n (z : Zone) : z.close.n = z.n := foldl_relax_n _ _

/-- **Closing keeps the valuations**: a valuation meets the closed zone's
bounds exactly when it meets the zone's. -/
theorem close_sat (z : Zone) (v : Nat → Int) : z.close.Sat v ↔ z.Sat v :=
  foldl_relax_sat _ z (fun _ hk => Nat.le_of_lt_succ (List.mem_range.mp hk)) v

/-! ## Adding a constraint -/

/-- The zone with `v j - v i ≤ c` added to its entry, not closed. -/
def tighten (i j : Nat) (c : Int) (z : Zone) : Zone :=
  ofFn z.n fun a b => if a = i ∧ b = j then Bnd.min (z.get a b) (some c) else z.get a b

@[simp] theorem tighten_n (i j : Nat) (c : Int) (z : Zone) : (tighten i j c z).n = z.n := rfl

theorem tighten_sat {i j : Nat} {c : Int} {z : Zone} (hi : i ≤ z.n) (hj : j ≤ z.n)
    (v : Nat → Int) : (tighten i j c z).Sat v ↔ z.Sat v ∧ v j - v i ≤ c := by
  constructor
  · intro h
    refine ⟨fun a ha b hb d hd => ?_, ?_⟩
    · by_cases hab : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := hab
        obtain ⟨d', h', hle⟩ := Bnd.min_le_left (b := some c) hd
        have hg : (tighten a b c z).get a b = some d' := by
          rw [tighten, get_ofFn ha hb]; simpa only [and_self, ↓reduceIte] using h'
        have := h a ha b hb d' hg
        omega
      · have hg : (tighten i j c z).get a b = some d := by
          rw [tighten, get_ofFn ha hb]; simpa only [hab, ↓reduceIte] using hd
        exact h a ha b hb d hg
    · obtain ⟨d', h', hle⟩ := Bnd.min_le_right (a := z.get i j) (rfl : some c = some c)
      have hg : (tighten i j c z).get i j = some d' := by
        rw [tighten, get_ofFn hi hj]; simpa only [and_self, ↓reduceIte] using h'
      have := h i hi j hj d' hg
      omega
  · rintro ⟨h, hc⟩ a ha b hb d hd
    rw [tighten, get_ofFn (n := z.n) ha hb] at hd
    split at hd
    · rename_i hab
      obtain ⟨rfl, rfl⟩ := hab
      rcases Bnd.min_eq_some hd with hd | hd
      · exact h a ha b hb d hd
      · cases hd; exact hc
    · exact h a ha b hb d hd

/-- `v j - v i ≤ c` added, and the zone closed again. -/
def add (i j : Nat) (c : Int) (z : Zone) : Zone := (tighten i j c z).close

@[simp] theorem add_n (i j : Nat) (c : Int) (z : Zone) : (add i j c z).n = z.n := by
  simp [add]

/-- **Adding a constraint**: the valuations of `z.add i j c` are those of `z`
that meet `v j - v i ≤ c`. -/
theorem add_sat {i j : Nat} {c : Int} {z : Zone} (hi : i ≤ z.n) (hj : j ≤ z.n)
    (v : Nat → Int) : (z.add i j c).Sat v ↔ z.Sat v ∧ v j - v i ≤ c := by
  rw [add, close_sat]; exact tighten_sat hi hj v

/-! ## Emptiness -/

/-- A node with a negative bound on `v i - v i`. -/
def negDiag (z : Zone) : Bool :=
  (List.range (z.n + 1)).any fun i => match z.get i i with
    | some c => decide (c < 0)
    | none => false

/-- Is the zone empty? After closing, a negative cycle shows on the diagonal. -/
def empty? (z : Zone) : Bool := z.close.negDiag

theorem negDiag_unsat {z : Zone} (h : z.negDiag = true) (v : Nat → Int) : ¬ z.Sat v := by
  intro hs
  simp only [negDiag, List.any_eq_true, List.mem_range] at h
  obtain ⟨i, hi, hc⟩ := h
  split at hc
  · rename_i c hget
    have := hs i (Nat.le_of_lt_succ hi) i (Nat.le_of_lt_succ hi) c hget
    simp at hc; omega
  · cases hc

/-- **An empty zone admits no valuation.** -/
theorem empty?_sound {z : Zone} (h : z.empty? = true) (v : Nat → Int) : ¬ z.Sat v := by
  rw [← close_sat]; exact negDiag_unsat h v

end Zone

/-! ## Examples -/

-- A chain: `x - y ∈ [0, 5]` and `y - z ∈ [0, 5]` (nodes `x = 1`, `y = 2`,
-- `z = 3`) give `x - z ∈ [0, 10]`: the entries `(3, 1)` and `(1, 3)`.
#guard
  let z := ((((Zone.top 3).add 2 1 5).add 1 2 0).add 3 2 5).add 2 3 0
  z.get 3 1 == some 10 && z.get 1 3 == some 0 && !z.empty?

-- A negative cycle: `x - y ≤ -1` and `y - x ≤ 0`.
#guard ((Zone.top 2).add 2 1 (-1) |>.add 1 2 0).empty?

-- Unary bounds through the zero node: `x ≤ 3` and `y - x ≤ 2` give `y ≤ 5`.
#guard ((Zone.top 2).add 0 1 3 |>.add 1 2 2).get 0 2 == some 5

end Substrait
