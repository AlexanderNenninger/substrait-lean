import Lean

/-!
# The build budget's calibration

`scripts/lean_timings.py calibrate` compiles this file, which imports only Lean's
core, before the build and divides each module's CPU time by its CPU time, so
the budget's ceilings hold on any runner (docs/build-performance.md, "The
budget"). Like the generated modules, it spends its time in `simp`, `omega` and
reduction. Changing it changes every ratio: run `write-budget` again after.
-/

def poly (x : Nat) : Nat := x * x * x + 3 * x * x + 3 * x + 1

def walk : Nat → List Nat → Nat
  | acc, [] => acc
  | acc, x :: xs => walk (acc * 31 % 1000003 + x) xs

structure Tally where
  sum : Int
  count : Nat
  flag : Bool

def step (a : Tally) (x : Int) : Tally :=
  { a with sum := a.sum + x, count := a.count + 1, flag := a.flag || x < 0 }

-- Normalisation, as the lowering lemmas do.
theorem poly_eq (x : Nat) : poly x = (x + 1) * (x + 1) * (x + 1) := by
  simp only [poly]; grind

theorem step_count (a : Tally) (xs : List Int) :
    (xs.foldl step a).count = a.count + xs.length := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, step]; omega

-- Linear arithmetic, many small goals.
theorem lin₁ (a b c d : Int) (h₁ : a ≤ b) (h₂ : b < c) (h₃ : c ≤ d + 2) :
    a < d + 3 := by omega
theorem lin₂ (a b c : Nat) (h : a + 2 * b ≤ 3 * c) (h' : c < b) : a < b + 1 := by omega
theorem lin₃ (x y : Int) (h : 3 * x + 5 * y = 7) (h' : 0 ≤ x) (h'' : x ≤ 4) :
    y ≤ 2 := by omega

-- Reduction in the kernel and the elaborator.
theorem walk_val : walk 7 (List.range 300) = walk 7 (List.range 300) := rfl
theorem poly_val : poly 1234 = 1883652875 := by decide
example : (List.range 120).foldl (· + ·) 0 = 7140 := by decide
example : ((List.range 60).map poly).length = 60 := by simp

-- The same proofs again, many times: the bulk of the work, as in a module of entries.
open Lean Elab Command in
elab "calib_block " n:num : command => do
  for i in [0:n.getNat] do
    let k := Syntax.mkNumLit (toString (i + 2))
    elabCommand (← `(example (x : Nat) (a b : Int) (h : a ≤ b) :
        poly (x + $k) = (x + $k + 1) * (x + $k + 1) * (x + $k + 1) ∧ a - $k < b + $k := by
      constructor
      · simp only [poly]; grind
      · omega))

calib_block 150
