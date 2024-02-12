import Lean
import Mathlib.Tactic

-- sqrt_eq_cases for y = √ x
theorem eq_sqrt_cases (x y : ℝ) : y = Real.sqrt x ↔ y * y = x ∧ 0 ≤ y ∨ x < 0 ∧ y = 0 := by
  rw [eq_comm]
  exact Real.sqrt_eq_cases

macro "norm_sqrt_eq" : tactic => `(tactic| rw [Real.sqrt_eq_cases] <;> ring_nf <;> repeat norm_num )
macro "norm_eq_sqrt" : tactic => `(tactic| rw [eq_sqrt_cases] <;> ring_nf <;> repeat norm_num )

-- Normalize square roots of rational literals
macro "norm_sqrt" : tactic => `(tactic| first | norm_sqrt_eq | norm_eq_sqrt)

example : Real.sqrt 25 = 5 := by norm_sqrt
example : Real.sqrt 4 = 2 := by norm_sqrt
example : Real.sqrt 18 = 3*Real.sqrt 2 := by norm_sqrt
example : 2 = Real.sqrt 4:= by norm_sqrt
example : Real.sqrt (1/4) = 1/2 := by norm_sqrt
example : Real.sqrt (1/2) = Real.sqrt 2 / 2 := by norm_sqrt

example : Real.sqrt 4 = 2 := by
  exact Eq.trans (by norm_num) (Real.sqrt_sq zero_le_two)



-- Cancel sqrts in an inequality

macro "cancel_sqrt" : tactic => `(tactic| first | rw [Real.sqrt_lt_sqrt_iff] ; repeat assumption | rw [Real.sqrt_le_sqrt_iff] ; repeat assumption )

example (a b : ℝ) (hpos : 0 ≤ b) : a ≤ b ↔ Real.sqrt a ≤ Real.sqrt b := by
  cancel_sqrt

example (a b c: ℝ) (hpos : 0 ≤ b) : a+c ≤ b ↔ Real.sqrt (a+c) ≤ Real.sqrt b := by
  cancel_sqrt

example (a b : ℝ) (hpos : 0 ≤ b) (ineq : a ≤ b) : Real.sqrt a ≤ Real.sqrt b := by
  cancel_sqrt

example {y : ℝ} (hy : y≥ 0) : y^2 = 3 ↔ Real.sqrt 3 = y := by
  rw [Real.sqrt_eq_iff_sq_eq _ hy]
  norm_num
