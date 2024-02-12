import Lean
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import FormalisingMathematics2024.Section02reals.missing

example (a b: ℝ) (h : a ≤ b) : a/4 ≤ b/4 := by
  cancel_denoms
  exact h

theorem sq_ineq (a b : ℝ) (hpos : 0 ≤ a) : a ≤ b → a^2 ≤ b^2 := by
  exact fun a_1 ↦ pow_le_pow_left hpos a_1 2

example (a : ℝ) (ha : 0 ≤ a) : Real.sqrt (a^2) = a := by
  exact Real.sqrt_sq ha

-- Theorem 1.1, two-variable case
theorem amgm2 (a b : ℝ) (hpos1 : 0 ≤ a) (hpos2 : 0 ≤ b) : Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have h1 : 0 ≤ (a + b)^2 - 4*a*b := by {
    calc
      0 ≤ (a - b)^2 := sq_nonneg (a - b)
      _ = (a + b)^2 - 4*a*b := by ring
  }
  simp at h1

  have h3 : Real.sqrt (4*a*b) ≤ Real.sqrt ((a + b)^2) := by {
    cancel_sqrt
    exact sq_nonneg (a + b)
  }

  have hpos3 : 0 ≤ a + b := by linarith
  have h4 : Real.sqrt ((a+b)^2) = a+b := by exact Real.sqrt_sq hpos3
  rw [h4] at h3

  calc
    Real.sqrt (a * b) = 2 * Real.sqrt (a * b) / 2 := by ring
    _ = Real.sqrt (4 * a * b) / 2 := by {
      congr
      calc
        2 * Real.sqrt (a*b) = Real.sqrt 4 * Real.sqrt (a*b) := by {
          congr
          norm_sqrt
        }
        _ = Real.sqrt (4 * a * b) := by {

          field_simp

          ring
        }
    }
    _ ≤ (a + b) / 2 := by {
      cancel_denoms
      exact h3
    }

open Finset Classical BigOperators NNReal ENNReal

theorem sqrt_sqrt (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x ^ ((1:ℝ)/4) := by {
  rw [Real.sqrt_eq_cases]
  repeat constructor
  rw [eq_comm]
  rw [Real.sqrt_eq_cases]
  repeat constructor
  ring_nf

  suffices (x ^ ((1:ℝ)/4)) ^ (4:ℝ) = x by {
    have e : (x ^ ((1:ℝ)/4)) ^ (4:ℝ) = (x ^ ((1:ℝ)/4)) ^ (4:ℕ) := by norm_cast
    rw [← e]
    exact this
  }

  rw [← Real.rpow_mul]

  simp

  exact hx

  exact mul_self_nonneg (x ^ (1 / 4))

  exact Real.rpow_nonneg_of_nonneg hx (1 / 4)
}

-- Real.sqrt (a * b) ≤ (a + b) / 2
-- Real.sqrt (c * d) ≤ (c + d) / 2
-- Theorem 1.1, four-variable case
theorem amgm4 (a b c d : ℝ) (hpos1 : 0 ≤ a) (hpos2 : 0 ≤ b) (hpos3 : 0 ≤ c) (hpos4 : 0 ≤ d) : (a * b * c * d)^((1:ℝ)/4) ≤ (a + b + c + d) / 4 := by
  have h1 : (Real.sqrt (a * b) + Real.sqrt (c * d)) ≤ (a + b + c + d) / 2 := by {
    calc
      (Real.sqrt (a * b) + Real.sqrt (c * d)) ≤ (a + b) / 2 + Real.sqrt (c * d) := by {
        gcongr
        exact amgm2 a b hpos1 hpos2
      }
      _ ≤ (a + b) / 2 + (c + d) / 2 := by {
        gcongr
        exact amgm2 c d hpos3 hpos4
      }
      _ = (a + b + c + d) / 2 := by {
        cancel_denoms
        ring
      }
  }

  have h1 : (Real.sqrt (a * b) + Real.sqrt (c * d)) / 2 ≤ (a + b + c + d) / 4 := by {
    cancel_denoms
    cancel_denoms at h1
    exact h1
  }

  have h2 : Real.sqrt (Real.sqrt (a * b) * Real.sqrt (c * d)) ≤ (Real.sqrt (a * b) + Real.sqrt (c * d)) / 2 := amgm2 (Real.sqrt (a * b)) (Real.sqrt (c * d)) (Real.sqrt_nonneg (a * b)) (Real.sqrt_nonneg (c * d))

  have eq1 : Real.sqrt (Real.sqrt (a * b) * Real.sqrt (c * d)) = Real.sqrt (Real.sqrt (a * b * c * d)) := by {
    field_simp
    ring
  }

  rw [eq1] at h2

  rw [sqrt_sqrt] at h2

  linarith

  suffices 0 ≤ (a*b)*(c*d) by linarith

  exact mul_nonneg (mul_nonneg hpos1 hpos2) (mul_nonneg hpos3 hpos4)

theorem cancels (a b c : ℝ) (hc : 0 ≤ c) : a ≤ b ↔ a * c ≤ b * c := by sorry

-- theorem amgm3; actually kind of hard
theorem amgm3 (a b c : ℝ) (hpos1 : 0 ≤ a) (hpos2 : 0 ≤ b) (hpos3 : 0 ≤ c) : (a * b * c)^((1:ℝ)/3) ≤ (a + b + c) / 3 := by
  have exists_A : ∃ A, (a + b + c) / 3 = A := by use (a+b+c)/3
  cases' exists_A with A hA

  have hpos4 : 0 ≤ A := by linarith
  have h : (a * b * c * A)^((1:ℝ)/4) ≤ (a + b + c + A) / 4 := by {
    apply amgm4
    repeat linarith
  }

  have rw1 : (a * b * c * A) ^ ((1:ℝ) / 4) = (a * b * c)^((1:ℝ) / 4) * A ^ ((1:ℝ) / 4) := by {
    rw [Real.mul_rpow]
    have h : 0 ≤ a*b := by exact mul_nonneg hpos1 hpos2
    exact mul_nonneg h hpos3
    linarith
  }

  have rw2 : (a + b + c + A) / 4 = A := by linarith

  have rw3 : A = A ^ ((3:ℝ) / 4) *  A ^ ((1:ℝ) / 4) := by sorry

  rw [rw1] at h
  rw [rw2] at h
  rw [rw3] at h


  sorry
