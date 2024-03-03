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

theorem amgm2_rtfree (a b : ℝ) (hpos1 : 0 ≤ a) (hpos2 : 0 ≤ b) : a * b ≤ (a*a + b*b) / 2 := by
  sorry

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

theorem cancels (a b c : ℝ) (hc : 0 < c) : a ≤ b ↔ a * c ≤ b * c := by {
  have hc' : 0 ≤ c := by exact LT.lt.le hc
  constructor
  intro h
  exact mul_le_mul_of_nonneg_right h hc'
  intro h
  have h' : a * c * c⁻¹ ≤ b * c * c⁻¹ := by {
    apply mul_le_mul_of_nonneg_right
    exact h
    exact inv_nonneg.mpr hc'
  }
  field_simp at h'
  exact h'
}

theorem takes4weak (a b : ℝ) (ha : 0 ≤ a) : a ≤ b → a ^ ((4:ℝ)/3) ≤ b ^ ((4:ℝ)/3) := by
  intro h1
  apply Real.rpow_le_rpow
  exact ha
  exact h1
  norm_num

theorem takes14weak (a b : ℝ) (ha : 0 ≤ a) : a ≤ b → a ^ ((1:ℝ)/4) ≤ b ^ ((1:ℝ)/4) := by
  intro h1
  apply Real.rpow_le_rpow
  exact ha
  exact h1
  norm_num

-- currently unused
theorem takes4 (a b : ℝ) (ha : 0 ≤ a) : a ≤ b ↔ a ^ ((4:ℝ)/3) ≤ b ^ ((4:ℝ)/3) := by
  sorry

noncomputable def _14 : ℝ := (1:ℝ)/4
noncomputable def _34 : ℝ := (3:ℝ)/4

theorem _14_def : _14 = (1:ℝ)/4 := by rfl
theorem _34_def : _34 = (3:ℝ)/4 := by rfl

-- theorem amgm3 from https://math.stackexchange.com/questions/2576966/elementary-proof-for-sqrt3xyz-leq-dfracxyz3
theorem amgm3 (x y z : ℝ) (hpos1 : 0 ≤ x) (hpos2 : 0 ≤ y) (hpos3 : 0 ≤ z) : (x * y * z)^((1:ℝ)/3) ≤ (x + y + z) / 3 := by
  have exists_A : ∃ A, (x + y + z) / 3 = A := by use (x + y + z)/3
  cases' exists_A with A hA

  have hpos4 : 0 ≤ A := by linarith

  -- 1st inequality
  have h : (x * y * z * A)^_14 ≤ (x + y + z + A) / 4 := by {
    apply amgm4
    repeat linarith
  }

  have rw1 : (x * y * z * A) ^ _14 = (x * y * z)^_14 * A ^ _14 := by {
    rw [Real.mul_rpow]
    have h : 0 ≤ x*y := by exact mul_nonneg hpos1 hpos2
    exact mul_nonneg h hpos3
    linarith
  }

  have rw2 : (x + y + z + A) / 4 = A := by linarith

  have rw3 : A = (A ^ _34) *  (A ^ _14) := by {
    rw [_34_def]
    rw [_14_def]
    rw [← Real.rpow_add_of_nonneg]
    norm_num
    exact hpos4
    norm_num
    norm_num
  }

  rw [rw1] at h

  rw [rw2] at h

  -- 3rd inequality
  have h' : (x * y * z) ^ _14 * A ^ _14 ≤ (A ^ _34) *  (A ^ _14) := by {
    calc
      (x * y * z) ^ _14 * A ^ _14 ≤ A := by exact h
      _ = (A ^ _34) *  (A ^ _14) := by exact rw3
  }

  have h_cases : 0 ≤ A ^ _14 := by positivity
  have h_cases' : 0 = A ^ _14 ∨ 0 < A ^ _14 := by exact LE.le.eq_or_lt h_cases
  cases' h_cases' with h1 h2

  -- case where A=0
  rw [_14_def] at h1
  have h1' : 0 = A := by {
    calc
      (0:ℝ) = 0 ^ (4:ℝ) := by norm_num
      _ = (A ^ _14) ^ (4:ℝ) := by {
        rw [h1]
        rw [_14_def]
      }
      _ = A := by {
        rw [_14_def]
        rw [← Real.rpow_mul]
        norm_num
        exact hpos4
      }
  }
  rw [← hA] at h1'
  have hx : x = 0 := by linarith
  have hy : y = 0 := by linarith
  have hz : z = 0 := by linarith
  simp [hx, hy, hz]

  rw [← cancels] at h'

  apply takes4weak at h'

  rw [← Real.rpow_mul] at h'
  rw [← Real.rpow_mul] at h'

  have hs1 : _14 * ((4:ℝ)/3) = (1:ℝ)/3 := by {
    field_simp
    rw [_14_def]
    simp
  }

  have hs2 : _34 * ((4:ℝ)/3) = 1 := by {
    field_simp
    rw [_34_def]
    simp
  }

  rw [hs1, hs2] at h'

  simp at h'
  simp
  rw [hA]
  exact h'

  exact hpos4

  repeat positivity

-- example 1.2
theorem example12 (a b c: ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c):  a * b + b * c + c * a ≤ a*a + b*b + c*c := by
  have h1 := amgm2_rtfree a b ha hb
  have h2 := amgm2_rtfree b c hb hc
  have h3 := amgm2_rtfree c a hc ha

  linarith
