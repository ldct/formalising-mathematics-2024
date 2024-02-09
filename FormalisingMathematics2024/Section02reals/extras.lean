/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet5 -- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

example (a b : ℝ) : 0 < a → |a*b| = a*|b| := by {
  rw [abs_mul a b]
  simp
  intro h
  left
  linarith
}

example (a b c: ℝ) : 0 < c → a < b → c*a < c*b := by sorry

-- Exercise 2.3.1: The sequence (37,37,...) converges to 37
example : TendsTo (fun _ ↦ 37) 37 := by
  rw [tendsTo_def] at *
  intro ε hε
  use 0
  intro n _
  field_simp
  exact hε

-- Example 2.2.5: The sequence given by a_n = 1/sqrt(n) converges to 0
example : TendsTo (fun n ↦ 1/(Real.sqrt n)) 0 := by
  rw [tendsTo_def] at *
  intro ε hε
  have hB : ∃ B : ℕ, (1/(ε*ε) < B) ∧ (1 < B) := by {
    use Nat.max 2 (1 + Nat.ceil (1/(ε*ε)))
    constructor
    simp
    right

    calc
      ε⁻¹ * ε⁻¹ ≤ ↑⌈ε⁻¹ * ε⁻¹⌉₊ := by exact Nat.le_ceil (ε⁻¹ * ε⁻¹)
      _ < 1 + ↑⌈ε⁻¹ * ε⁻¹⌉₊ := by simp

    calc
      1 < 2 := by norm_num
      _ ≤ Nat.max 2 (1 + ⌈1 / (ε * ε)⌉₊) := by exact Nat.le_max_left 2 (1 + ⌈1 / (ε * ε)⌉₊)
  }

  cases' hB with B hB
  use B
  intro n

  intro hn

  have hn_old : B ≤ n := by exact hn

  have hn : 1/(ε*ε) < n := by {
    cases' hB with h1 h2
    calc
      1 / (ε * ε) < B := by exact h1
      _ ≤ n := by exact Nat.cast_le.mpr hn
  }

  have hn_canonical : 1 < n*ε*ε := by {
    simp at hn
    rw [inv_mul_lt_iff] at hn
    rw [inv_pos_lt_iff_one_lt_mul] at hn
    linarith
    exact hε
    exact hε
  }

  have hn : (1/(Real.sqrt n) < ε) := by {
    simp
    rw [inv_pos_lt_iff_one_lt_mul']

    -- take squarer roots on both side of `hn_canonical`
    have hn_canonical_sqrt : Real.sqrt 1 < Real.sqrt (↑n * ε * ε) := by {

      rw [Real.sqrt_lt_sqrt_iff]

      exact hn_canonical
      norm_num
    }

    simp at hn_canonical_sqrt

    calc
      1 < Real.sqrt (↑n * ε * ε) := by exact hn_canonical_sqrt
      _ = Real.sqrt (n * (ε * ε)) := by ring_nf
      _ = Real.sqrt ↑n * Real.sqrt (ε*ε) := by simp
      _ = Real.sqrt ↑n * ε := by {
        simp
        left
        exact (Real.sqrt_eq_iff_mul_self_eq_of_pos hε).mpr rfl
      }
    simp
    linarith
  }

  rw [abs_lt] at *

  constructor

  calc
    -ε < 0 := by linarith
    _ < 1 / Real.sqrt ↑n := by {
      have h2 : 0 < Real.sqrt ↑n := by {
        apply Real.sqrt_pos.mpr
        simp
        linarith
      }
      exact one_div_pos.mpr h2
    }
    _ = 1 / Real.sqrt ↑n - 0 := by ring

  simp at *
  exact hn


-- The sequence (1,2,3...) not converge to any real number
example : ∀ t : ℝ, ¬(TendsTo (fun n ↦ n) t) := by {
  intro t
  by_contra h_converges
  rw [tendsTo_def] at *

  specialize h_converges (1/2)
  have hpos : ((0 : ℝ) < (1/2)) := by norm_num

  apply h_converges at hpos

  have h_converges : (∃ B, ∀ (n : ℕ), B ≤ n → |↑n - t| < (1/2)) := by exact hpos

  cases' h_converges with B hB

  have exists_bad_n : ∃ bad_n : ℕ, (t+1) < bad_n ∧ B < bad_n := by {
    use Nat.max (1 + Nat.ceil (t+1)) (1+B)
    constructor
    simp
    left
    calc
      t + 1 ≤ ↑⌈t + 1⌉₊ := by exact Nat.le_ceil (t + 1)
      _ < 1 + ↑⌈t + 1⌉₊ := by simp
    simp
  }

  cases' exists_bad_n with bad_n h_bad_n

  specialize hB bad_n

  cases' h_bad_n with h1 h2

  have hBn : B ≤ bad_n := by linarith

  apply hB at hBn

  have h1 : 1 < |↑bad_n - t| := by {
    rw [lt_abs]
    left
    linarith
  }

  linarith
}

-- The sequence (1,0,1,0,...) does not converge to any real number
example : ∀ t : ℝ, ¬(TendsTo (fun n ↦ if n%2 = 1 then 0 else 1) t) := by sorry


-- Example 2.2.6: The sequence a_n = (n+1)/n converges to 1

-- Definition 2.3.1: Bounded sequence

def Bounded (a : ℕ → ℝ) : Prop :=
  ∃ M : ℕ, 0 < M ∧ (∀ n, a n < M)

theorem Bounded_def {a : ℕ → ℝ} :
    Bounded a ↔ ∃ M : ℕ, 0 < M ∧ (∀ n, a n < M) := by
  rfl

-- The sequence 1/x is bounded

example : Bounded (fun n ↦ 1/(n+1)) := by
  rw [Bounded_def] at *
  use 2
  constructor
  norm_num
  intro n
  have h0 : 0 < (n:ℝ)+1 := by linarith
  simp
  rw [inv_pos_lt_iff_one_lt_mul h0]
  have hn : 1 ≤ (n:ℝ)+1 := by linarith
  simp
  -- want a tactic to replace a subexpression by an underestimate
  linarith

noncomputable def max_prefix : ((ℕ → ℝ)) → ℕ → ℝ
| _, 0   => 0
| f, x+1 => max (f x) (max_prefix f x)

theorem mp_def (f : ℕ → ℝ) (b : ℕ) : max_prefix f (b+1) = max (f b) (max_prefix f b) := by rfl

theorem mp_increasing (f : ℕ → ℝ) (a : ℕ) (b : ℕ) (hi : a < b): f a ≤ max_prefix f b := by
  induction' b with x y
  exfalso
  exact Nat.not_succ_le_zero a hi
  rw [mp_def]
  have a_cases : a < x ∨ a = x := by exact Nat.lt_succ_iff_lt_or_eq.mp hi
  cases' a_cases with p q
  apply y at p
  exact le_max_of_le_right p
  rw [q]
  exact le_max_left (f x) (max_prefix f x)

theorem FinitePrefixMax (f : ℕ → ℝ) (B : ℕ) : ∃ m_elem, ∀ n : ℕ, n < B → f n ≤ m_elem := by
  use max_prefix f B
  intro n hnB
  apply mp_increasing
  exact hnB

theorem abs_gt (a:ℝ) (b:ℝ) : |a| > b ↔ -a < -b ∧ b > a := by sorry

example (a b : ℝ) (h : |a - b| < 1) : |a| < |b| + 1 := by sorry

example (a b c: ℝ) (h1 : |a - b| < 1) (h2 : |b - c| < 1) : |a - c| < 2 := by {
  sorry
}

-- Converges => Bounded
theorem ConvergesThenBounded (f : ℕ → ℝ) (hc : ∃ t, TendsTo f t) : Bounded f := by
  cases' hc with t h_conv
  rewrite [tendsTo_def] at *
  specialize h_conv 1

  norm_num at h_conv -- eliminate the `0 < 1 →`
  cases' h_conv with B hB

  rw [Bounded_def] at *

  have h : ∃ m_elem, ∀ n : ℕ, n < B → f n ≤ m_elem := by apply FinitePrefixMax

  cases' h with m_elem h_m_elem

  use (max (1 + Nat.ceil m_elem) (Nat.ceil (|t|+2)))

  constructor

  simp

  intro n

  have cases_nb : B ≤ n ∨ n < B := by exact le_or_lt B n

  cases' cases_nb with h1 h2

  have h6: |f n| - |t| ≤ |f n - t| := by exact abs_sub_abs_le_abs_sub (f n) t

  have h7: |f n| - |t| < 1 := by exact gt_of_gt_of_ge (hB n h1) h6

  have h4 : |f n| < |t| + 1 := by exact sub_lt_iff_lt_add'.mp h7

  simp
  right

  calc
    f n = f n := rfl
    _ ≤ |f n| := le_abs_self (f n)
    _ < |t| + 1 := h4
    _ ≤ |t| + 2 := by linarith
    _ ≤ ↑⌈|t| + 2⌉₊ := Nat.le_ceil (|t| + 2)

  have h5 : f n ≤ m_elem := by exact h_m_elem n h2

  calc
    f n ≤ m_elem := h5
    _ < ↑(max (1 + ⌈m_elem⌉₊) ⌈|t| + 2⌉₊) := by {
      simp
      left
      calc
        m_elem ≤ ↑⌈m_elem⌉₊ := Nat.le_ceil m_elem
        _ < 1 +  ↑⌈m_elem⌉₊ := by apply lt_one_add
    }

example (x : ℝ) (y : ℝ) : |x + y| ≤ |x| + |y| := by exact abs_add x y

-- 2.2.3 (iii)
theorem tendsTo_mul_abott {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
  rw [tendsTo_def]
  intro ε hε

  have h_exists_n1 : ∃ n1, ∀ n : ℕ, n1 ≤ n → |b n - u| < ε/(2*t)  := by sorry

  have b_converges : ∃ z, TendsTo b z := by exact Exists.intro u hb
  have h_b_bounded : Bounded b := ConvergesThenBounded b b_converges -- callout: applying a lemma

  rw [Bounded_def] at *

  cases' h_b_bounded with m hm
  cases' hm with m_pos m_bounds

  have h_exists_n2 : ∃ n2, ∀ n : ℕ, n2 ≤ n → |a n - t| < ε/(2*m) := by sorry

  cases' h_exists_n1 with n1 hn1

  cases' h_exists_n2 with n2 hn2

  use max n1 n2

  intro n hn

  calc
    |a n * b n - (t * u)| = |a n * b n - t * b n + (t * b n - t * u)| := by ring_nf
    _ ≤ |a n * b n - t * b n| + |t * b n - t * u| := abs_add (a n * b n - t * b n) (t * b n - t * u)
    _ = |b n * (a n - t)| + |t * (b n - u)| := by ring_nf
    _ = |b n| * |a n - t| + |t * (b n - u)| := by {
      congr
      exact abs_mul (b n) (a n - t)
    }
    _ = |b n| * |a n - t| + |t| * |b n - u| := by {
      congr
      exact abs_mul t (b n - u)
    }
    _ ≤ m * |a n - t| + |t| * |b n - u| := by {
      simp
      specialize m_bounds n
      have m_bounds' : b n ≤ m := LT.lt.le m_bounds
      have hpos : 0 ≤ |a n - t| := abs_nonneg (a n - t)
      sorry
    }
    _ < ε := by {

      sorry
    }



-- Exercise 2.2.7: Define convergence to infinity

def TendsToInf (a : ℕ → ℝ) : Prop :=
  ∀ M > 0, ∃ B : ℕ, ∀ n, B ≤ n → M < a n

theorem tendsToInf_def {a : ℕ → ℝ} :
    TendsToInf a ↔ ∀ M > 0, ∃ B : ℕ, ∀ n, B ≤ n → M < a n := by
  rfl


-- a_n = sqrt n tends to infinity

example : TendsToInf (fun n ↦ Real.sqrt n) := by
  rw [tendsToInf_def] at *
  intro M hM

  have hB : ∃ B : ℕ, ⌈M * M⌉₊ < B := by {
    use ⌈M * M⌉₊ + 1
    simp
  }

  cases' hB with B hB

  use B

  intro n hn

  have hB : ⌈M * M⌉₊ < n := by linarith


  -- take squarer roots on both side of `hB`
  have hB_sqrt : Real.sqrt ⌈M * M⌉₊ < Real.sqrt n := by {
    rw [Real.sqrt_lt_sqrt_iff]
    exact Nat.cast_lt.mpr hB
    simp
  }

  have mpos : 0 ≤ M := by linarith

  calc
    M = Real.sqrt (M^2) := by {
      rw [Real.sqrt_sq]
      exact mpos
    }
    _ = Real.sqrt (M*M) := by ring_nf
    _ <= Real.sqrt ↑⌈M * M⌉₊ := by {
      simp
      exact Nat.le_ceil (M * M)
    }
    _  < Real.sqrt n := by exact hB_sqrt



end Section2sheet6
