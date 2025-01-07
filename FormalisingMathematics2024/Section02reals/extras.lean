/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet5 -- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

-- Exercise 2.3.1: The sequence (a,a,...) converges to a
example (a : ℝ): TendsTo (fun _ ↦ a) a := by
  rw [tendsTo_def] at *
  intro ε hε
  use 0
  intro n _
  field_simp
  exact hε

example (a b k : ℝ) (a_lt_b : a < b) (kpos : 0 < k) : (a*k < b*k) := by
  exact (mul_lt_mul_right kpos).mpr a_lt_b

example (ε : ℝ) (ε_pos : 0 < ε) (hn : 1 < ε*ε) : 1 < ε := by
  have := (Real.sqrt_lt_sqrt_iff (by norm_num)).mpr hn
  simp at this
  let t := (Real.sqrt_eq_iff_mul_self_eq_of_pos ε_pos).mpr rfl
  rw [t] at this
  exact this

instance : StrictMono NNReal.sqrt := by
  intro a b hab
  exact NNReal.sqrt_lt_sqrt_iff.mpr hab

noncomputable def my_sqrt (x : NNReal) : NNReal :=
  NNReal.sqrt x

instance : StrictMono my_sqrt := by
  intro a b hab
  exact NNReal.sqrt_lt_sqrt_iff.mpr hab

example (ε : ℝ) (ε_pos : 0 < ε) (hn : 1 < ε*ε) : 1 < ε := by
  have : 0 ≤ ε := by positivity
  lift ε to NNReal using this
  have : 1 < ε * ε := by exact hn
  apply_fun my_sqrt at this
  sorry
  exact instStrictMonoNNRealToPreorderToPartialOrderInstNNRealStrictOrderedSemiringMy_sqrt

-- Example 2.2.5: The sequence given by a_n = 1/sqrt(n) converges to 0
example : TendsTo (fun n ↦ 1/(Real.sqrt n)) 0 := by
  intro ε ε_pos

  -- Choose a natural number N satisfying N > 1/ε^2
  have exists_N : ∃ N : ℕ, (1/(ε*ε) < N) := by {
    use (1 + Nat.ceil (1/(ε*ε)))
    simp
    calc
      ε⁻¹ * ε⁻¹ ≤ ⌈ε⁻¹ * ε⁻¹⌉₊ := by exact Nat.le_ceil (ε⁻¹ * ε⁻¹)
      _ < 1 + ↑⌈ε⁻¹ * ε⁻¹⌉₊ := by simp
  }

  cases' exists_N with N N_cond

  have N_ge_0 : 0 < N := by
    rify
    have : 0 ≤ 1/(ε*ε) := by positivity
    linarith

  use N
  intro n hn

  rw [sub_zero, abs_of_nonneg (one_div_nonneg.mpr (Real.sqrt_nonneg n))]

  have hn : 1/(ε*ε) < n := by {
    rify at N_ge_0
    rify at hn
    linarith
  }

  have hn_canonical : 1 < n*ε*ε := by {
    have pos : 0 < ε*ε := by positivity
    have := (mul_lt_mul_right pos).mpr hn
    field_simp at this
    rw [mul_assoc]
    exact this
  }

  have hn_canonical_sqrt := (Real.sqrt_lt_sqrt_iff (by norm_num)).mpr hn_canonical
  simp at hn_canonical_sqrt

  simp
  rw [inv_pos_lt_iff_one_lt_mul']

  calc
    1 < Real.sqrt (n * ε * ε) := hn_canonical_sqrt
    _ = Real.sqrt (n * (ε * ε)) := by ring_nf
    _ = Real.sqrt n * Real.sqrt (ε*ε) := by simp
    _ = Real.sqrt n * ε := by {
      simp
      left
      exact (Real.sqrt_eq_iff_mul_self_eq_of_pos ε_pos).mpr rfl
    }

  simp
  linarith

-- Example 2.2.6: The sequence given by a_n = n+1/n converges to 1
example : TendsTo (fun n ↦ (n+1)/n) 1 := by
  intro ε ε_pos

  -- Choose a natural number N satisfying N > 1/ε^2
  have exists_N : ∃ N : ℕ, (1/ε < N) := by
    use (1 + Nat.ceil (1/ε))
    have : 1/ε ≤ ⌈1/ε⌉₊ := Nat.le_ceil (1/ε)
    push_cast
    linarith

  cases' exists_N with N N_cond

  use N
  intro n hn

  have n_pos : 0 < (n:ℝ) := by
    have : 0 < 1/ε := by positivity
    rify at hn
    linarith


  simp

  have : ((n + 1) / (n: ℝ)) - 1 = 1/n := by field_simp

  rw [this, abs_of_nonneg]

  have N_cond : 1 / ε < n := by
    rify at hn
    linarith

  have pos : 0 < (ε / n) := by positivity
  have N_cond := (mul_lt_mul_right pos).mpr N_cond
  field_simp at N_cond
  rw [mul_comm] at N_cond
  field_simp at N_cond
  exact N_cond

  simp only [one_div, inv_nonneg, Nat.cast_nonneg]


-- The sequence (1,2,3...) not converge to any real number
example : ∀ t : ℝ, ¬(TendsTo (fun n ↦ n) t) := by {
  intro lim
  by_contra h_converges
  rw [tendsTo_def] at *

  cases' (h_converges (1/2) (by norm_num)) with B hB

  have exists_bad_n : ∃ bad_n : ℕ, (lim+1) < bad_n ∧ B < bad_n := by {
    use Nat.max (1 + Nat.ceil (lim+1)) (1+B)
    constructor
    simp
    left
    calc
      lim + 1 ≤ ↑⌈lim + 1⌉₊ := by exact Nat.le_ceil (lim + 1)
      _ < 1 + ↑⌈lim + 1⌉₊ := by simp
    simp
  }

  cases' exists_bad_n with bad_n h_bad_n

  specialize hB bad_n

  cases' h_bad_n with h1 h2

  have hBn : B ≤ bad_n := by linarith

  apply hB at hBn

  have h1 : 1 < |↑bad_n - lim| := by {
    rw [lt_abs]
    left
    linarith
  }

  linarith
}

-- The sequence (1,0,1,0,...) does not converge to any real number
example : ∀ t : ℝ, ¬(TendsTo (fun n ↦ if n%2 = 1 then 0 else 1) t) := by sorry

-- Definition 2.3.1: Bounded sequence
def Bounded (a : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, 0 < M ∧ (∀ n, |a n| < M)

theorem Bounded_def {a : ℕ → ℝ} :
    Bounded a ↔ ∃ M : ℝ, 0 < M ∧ (∀ n, |a n| < M) := by
  rfl

-- The sequence 1/x is bounded

example : Bounded (fun n ↦ 1/(n+1)) := by
  rw [Bounded_def] at *
  use 2
  constructor
  norm_num
  intro n
  push_cast
  have : |1 / ((n : ℝ) + 1)| = 1 / ((n : ℝ) + 1) := by exact abs_eq_self.mpr (by positivity)
  rw [this]
  simp
  rw [inv_pos_lt_iff_one_lt_mul (by linarith)]
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

-- Any finite prefix of a sequence has an upper bound
theorem FinitePrefixMax (f : ℕ → ℝ) (N : ℕ) : ∃ B, ∀ n : ℕ, n < N → f n ≤ B := by
  use max_prefix f N
  intro n hnB
  apply mp_increasing
  exact hnB

-- Any finite prefix of a sequence has a magnitude bound
theorem FinitePrefixMax' (f : ℕ → ℝ) (N : ℕ) : ∃ B, ∀ n : ℕ, n < N → |f n| ≤ B := by
  exact FinitePrefixMax (fun n ↦ |f n|) N

-- Theorem 2.3.2 from Abbott. Converges => Bounded
theorem ConvergesThenBounded (f : ℕ → ℝ) (hc : ∃ t, TendsTo f t) : Bounded f := by
  cases' hc with l h_conv
  specialize h_conv 1 (by norm_num)

  cases' h_conv with N hN

  have h := FinitePrefixMax' f N

  cases' h with B hB

  use (max (1 + Nat.ceil B) (Nat.ceil (|l|+2)))

  constructor
  . rw [lt_max_iff]; left; linarith

  intro n

  cases (le_or_lt N n) with
  | inl N_lt_n => {
    rw [lt_max_iff]
    right

    have fn_near_l := hN n N_lt_n

    have h6: |f n| - |l| ≤ |f n - l| := abs_sub_abs_le_abs_sub (f n) l
    have h7: |f n| - |l| < 1 := by linarith
    calc
      |f n| < |l| + 1 := sub_lt_iff_lt_add'.mp h7
      _ ≤ |l| + 2 := by linarith
      _ ≤ ↑⌈|l| + 2⌉₊ := Nat.le_ceil (|l| + 2)
  }
  | inr h1 => {
    simp
    left

    calc
      |f n| ≤ B := hB n h1
      _ < (1 + ⌈B⌉₊) := by {
        calc
          B ≤ ↑⌈B⌉₊ := Nat.le_ceil B
          _ < 1 +  ↑⌈B⌉₊ := by apply lt_one_add
      }
  }

-- Theorem 2.3.3.iii (algebraic limit theorem, product)
theorem tendsTo_mul_abott {a b : ℕ → ℝ} {A B : ℝ} (a_pos : A ≠ 0) (ha : TendsTo a A) (hb : TendsTo b B) :
    TendsTo (fun n ↦ a n * b n) (A * B) := by
  rw [tendsTo_def]
  intro ε hε

  have h_b_bounded := ConvergesThenBounded b (Exists.intro B hb)
  cases' h_b_bounded with M hM
  cases' hM with m_pos m_bounds

  have h_exists_n1 := hb (ε/(2*|A|)) (by positivity)
  cases' h_exists_n1 with n1 hn1

  have h_exists_n2 := ha (ε/(2*M)) (by positivity)
  cases' h_exists_n2 with n2 hn2

  use max n1 n2

  intro n hn

  calc
    |a n * b n - (A * B)| = |a n * b n - A * b n + (A * b n - A * B)| := by ring_nf
    _ ≤ |a n * b n - A * b n| + |A * b n - A * B| := abs_add (a n * b n - A * b n) (A * b n - A * B)
    _ = |b n * (a n - A)| + |A * (b n - B)| := by ring_nf
    _ = |b n| * |a n - A| + |A * (b n - B)| := by congr; exact abs_mul (b n) (a n - A)
    _ = |b n| * |a n - A| + |A| * |b n - B| := by congr; exact abs_mul A (b n - B)
    _ ≤ M * |a n - A| + |A| * |b n - B| := by {
      simp
      specialize m_bounds n
      have hpos : 0 ≤ |a n - A| := abs_nonneg (a n - A)
      suffices : |b n| ≤ M
      exact mul_le_mul_of_nonneg_right this hpos
      exact LT.lt.le m_bounds
    }
    _ < M * (ε / (2*M)) + |A| * |b n - B| := by
      gcongr
      apply hn2
      exact le_of_max_le_right hn
    _ < M * (ε / (2*M)) + |A| * (ε / (2*|A|)) := by
      gcongr
      apply hn1
      exact le_of_max_le_left hn
    _ = ε := by {
      field_simp
      ring
    }



-- Exercise 2.2.7: Define convergence to infinity
def TendsToInf (a : ℕ → ℝ) : Prop :=
  ∀ M > 0, ∃ B : ℕ, ∀ n, B ≤ n → M < a n

theorem tendsToInf_def {a : ℕ → ℝ} :
    TendsToInf a ↔ ∀ M, 0 < M → ∃ B : ℕ, ∀ n, B ≤ n → M < a n := by
  rfl


-- a_n = sqrt n tends to infinity

example : TendsToInf (fun n ↦ Real.sqrt n) := by
  rw [tendsToInf_def] at *
  intro M M_pos

  use ⌈M * M⌉₊ + 1

  intro n n_large

  have n_large : ⌈M * M⌉₊ < n := by linarith

  rify at n_large
  have hB_sqrt := (Real.sqrt_lt_sqrt_iff (by norm_num)).mpr n_large

  calc
    M = Real.sqrt (M^2) := by rw [Real.sqrt_sq (by positivity)]
    _ = Real.sqrt (M*M) := by ring_nf
    _ <= Real.sqrt ↑⌈M * M⌉₊ := by {
      simp only [Nat.cast_nonneg, Real.sqrt_le_sqrt_iff]
      exact Nat.le_ceil (M * M)
    }
    _ < Real.sqrt n := hB_sqrt



end Section2sheet6
