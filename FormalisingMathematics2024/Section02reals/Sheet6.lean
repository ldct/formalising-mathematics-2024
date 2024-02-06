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

example (x: ℝ) (hx : 0 < 2 * (x/2)) : 0 < x := by {
  ring_nf
}




/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
    rw [tendsTo_def] at *
    intro ε hε
    specialize h (ε/37)
    have hp : 0 < ε/37 := by linarith
    apply h at hp
    cases' hp with B hB

    use B
    intro n hBn
    specialize hB n hBn

    -- multiply hB by 37
    have mulrw (x y : ℝ) : x < y → 37*x < 37*y := by {
      intro h
      linarith
    }
    apply mulrw at hB

    -- simplify the RHS of B
    have h : 37 * (ε / 37) = ε := by linarith
    rw [h] at hB

    calc
    |37 * a n - 37 * t| = |37 * (a n - t)| := by ring_nf
    _ = 37 * |a n - t| := by {
      rw [abs_mul 37 (a n - t)]
      simp
      norm_num
    }
    _ < ε := by exact hB

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
    rw [tendsTo_def] at *
    intro ε hε
    specialize h (ε/c)
    have hp : 0 < ε/c := by exact div_pos hε hc
    apply h at hp
    cases' hp with B hB

    use B
    intro n hBn
    specialize hB n hBn

    -- multiply hB by c
    have mulrw (x y : ℝ) : x < y → c*x < c*y := by {
      intro h
      exact (mul_lt_mul_left hc).mpr h
    }
    apply mulrw at hB

    -- simplify the RHS of hB
    have h : c * (ε / c) = ε := by {
      field_simp
      ring
    }
    rw [h] at hB

    calc
    |c * a n - c * t| = |c * (a n - t)| := by ring_nf
    _ = c * |a n - t| := by {
      rw [abs_mul c (a n - t)]
      simp
      left
      exact LT.lt.le hc
    }
    _ < ε := by exact hB


/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rw [tendsTo_def] at *
  intro ε hε
  specialize h (ε/(-c))
  have hp : 0 < ε/(-c) := by {
    sorry
  }

  apply h at hp

  cases' hp with B hB

  use B
  intro n hBn
  specialize hB n hBn

  -- multiply hB by c
  have mulrw (x y : ℝ) : x < y → -c*x < -c*y := by {
    intro h
    have h_neg_c_pos : 0 < -c := by linarith
    exact (mul_lt_mul_left h_neg_c_pos).mpr h
  }
  apply mulrw at hB

  -- simplify the RHS of B
  have h : -c * (ε / -c) = ε := by {
    have c_ne_0 : c ≠ 0 := by exact LT.lt.ne hc
    field_simp
    ring_nf
    field_simp
    ring
  }
  rw [h] at hB

  calc
  |c * a n - c * t| = |c * (a n - t)| := by ring_nf
  _ = -c * |a n - t| := by {
    rw [abs_mul c (a n - t)]
    have h_abs_c : |c| = -c := by exact abs_of_neg hc
    simp
    rw [h_abs_c]
    ring
  }
  _ < ε := by exact hB

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  have c_cases : 0 < c ∨ 0 = c ∨ c < 0 := by exact lt_trichotomy 0 c
  cases' c_cases with c1 c2

  exact tendsTo_pos_const_mul h c1

  cases' c2 with c3 c4

  rw [tendsTo_def] at *
  intro ε hε
  use 0
  intro n hn
  rw [← c3]
  simp
  exact hε

  exact tendsTo_neg_const_mul h c4

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
  simpa [mul_comm] using tendsTo_const_mul c h -- wtf is this

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
    have h3 : TendsTo (fun n ↦ a n - b n + b n) (t + u) := by exact tendsTo_add h1 h2
    simpa using h3 -- wtf is this


/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  constructor
  intro h
  sorry
  sorry

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  sorry

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
sorry

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  sorry

end Section2sheet6
