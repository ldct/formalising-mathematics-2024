/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet3
-- import the definition of `TendsTo` from a previous sheet

namespace Section2sheet5

open Section2sheet3solutions

-- you can maybe do this one now
theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  rw [tendsTo_def]
  rw [tendsTo_def] at ha
  intro ε hε
  specialize ha ε hε
  cases ha with | intro B hB => {
    use B
    intro n
    intro hbn
    specialize hB n hbn
    rw [← abs_neg]
    ring_nf
    exact hB
  }

example (a b : ℝ) : |a+b| ≤ |a| + |b| := by exact abs_add a b

example (a b c : ℝ) : a ≤ b → b < c → a < c := by exact fun a_1 a_2 ↦ gt_of_gt_of_ge a_2 a_1

-- example (a b c d : ℝ) : |a| ≤ b → |c| ≤ d → |a+c| ≤ (b+d) := by exact?

/-
`tendsTo_add` is the next challenge. In a few weeks' time I'll
maybe show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful.
-/
/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) :=
by
  rw [tendsTo_def]
  rw [tendsTo_def] at ha
  rw [tendsTo_def] at hb
  intro ε hε

  specialize ha (ε/3)
  have h1 : (0 < ε/3) := by linarith
  apply ha at h1
  cases' h1 with B1 hB1

  specialize hb (ε/3)
  have h2 : (0 < ε/3) := by linarith
  apply hb at h2
  cases' h2 with B2 hB2

  use (max B1 B2)
  intro n n_ge

  specialize hB1 n
  specialize hB2 n

  have hn1 : (B1 ≤ n) := by {
    apply le_of_max_le_left at n_ge
    exact n_ge
  }

  have hn2 : (B2 ≤ n) := by {
    apply le_of_max_le_right at n_ge
    exact n_ge
  }

  apply hB1 at hn1
  apply hB2 at hn2

  calc
    |a n + b n - (t + u)| = |(a n - t) + (b n - u)| := by ring_nf
    _ ≤ |a n - t| + |(b n - u)| := by exact abs_add (a n - t) (b n - u)
    _ < ε := by linarith


/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by

  -- this one follows without too much trouble from earlier results.
  apply tendsTo_neg at hb
  apply tendsTo_add ha hb

end Section2sheet5
