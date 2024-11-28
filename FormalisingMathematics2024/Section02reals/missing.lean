import Lean
import Mathlib.Tactic
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Tactic.Positivity

open Lean

-- field_simp deficiency

example (c ε: ℝ) (hc : 0 < c) : c * (ε / c) = ε := by {
  field_simp
  ring
}

example (c ε: ℝ) (hc : c < 0) : -c * (ε / -c) = ε := by {
  field_simp [show c ≠ 0 by exact LT.lt.ne hc]
  ring
}


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

-- Heather Macbeth

syntax (name := cancelDischarger) "cancel_discharger " : tactic
syntax (name := cancelAux) "cancel_aux " term " at " term : tactic
syntax (name := cancel) "cancel " term " at " term : tactic

macro_rules | `(tactic| cancel_discharger) => `(tactic | positivity)
macro_rules
| `(tactic| cancel_discharger) =>`(tactic | fail "cancel failed, could not verify the following side condition:")

/-! ### powers -/
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := lt_of_pow_lt_pow (n := $a) (by cancel_discharger) $(mkIdent h))
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := le_of_pow_le_pow (n := $a) (by cancel_discharger) (by cancel_discharger) $(mkIdent h))
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := pow_eq_zero (n := $a) $(mkIdent h))


/-! ### multiplication, LHS and RHS -/
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := mul_left_cancel₀ (a := $a) (by cancel_discharger) $(mkIdent h))
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := mul_right_cancel₀ (b := $a) (by cancel_discharger) $(mkIdent h))
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := le_of_mul_le_mul_left (a := $a) $(mkIdent h) (by cancel_discharger))
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := le_of_mul_le_mul_right (a := $a) $(mkIdent h) (by cancel_discharger))
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := lt_of_mul_lt_mul_left (a := $a) $(mkIdent h) (by cancel_discharger))
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := lt_of_mul_lt_mul_right (a := $a) $(mkIdent h) (by cancel_discharger))

/-! ### multiplication, just LHS -/
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := pos_of_mul_pos_right (a := $a) $(mkIdent h) (by cancel_discharger))
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := pos_of_mul_pos_left (b := $a) $(mkIdent h) (by cancel_discharger))
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := nonneg_of_mul_nonneg_right (a := $a) $(mkIdent h) (by cancel_discharger))
macro_rules
| `(tactic| cancel_aux $a at $h) =>
  let h := h.raw.getId
  `(tactic | replace $(mkIdent h):ident := nonneg_of_mul_nonneg_left (b := $a) $(mkIdent h) (by cancel_discharger))

-- TODO to trigger this needs some `guard_hyp` in the `cancel_aux` implementations
elab_rules : tactic
  | `(tactic| cancel $a at $_) => do
  let goals ← Elab.Tactic.getGoals
  let goalsMsg := MessageData.joinSep (goals.map MessageData.ofGoal) m!"\n\n"
  throwError "cancel failed: no '{a}' to cancel\n{goalsMsg}"

-- TODO build in a `try change 1 ≤ _ at h` to upgrade the `0 < _` result in the case of Nat
macro_rules | `(tactic| cancel $a at $h) => `(tactic| cancel_aux $a at $h; try apply $h)

-- https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3
  linarith
