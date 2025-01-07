/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-

# Subgroups and group homomorphisms

Like subsets of a type, a subgroup of a group isn't a type
and so it isn't a group! You can *make* a subgroup into a group,
but a group is a type and a subgroup is a term.

-/

section Subgroups

-- let `G` be a group
variable (G : Type) [Group G]

-- The type of subgroups of `G` is `Subgroup G`

-- Let `H` be a subgroup of `G`
variable (H : Subgroup G)

-- Just like subsets, elements of the subgroup `H` are terms `g` of type `G`
-- satisfying `g ∈ H`.

example (a b : G) (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by

  exact Subgroup.mul_mem H ha hb
  -- exact H.mul_mem ha hb -- equivalent
  -- You could instead do `apply H.mul_mem` and go on from there.

-- Try this one:

example (a b c : G) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    a * b⁻¹ * 1 * (a * c) ∈ H := by
  suffices (a * b⁻¹ * (a * c) ∈ H) by {
    group at this
    group
    exact this
  }
  apply H.mul_mem
  apply H.mul_mem
  exact ha
  exact Subgroup.inv_mem H hb
  apply H.mul_mem
  exact ha
  exact hc

/-

## Lattice notation for sub-things

Given two subgroups of a group, we can look at their intersection
(which is a subgroup) and their union (which in general isn't).
This means that set-theoretic notations such as `∪` and `∩` are not
always the right concepts in group theory. Instead, Lean uses
"lattice notation". The intersection of two subgroups `H` and `K` of `G`
is `H ⊓ K`, and the subgroup they generate is `H ⊔ K`. To say
that `H` is a subset of `K` we use `H ≤ K`. The smallest subgroup
of `G`, i.e., {e}, is `⊥`, and the biggest subgroup (i.e. G, but
G is a group not a subgroup so it's not G) is `⊤`.

-/

-- intersection of two subgroups, as a subgroup
example (H K : Subgroup G) : Subgroup G := H ⊓ K
-- note that H ∩ K *doesn't work* because `H` and `K` don't
-- have type `Set G`, they have type `Subgroup G`. Lean
-- is very pedantic!

example (H K : Subgroup G) (a : G) : a ∈ H ⊓ K ↔ a ∈ H ∧ a ∈ K := by
  -- true by definition!
  rfl

-- Note that `a ∈ H ⊔ K ↔ a ∈ H ∨ a ∈ K` is not true; only `←` is true.
-- Take apart the `Or` and use `exact?` to find the relevant lemmas.
example (H K : Subgroup G) (a : G) : a ∈ H ∨ a ∈ K → a ∈ H ⊔ K := by
  intro h
  cases' h with h1 h2
  exact Subgroup.mem_sup_left h1
  exact Subgroup.mem_sup_right h2

end Subgroups

/-

## Group homomorphisms

The notation is `→*`, i.e. "function which preserves `*`."

-/

section Homomorphisms

-- Let `G` and `H` be groups
variable (G H : Type) [Group G] [Group H]

-- Let `φ` be a group homomorphism
variable (φ : G →* H)

-- `φ` preserves multiplication

example (a b : G) : φ (a * b) = φ a * φ b :=
  φ.map_mul a b -- this is the term: no `by`

example (a b : G) : φ (a * b⁻¹ * 1) = φ a * (φ b)⁻¹ * 1 := by
  -- if `φ.map_mul` means that `φ` preserves multiplication
  -- (and you can rewrite with this) then what do you think
  -- the lemmas that `φ` preserves inverse and one are called?
  suffices (φ (a * b⁻¹) = φ a * (φ b)⁻¹) by {
    group
    group at this
    exact this
  }
  calc
    φ (a * b⁻¹) = φ a * φ (b⁻¹) := φ.map_mul a b⁻¹
    _ = φ a * (φ b)⁻¹ := by {
      congr
      exact φ.map_inv b
    }

-- Group homomorphisms are extensional: if two group homomorphisms
-- are equal on all inputs the they're the same.

example (φ ψ : G →* H) (h : ∀ g : G, φ g = ψ g) : φ = ψ := by
  ext x
  specialize h x
  exact h

end Homomorphisms

namespace DihedralGroup

-- s*s = 1
example (n: ℕ) : (sr 0: DihedralGroup n) * (sr 0) = (r 0) := by simp

-- sr r = r^-1 sr
example (n: ℕ) : (sr 1: DihedralGroup n) * (r 1) = r (-1) * (sr 1) := by simp

example (n: ℕ) : (sr 2: DihedralGroup n) * (r 1) = r (-1) * (sr 2) := by simp

-- x r = r^-1 x where x = sr k
example (n k: ℕ) : (sr k: DihedralGroup n) * (r 1) = r (-1) * (sr k) := by simp

-- { r0 } is a subgroup of D8
example : Subgroup (DihedralGroup 4) where
  carrier := {x | x = r 0}
  mul_mem' := by
    simp
    rfl
  one_mem' := by
    simp
    rfl
  inv_mem' := by
    simp
    rfl

example : Subgroup (DihedralGroup 4) where
  carrier := {x | x = r 0 ∨ x = sr 0 }
  mul_mem' := by
    intros a b ha hb
    simp at ha
    simp at hb
    simp
    aesop
  one_mem' := by
    simp
    left
    rfl
  inv_mem' := by
    intros x y
    simp at y
    cases' y with l r
    simp
    left
    rw [l]
    rfl
    simp
    right
    rw [r]
    rfl

example : Subgroup (DihedralGroup 4) where
  carrier := { r 0, r 2, sr 0, sr 2 }
  mul_mem' := by
    simp
    decide
  one_mem' := by
    simp
    decide
  inv_mem' := by
    simp
    decide

example : Subgroup (DihedralGroup 4) where
  carrier := { r 0, r 2, sr 1, sr 3 }
  mul_mem' := by
    simp
    decide
  one_mem' := by
    simp
    decide
  inv_mem' := by
    simp
    decide

example : Subgroup (DihedralGroup 6) where
  carrier := { r 0 } ∪ { sr 0 }
  mul_mem' := by aesop
  one_mem' := by aesop
  inv_mem' := by aesop

-- The subgroup of even powers of r
example (n : ℕ): Subgroup (DihedralGroup n) where
  carrier := { r (2*i) | i : ZMod n }
  mul_mem' := by
    intros a b ha hb
    simp at ha
    simp at hb
    cases' ha with i ha
    cases' hb with j hb
    rw [← ha, ← hb]
    simp
    use i + j
    ring
  one_mem' := by
    use 0
    simp
    rfl
  inv_mem' := by
    intros x hx
    simp at hx
    cases' hx with i hi
    use -i
    rw [← hi]

    have rr : (r (2 * i))⁻¹ = r (- (2 * i)) := by
      rfl

    rw [rr]
    ring_nf


def A : Subgroup (DihedralGroup 4) where
  carrier := { r i | i : ZMod 4 }
  mul_mem' := by
    intros a b
    fin_cases a <;> fin_cases b <;> decide
  one_mem' := by decide
  inv_mem' := by
    intros a
    fin_cases a <;> decide

theorem mem_f4_iff (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  fin_cases i <;> decide


theorem mem_z4_iff (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  change Fin 4 at i
  exact mem_f4_iff i

theorem mem_A_iff' (g : DihedralGroup 4) : g ∈ A ↔ g ∈ { r i | i : ZMod 4 } := Iff.rfl

theorem mem_A_iff (g : DihedralGroup 4) : g ∈ A ↔ g = r 0 ∨ g = r 1 ∨ g = r 2 ∨ g = r 3:= by {
  rw [mem_A_iff']
  fin_cases g <;> decide
}

def C_A : Subgroup (DihedralGroup 4) := Subgroup.centralizer A

example (G : Type) [Group G] (H : Subgroup G) : Subgroup.centralizer H ≤ Subgroup.normalizer H := by {
  intros g g_centralizes_h
  have ginv_centralizes_h : g⁻¹ ∈ Subgroup.centralizer H := by {
    exact Subgroup.inv_mem (Subgroup.centralizer ↑H) g_centralizes_h
  }
  have conj_by_ginv' (h : G) : h ∈ H → g⁻¹ * h * g ∈ H := by {
    intro hh
    specialize ginv_centralizes_h h
    rw [←ginv_centralizes_h]
    simp
    exact hh
    exact hh
  }
  rw [Subgroup.mem_centralizer_iff] at g_centralizes_h
  rw [Subgroup.mem_normalizer_iff]
  intros h
  constructor
  intros hh
  have rw1 := g_centralizes_h h hh
  rw [← rw1]
  group
  exact hh
  intros h'
  have spec := conj_by_ginv' (g * h * g⁻¹) h'
  group at spec
  exact spec
}




-- example 2 on page 50
theorem A_le_CA : A ≤ C_A := by
  intros a ha
  intros b hb
  simp only [Subgroup.mem_carrier, SetLike.mem_coe] at hb
  rw [mem_A_iff] at ha
  rw [mem_A_iff] at hb
  cases ha <;> cases hb <;> aesop

theorem A_le_CA_carrier : A.carrier ≤ C_A.carrier := by
  exact A_le_CA


theorem ri_in_CA (i : ZMod 4) : r i ∈ C_A := by
  apply A_le_CA
  rw [mem_A_iff]
  fin_cases i <;> decide

theorem s_not_in_CA : (sr 0) ∉ C_A := by
  intro hs
  specialize hs (r 1)
  simp at hs
  have t : ((-1 : ZMod 4) = 1) -> False := by decide
  apply t
  apply hs
  rw [mem_A_iff]
  simp only [r.injEq, true_or, or_true]

example (i : ZMod 4) : (sr i ∉ C_A) := by
  by_contra rs_i_in_CA
  have r_i_inv_in_CA := ri_in_CA (-i)
  have mul := Subgroup.mul_mem C_A rs_i_in_CA r_i_inv_in_CA
  simp at mul
  apply s_not_in_CA
  exact mul

theorem A_complement_is_sr (x : DihedralGroup 4) (hx : x ∉ A) : ∃ i, x = sr i := by
  cases' x with i i
  exfalso
  have spec := mem_A_iff' (r i)
  rw [spec] at hx
  simp at hx
  use i

theorem A_le_CA' : C_A.carrier ≤ A.carrier := by
  intro x x_in_CA
  by_contra x_not_in_A
  have spec := A_complement_is_sr x x_not_in_A
  cases' spec with i x_eq_sr_i
  have r_neg_i_in_CA := ri_in_CA (-i)
  have prod_in_CA := Subgroup.mul_mem C_A x_in_CA r_neg_i_in_CA
  rw [x_eq_sr_i] at prod_in_CA
  simp at prod_in_CA
  apply s_not_in_CA
  exact prod_in_CA


theorem A_eq_CA_carrier : A.carrier = C_A.carrier := by {
  exact le_antisymm A_le_CA_carrier A_le_CA'
}

theorem A_eq_CA : A = C_A := by {
  ext a
  rw [← Subgroup.mem_carrier]
  rw [← Subgroup.mem_carrier]
  have h1 := Eq.le A_eq_CA_carrier
  have h2 := Eq.le A_eq_CA_carrier.symm
  constructor
  intro ha
  exact h1 (h2 (h1 ha))
  intro ha
  exact h2 (h1 (h2 ha))
}


example : (1 : ZMod 4) ≠ -1 := by decide
