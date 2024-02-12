/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C: Set X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext x
  constructor
  intro h
  cases' h with h1 h2
  exact h1
  exact h2
  intro h
  left
  exact h

example : A ∩ A = A := by
  ext x
  constructor
  intro h
  cases' h with h1 h2
  exact h1
  intro h
  constructor
  exact h
  exact h

example : A ∩ ∅ = ∅ := by
  ext x
  constructor
  intro h
  cases' h with h1 h2
  exact h2
  intro h
  cases' h

example : A ∪ univ = univ := by
  ext x
  constructor
  intro h
  triv
  intro h
  right
  exact h


example : A ⊆ B → B ⊆ A → A = B := by
  intro h1
  intro h2
  ext x
  constructor
  intro h3
  apply h1
  exact h3
  intro h3
  apply h2
  exact h3

example : A ∩ B = B ∩ A := by
  ext x
  constructor
  intro h
  cases' h with h1 h2
  constructor
  exact h2
  exact h1
  intro h
  cases' h with h1 h2
  constructor
  exact h2
  exact h1

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext x
  constructor
  intro h
  cases' h with h1 h2
  cases' h2 with h3 h4
  constructor
  constructor
  exact h1
  exact h3
  exact h4
  intro h
  cases' h with h1 h2
  cases' h1 with h3 h4
  constructor
  exact h3
  constructor
  exact h4
  exact h2

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x
  constructor
  intro h
  cases' h with h1 h2
  left
  left
  exact h1
  cases' h2 with h3 h4
  left
  right
  exact h3
  right
  exact h4
  intro h
  cases' h with h1 h2
  cases' h1 with h3 h4
  left
  exact h3
  right
  left
  exact h4
  right
  right
  exact h2

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  intro h
  cases' h with h1 h2
  constructor
  left
  exact h1
  left
  exact h1
  constructor
  right
  cases' h2 with h3 h4
  exact h3
  right
  cases' h2 with h3 h4
  exact h4
  intro h
  cases' h with h1 h2

  cases' h1 with h3 h4
  left
  exact h3

  cases' h2 with h3 h5

  left
  exact h3

  right
  constructor
  exact h4
  exact h5

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext x
  constructor
  intro h
  cases' h with h1 h2

  cases' h2 with h3 h4
  left
  constructor
  exact h1
  exact h3

  right
  constructor
  exact h1
  exact h4

  intro h

  cases' h with h1 h2
  cases' h1 with h3 h4
  constructor
  exact h3
  left
  exact h4

  cases' h2 with h1 h3
  constructor
  exact h1
  right
  exact h3
