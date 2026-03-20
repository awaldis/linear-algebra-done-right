import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/-!
# Exercise 1C.7 - Prove or give a counterexample: If 𝑈 is a nonempty subset of
# 𝐑² such that 𝑈 is closed under addition and under taking additive inverses
# (meaning −𝑢 ∈ 𝑈 whenever 𝑢 ∈ 𝑈), then 𝑈 is a subspace of 𝐑².
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/

-------------------------------------------------------------------------------
-- Define a subset of ℝ² that provides a counterexample - namely, all the real
-- numbers that are also integers.
-------------------------------------------------------------------------------
def intPairsSubset : Set (Fin 2 → ℝ) := {v | ∀ i, ∃ n : ℤ, v i = ↑n }

-----------------------------------------------------------------------------
-- Closed under addition.
-- If each component of v and w is an integer, then each component of
-- v + w is also an integer (sum of integers is an integer).
-----------------------------------------------------------------------------
theorem intPairs_add_closed {v w : Fin 2 → ℝ}
                                  (h_v_in_subset : v ∈ intPairsSubset)
                                  (h_w_in_subset : w ∈ intPairsSubset) :
                                     v + w ∈ intPairsSubset := by
  unfold intPairsSubset at *
  simp only [Set.mem_setOf_eq] at *

  -- Move the universally quantified i from the goal to the context.
  intro i

  -- Specialize the universal in h_v_in_subset
  have h_exist_n_st_v_i_eq_n : ∃ (n:ℤ), v i = ↑n := h_v_in_subset i

  -- Unpack into witness n and proof that v i = ↑n
  rcases h_exist_n_st_v_i_eq_n with ⟨n, h_v_i_eq_n⟩

  -- Same idea for w and m but use obtain shortcut.
  obtain ⟨m, h_w_i_eq_m⟩ := h_w_in_subset i

  use n + m
  simp only [Pi.add_apply]
  simp only [h_v_i_eq_n, h_w_i_eq_m]
  have h_cast : (↑((n + m): ℤ) : ℝ) = (↑(n:ℤ):ℝ) + (↑(m:ℤ):ℝ) :=
                                                            Int.cast_add n m
  rw [h_cast]

-----------------------------------------------------------------------------
-- Closed under additive inverse.
-----------------------------------------------------------------------------
-- TBD

-----------------------------------------------------------------------------
-- NOT closed under scalar multiplication.
-----------------------------------------------------------------------------
-- TBD
