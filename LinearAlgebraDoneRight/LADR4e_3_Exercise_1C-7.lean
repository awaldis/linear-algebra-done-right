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
-- Our "U" will provide a counterexample that specifies a subset of ℝ² that
-- possesses the closure under addition and additive inverse properties but
-- fails closure under scalar multiplication.
--
-- In summary, the counterexample set will be all the vectors whose elements
-- consist only of real numbers that can be cast to integers.
--
-- Specifically, when every vector in ℝ² (Fin 2 → ℝ) is applied to every index
-- in Fin 2, the vector is considered a member of the subset only if both real
-- numbers produced are equivalent to some integer n coerced to a real number.
-------------------------------------------------------------------------------
def intPairsSubset : Set (Fin 2 → ℝ) := {v | ∀ i, ∃ (n:ℤ), v i = ↑n }

-----------------------------------------------------------------------------
-- Prove that the subset really is closed under addition.
-----------------------------------------------------------------------------
theorem intPairs_add_closed {vec1 vec2 : Fin 2 → ℝ}
                             (h_vec1_in_subset : vec1 ∈ intPairsSubset)
                             (h_vec2_in_subset : vec2 ∈ intPairsSubset) :
                              vec1 + vec2 ∈ intPairsSubset := by
  unfold intPairsSubset at *
  simp only [Set.mem_setOf_eq] at *

  -- Goal: ∀ (i : Fin 2), ∃ n, (vec1 + vec2) i = ↑n

  -- Move index from goal to context.
  intro (i:Fin 2)

  -- Unpack input hypotheses.
  obtain ⟨int1, h_vec1_i_eq_int1⟩ := h_vec1_in_subset i
  obtain ⟨int2, h_vec2_i_eq_int2⟩ := h_vec2_in_subset i

  use int1 + int2
  simp only [Pi.add_apply]
  simp only [h_vec1_i_eq_int1, h_vec2_i_eq_int2]

  -- Prove the cast can be done either before or after addition.
  have h_cast : (↑((int1 + int2): ℤ) : ℝ) = (↑(int1:ℤ):ℝ) + (↑(int2:ℤ):ℝ) :=
                                                        Int.cast_add int1 int2
  rw [h_cast]

-----------------------------------------------------------------------------
-- Prove that the additive inverse of every element of 'intPairsSubset' is
-- also in 'intPairsSubset'.
-----------------------------------------------------------------------------
theorem intPairs_add_inv_exists {vec : Fin 2 → ℝ}
                                (h_vec_in_subset : vec ∈ intPairsSubset) :
                                -vec ∈ intPairsSubset := by
  unfold intPairsSubset at *
  simp only [Set.mem_setOf_eq] at *

  -- Goal: ∀ (i : Fin 2), ∃ n, (-vec) i = ↑n

  -- Move index from goal to context.
  intro (i:Fin 2)

  -- Unpack input hypotheses.
  obtain ⟨int, h_vec_i_eq_int⟩ := h_vec_in_subset i

  use -int
  simp only [Pi.neg_apply]
  simp only [h_vec_i_eq_int]

  -- Prove the cast can be done either before or after negation.
  have h_cast : (↑(-(int: ℤ)) : ℝ) = -(↑(int:ℤ):ℝ) := Int.cast_neg int
  rw [h_cast]


-----------------------------------------------------------------------------
-- NOT closed under scalar multiplication.
-----------------------------------------------------------------------------
-- TBD
