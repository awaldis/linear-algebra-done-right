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
-- Show that if we assume the the set is a subspace then scalar multiplication
-- can result in an element that is NOT in the set.
-----------------------------------------------------------------------------
theorem intPairs_not_subspace :
  ¬ ∃ (S : Submodule ℝ  (Fin 2 → ℝ)), (S :Set (Fin 2 → ℝ)) =
                                                 intPairsSubset := by
  intro ⟨S, hS⟩

  -- Prove (-0.5,0) IS NOT in the subspace set.
  have h_half_0_not_in_set : ¬![0.5, 0] ∈ intPairsSubset := by
    unfold intPairsSubset; simp only [Set.mem_setOf_eq]
    intro h_there_exists_an_n
    specialize h_there_exists_an_n 0
    obtain ⟨int, h_half_eq_int⟩ := h_there_exists_an_n
    simp [Matrix.cons_val_zero] at h_half_eq_int

    -- Show that ↑int (which is equal to 0.5) is greater than zero and less than
    -- one.  This is fine in the real numbers.  Then cast the inequalities to
    -- integers to get the false implication that there is an integer greater
    -- than zero and less than one.  'omega' will detect this and flag it as
    -- false.
    have h_half_gt_zero_in_reals : (0:ℝ) < ↑int   := by linarith
    have h_half_lt_one_in_reals : (↑int : ℝ) < 1 := by linarith

    have h_half_gt_zero_in_ints : (0 : ℤ) < int := by
                                        exact_mod_cast h_half_gt_zero_in_reals
    have h_half_lt_one_in_ints : int < (1 : ℤ) := by
                                        exact_mod_cast h_half_lt_one_in_reals
    omega

  -- Prove (-0.5,0) IS in the subspace set.
  have h_half_0_in_set : ![0.5, 0] ∈ intPairsSubset := by

    have h_1_0_in_subspace : ![1, 0] ∈ S := by
      have : ![1, 0] ∈ intPairsSubset := by
        unfold intPairsSubset; simp only [Set.mem_setOf_eq]
        intro i
        fin_cases i
        ·  use 1; norm_num
        ·  use 0; norm_num
      rw [← hS] at this; rwa [SetLike.mem_coe] at this

    have h_half_0_in_subspace : ![0.5, 0] ∈ S := by

      have h_smul_is_member : (0.5:ℝ) • ![1, 0] ∈ S :=
                                               S.smul_mem 0.5 h_1_0_in_subspace

      have h_smul_eq_half_0 : (0.5:ℝ) • ![(1:ℝ), 0] = ![0.5, 0] := by
        ext i
        fin_cases i <;> simp

      rwa [h_smul_eq_half_0] at h_smul_is_member

    rw [← hS]; rw [SetLike.mem_coe]
    exact h_half_0_in_subspace

  -- Assuming S is a subspace leads to a contradiction.
  exact absurd h_half_0_in_set h_half_0_not_in_set
