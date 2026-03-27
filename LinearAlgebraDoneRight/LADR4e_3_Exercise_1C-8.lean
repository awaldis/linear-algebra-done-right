import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/-!
# Exercise 1C.8 - Give an example of a nonempty subset 𝑈 of 𝐑² such that 𝑈 is
# closed underscalar multiplication, but 𝑈 is not a subspace of 𝐑².
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/

-------------------------------------------------------------------------------
-- Our "U" will provide a counterexample that specifies a subset of ℝ² that
-- possesses the closure under scalar multiplication property and fails under
-- vector addition.
--
-- Specifically, we will use the subset consisting of the x and y axis as the
-- counterexample.
-------------------------------------------------------------------------------
def x_Subset : Set (Fin 2 → ℝ) := {v | v 1 = 0}
def y_Subset : Set (Fin 2 → ℝ) := {v | v 0 = 0}

def unionSubset : Set (Fin 2 → ℝ) := x_Subset ∪ y_Subset

-----------------------------------------------------------------------------
-- Prove that the subset really is closed under scalar multiplication.
-----------------------------------------------------------------------------
theorem smul_closed (c:ℝ) {vec : Fin 2 → ℝ}
                          (h_vec_in_subset : vec ∈ unionSubset) :
                           c • vec ∈ unionSubset := by
  unfold unionSubset at *
  simp only [Set.mem_union] at *

  rcases h_vec_in_subset with h_on_x_axis | h_on_y_axis
  · left
    unfold x_Subset at *
    simp only [Set.mem_setOf_eq] at *
    simp only [Pi.smul_apply]
    rw [h_on_x_axis]
    rw [smul_eq_mul]
    ring

  · right
    unfold y_Subset at *
    simp only [Set.mem_setOf_eq] at *
    simp only [Pi.smul_apply]
    rw [h_on_y_axis]
    rw [smul_eq_mul]
    ring

-----------------------------------------------------------------------------
-- Show that if we assume the the set is a subspace then vector addition
-- can result in an element that is NOT in the set.
-----------------------------------------------------------------------------
theorem unionSubset_not_subspace :
  ¬ ∃ (S : Submodule ℝ  (Fin 2 → ℝ)), (S :Set (Fin 2 → ℝ)) =
                                                 unionSubset := by
  intro ⟨S, hS⟩

  ----------------------------------------------------------------------------
  -- Prove (1,1) IS NOT in the set (that is supposedly a subspace) according
  -- to the set builder definition.
  ----------------------------------------------------------------------------
  have h_1_1_not_in_set : ¬![1, 1] ∈ unionSubset := by
    unfold unionSubset at *
    simp only [Set.mem_union] at *

    -- Change NOR to AND
    push_neg
    constructor
    · intro h_in_x_Subset
      unfold x_Subset at *;  simp only [Set.mem_setOf_eq] at *
      simp [Matrix.cons_val_one] at h_in_x_Subset
    · intro h_in_y_Subset
      unfold y_Subset at *;  simp only [Set.mem_setOf_eq] at *
      simp [Matrix.cons_val_zero] at h_in_y_Subset

  ----------------------------------------------------------------------------
  -- Prove (1,1) IS in the set (that is supposedly a subspace) if we use the
  -- closure rules of subspaces.
  ----------------------------------------------------------------------------
  have h_1_1_in_set : ![1, 1] ∈ unionSubset := by

    have h_1_0_in_subspace : ![1, 0] ∈ S := by
      have : ![1, 0] ∈ unionSubset := by
        unfold unionSubset; left; unfold x_Subset; simp only [Set.mem_setOf_eq]
        simp
      rw [← hS] at this; rwa [SetLike.mem_coe] at this

    have h_0_1_in_subspace : ![0, 1] ∈ S := by
      have : ![0, 1] ∈ unionSubset := by
        unfold unionSubset; right; unfold y_Subset; simp only [Set.mem_setOf_eq]
        simp
      rw [← hS] at this; rwa [SetLike.mem_coe] at this

    have h_1_1_in_subspace : ![1, 1] ∈ S := by

      -- This is the crux of the proof.  Adding two elements in the subspace
      -- can result in an element that is outside the set definition.
      have h_sum_is_member: ![1, 0] + ![0, 1] ∈ S :=
                         S.add_mem h_1_0_in_subspace h_0_1_in_subspace

      have h_sum_eq_1_1 : ![(1:ℝ), 0] + ![0, 1] = ![1, 1] := by
        ext i
        fin_cases i <;> simp

      rwa [h_sum_eq_1_1] at h_sum_is_member

    rw [← hS]; rw [SetLike.mem_coe]
    exact h_1_1_in_subspace

  -- Assuming S is a subspace leads to a contradiction.
  exact absurd h_1_1_in_set h_1_1_not_in_set
