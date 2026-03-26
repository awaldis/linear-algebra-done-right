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
