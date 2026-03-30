import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/-!
# Exercise 1C.16 - Is the operation of addition on the subspaces of 𝑉
# commutative? In other words, if 𝑈 and 𝑊 are subspaces of 𝑉, is 𝑈 + 𝑊 = 𝑊 + 𝑈?
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
-------------------------------------------------------------------------------
-- Define what it means to be in the set of the sum of two subspaces.
-------------------------------------------------------------------------------
def sum2_SubspacesSet ( U W : Submodule 𝔽 V ) : Set V :=
  {x | ∃ u w : V, u ∈ U ∧ w ∈ W ∧ x = u + w}

-----------------------------------------------------------------------------
-- The answer to the exercise is yes and here is the proof.
------------------------------------------------------------------------------
theorem sum_of_subspaces_commutative ( U W : Submodule 𝔽 V ) :
                            sum2_SubspacesSet U W = sum2_SubspacesSet W U := by
  unfold sum2_SubspacesSet at *
  ext x
  constructor
  · -- U + W → W + U
    intro h_in_the_sum_of_subspaces
    simp only [Set.mem_setOf_eq] at *
    rcases h_in_the_sum_of_subspaces with ⟨u, w, h_u_in_U, h_w_in_W, h_sum_u_w⟩
    use w, u
    rw [h_sum_u_w, add_comm]
    exact ⟨h_w_in_W, h_u_in_U, rfl ⟩

  · -- W + U → U + W
    intro h_in_the_sum_of_subspaces
    simp only [Set.mem_setOf_eq] at *
    rcases h_in_the_sum_of_subspaces with ⟨w, u, h_w_in_W, h_u_in_U, h_sum_w_u⟩
    use u, w
    rw [h_sum_w_u, add_comm]
    exact ⟨h_u_in_U, h_w_in_W, rfl ⟩
