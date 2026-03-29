import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/-!
# Exercise 1C.15 - Suppose 𝑈 is a subspace of 𝑉. What is 𝑈 + 𝑈?
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
-- Show that the sum of a subspace with itself is identical with the subspace
-- itself.
------------------------------------------------------------------------------
theorem sum_of_subspace_with_itself ( U : Submodule 𝔽 V ) :
                                            sum2_SubspacesSet U U = U := by
  unfold sum2_SubspacesSet at *
  ext x
  constructor

  · -- If an arbitrary vector is in the sum of identical subspaces then it is
    -- in that single subspace.
    intro h_in_the_sum_of_subspaces
    simp only [Set.mem_setOf_eq] at *
    rcases h_in_the_sum_of_subspaces with ⟨u, w, h_u_in_U, h_w_in_U, h_sum_u_w⟩
    rw [h_sum_u_w]
    exact U.add_mem h_u_in_U h_w_in_U

  · -- If an arbitrary vector is in a subspace then it is in the sum of that
    -- subspace with itself.
    intro h_in_the_single_subspace
    simp only [Set.mem_setOf_eq] at *
    use x, 0
    exact ⟨h_in_the_single_subspace, U.zero_mem, (add_zero x).symm⟩
