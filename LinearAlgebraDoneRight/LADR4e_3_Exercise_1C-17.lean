import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/-!
# Exercise 1C.17 - Is the operation of addition on the subspaces of 𝑉
# associative? In other words, if 𝑉1, 𝑉2, 𝑉3 are subspaces of 𝑉, is
# (𝑉1 + 𝑉2) + 𝑉3 = 𝑉1 + (𝑉2 + 𝑉3)?
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

def sum2_Subspaces (U W : Submodule 𝔽 V) : Submodule 𝔽 V where
  carrier := {x | ∃ u w : V, u ∈ U ∧ w ∈ W ∧ x = u + w}
  zero_mem' := by
    use 0, 0
    simp
  add_mem' := by
    intro v₁ v₂ h_v₁_in_sum h_v₂_in_sum
    rcases h_v₁_in_sum with ⟨u₁, w₁, h_u₁_in_U, h_w₁_in_W, h_sum_u₁_w₁⟩
    rcases h_v₂_in_sum with ⟨u₂, w₂, h_u₂_in_U, h_w₂_in_W, h_sum_u₂_w₂⟩
    use (u₁ + u₂)
    use (w₁ + w₂)
    constructor
    · exact add_mem h_u₁_in_U h_u₂_in_U
    · constructor
      · exact add_mem h_w₁_in_W h_w₂_in_W
      · rw [h_sum_u₁_w₁, h_sum_u₂_w₂]
        ac_rfl
  smul_mem' := by
    -- Prove closure under scalar multiplication
    intro c v h_v_in_sum
    rcases h_v_in_sum with ⟨u, w, h_u_in_U, h_w_in_W, h_sum_u_w⟩
    use (c • u)
    use (c • w)
    constructor
    · exact U.smul_mem c h_u_in_U
    · constructor
      · exact W.smul_mem c h_w_in_W
      · rw [h_sum_u_w]
        simp


-----------------------------------------------------------------------------
-- The answer to the exercise is yes and here is the proof.
------------------------------------------------------------------------------
theorem sum_of_subspaces_commutative ( V₁ V₂ V₃ : Submodule 𝔽 V ) :
                          sum2_Subspaces (sum2_Subspaces V₁ V₂) V₃ =
                          sum2_Subspaces V₁ (sum2_Subspaces V₂ V₃) := by
  --unfold sum2_Subspaces at *
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
