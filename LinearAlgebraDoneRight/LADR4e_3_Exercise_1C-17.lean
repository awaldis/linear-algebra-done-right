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
-- Define what it means to be the sum of two subspaces.
-------------------------------------------------------------------------------
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
theorem sum_of_subspaces_associative ( V₁ V₂ V₃ : Submodule 𝔽 V ) :
                          sum2_Subspaces (sum2_Subspaces V₁ V₂) V₃ =
                          sum2_Subspaces V₁ (sum2_Subspaces V₂ V₃) := by
  ext x
  constructor
  · -- (V₁ + V₂) + V₃ → V₁ + (V₂ + V₃)
    intro h_in_the_sum_of_sumV₁V₂_V₃
    rcases h_in_the_sum_of_sumV₁V₂_V₃ with ⟨sum_v₁_v₂, v₃,
                                            h_sum_v₁_v₂_in_sumset_V₁_V₂,
                                            h_v₃_in_V₃, h_sum_v₁v₂_v₃⟩
    rcases h_sum_v₁_v₂_in_sumset_V₁_V₂ with ⟨v₁, v₂,
                                            h_v₁_in_V₁,
                                            h_v₂_in_V₂, h_sum_v₁_v₂⟩
    rw[h_sum_v₁_v₂] at h_sum_v₁v₂_v₃
    rw [h_sum_v₁v₂_v₃]

    use v₁, v₂ + v₃

    constructor
    · exact h_v₁_in_V₁
    · constructor
      · use v₂, v₃
      · ac_rfl

  · -- V₁ + (V₂ + V₃) → (V₁ + V₂) + V₃
    intro h_in_the_sum_of_sumV₁_V₂V₃
    rcases h_in_the_sum_of_sumV₁_V₂V₃ with ⟨v₁, sum_v₂_v₃, h_v₁_in_V₁,
                                            h_sum_v₂_v₃_in_sumset_V₂_V₃,
                                            h_sum_v₁_v₂v₃⟩
    rcases h_sum_v₂_v₃_in_sumset_V₂_V₃ with ⟨v₂, v₃,
                                            h_v₂_in_V₂,
                                            h_v₃_in_V₃, h_sum_v₂_v₃⟩
    rw[h_sum_v₂_v₃] at h_sum_v₁_v₂v₃
    rw [h_sum_v₁_v₂v₃]

    use v₁ + v₂, v₃

    constructor
    · use v₁, v₂
    · constructor
      · exact h_v₃_in_V₃
      · ac_rfl
