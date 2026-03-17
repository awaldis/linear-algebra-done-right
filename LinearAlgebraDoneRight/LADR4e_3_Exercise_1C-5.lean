import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false

/-!
# Exercise 1C.5 - Is 𝐑² a subspace of the complex vector space 𝐂²?
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/

def R2_subset_of_C2 : Set (Fin 2 → ℂ) := {v | ∀ i, (v i).im = 0}

theorem R2_not_subspace_of_C2 :
  ¬ ∃ (S : Submodule ℂ (Fin 2 → ℂ)), (S :Set (Fin 2 → ℂ)) = R2_subset_of_C2 := by
  intro ⟨S, hS⟩

  -- Prove (i,0) is not in the subspace set.
  have h_i_0_not_in_set : ¬![Complex.I, 0] ∈ R2_subset_of_C2 := by
    unfold R2_subset_of_C2
    simp only [Set.mem_setOf_eq, not_forall]
    use 0
    simp [Matrix.cons_val_zero]

  -- Prove (i,0) is in the subspace set.
  have h_i_0_in_set : ![Complex.I, 0] ∈ R2_subset_of_C2 := by

    have h_1_0_in_subspace : ![1,0] ∈ S := by
      have : ![1,0] ∈ R2_subset_of_C2 := by simp[R2_subset_of_C2]
      rw [← hS] at this
      rw [SetLike.mem_coe] at this
      exact this

    have h_i_0_in_subspace : ![Complex.I, 0] ∈ S := by
      have h_i_smul_1 : Complex.I • ![1,0] ∈ S :=
                                        S.smul_mem Complex.I h_1_0_in_subspace
      have h_i_smul_1_eq_i : Complex.I • ![1, 0] = ![Complex.I, 0] := by
        ext i; fin_cases i <;> simp
      rwa [h_i_smul_1_eq_i] at h_i_smul_1
    rw [← hS]
    rw [SetLike.mem_coe]
    exact h_i_0_in_subspace

  -- Assuming S is a subspace leads to a contradiction.
  exact absurd h_i_0_in_set h_i_0_not_in_set
