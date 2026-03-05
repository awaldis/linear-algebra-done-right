import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false

/-!
# Exercise 1C.2 - Verify all assertions about subspaces in Example 1.35.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]

-----------------------------------------------------------------------------
-- Exercise (a)
-- Show this set is a subspace if and only if b = 0.
-----------------------------------------------------------------------------
def set_2a (b : 𝔽) : Set (Fin 4 → 𝔽) := { x | x 2 = 5 * x 3 + b }

theorem subspace_iff_b_eq_zero (b : 𝔽) :
  (∃ (S : Submodule 𝔽 (Fin 4 → 𝔽)), (S : Set (Fin 4 → 𝔽)) = set_2a b)
                                                                  ↔ b = 0 := by
  constructor
  · -- Forward direction - If S is a subspace then b = 0
    intro ⟨S, hS⟩
    unfold set_2a at *
    -- Use the fact that the zero vector MUST be in the set to show that
    -- b MUST be zero.
    have h_0vec_in_set : (0 : Fin 4 → 𝔽) ∈ (S : Set _) := S.zero_mem
    rw [hS, Set.mem_setOf_eq] at h_0vec_in_set
    simp only [Pi.zero_apply] at h_0vec_in_set
    simp only [mul_zero] at h_0vec_in_set
    simp only [zero_add] at h_0vec_in_set
    exact h_0vec_in_set.symm

  · -- Reverse direction - If b = 0 then S is a subspace.
    intro h_b_eq_zero
    use {
    carrier := set_2a b
    zero_mem' := by
      unfold set_2a at *
      simp only [Set.mem_setOf_eq] at *
      simp only [Pi.zero_apply]
      subst h_b_eq_zero
      ring
    add_mem' {a b} ha hb := by
      unfold set_2a at *
      simp only [Set.mem_setOf_eq] at *
      simp only [Pi.add_apply]
      subst h_b_eq_zero
      calc a 2 + b 2
         = (5 * a 3 + 0) + (5 * b 3 + 0) := by rw [ha, hb]
       _ = 5 * (a 3 + b 3) + 0           := by ring
    smul_mem' c v hv := by
       unfold set_2a at *
       simp only [Set.mem_setOf_eq] at *
       simp only [Pi.smul_apply]
       simp only [smul_eq_mul]
       subst h_b_eq_zero
       calc c * v 2
          = c * (5 * v 3 + 0) := by rw [hv]
        _ = 5 * (c * v 3) + 0 := by ring
    }
    rfl
