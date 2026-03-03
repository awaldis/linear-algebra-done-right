import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false

/-!
# Exercise 1C.1 - For each of the following subsets of 𝔽³, determine whether it
# is a subspaceof 𝔽³.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]

-----------------------------------------------------------------------------
-- Exercise (a)
-- Yes, this is a subspace. All the elements of the set meet the conditions.
-----------------------------------------------------------------------------
def Set_1a : Set (Fin 3 → 𝔽) := {v | (v 0) + (2 * v 1) + (3 * v 2) = 0}

theorem axler_1C_1a : ∃ W : Submodule 𝔽 (Fin 3 → 𝔽), (W : Set (Fin 3 → 𝔽))
                                                                  = Set_1a := by
  use {
    carrier := Set_1a
    zero_mem' := by
      -- Goal: 0 ∈ Set_1a
      unfold Set_1a at *
      -- New goal: 0 ∈ {v | (v 0) + (2 * v 1) + (3 * v 2) = 0}
      simp only [Set.mem_setOf_eq] at *
      -- New goal: (0 0) + (2 * 0 1) + (3 * 0 2) = 0
      simp only [Pi.zero_apply]
      -- New goal: 0 + (2 * 0) + (3 * 0) = 0
      ring
    add_mem' {a b} ha hb := by
      -- Goal: a + b ∈ Set_1a
      unfold Set_1a at *
      -- New goal: a + b ∈ {v | (v 0) + (2 * v 1) + (3 * v 2) = 0}
      simp only [Set.mem_setOf_eq] at *
      -- New goal: (a + b) 0 + (2 * (a + b) 1) + (3 * (a + b) 2) = 0
      simp only [Pi.add_apply]
      -- New goal: (a 0 + b 0) + (2 * (a 1 + b 1)) + (3 * (a 2 + b 2)) = 0
      calc (a 0 + b 0) + (2 * (a 1 + b 1)) + (3 * (a 2 + b 2))
         =   (a 0 + (2 * a 1) + (3 * a 2))
           + (b 0 + (2 * b 1) + (3 * b 2)) := by ring
       _ = 0 + 0 := by rw [ha, hb]
       _ = 0 := by ring
    smul_mem' c v hv := by
       -- Goal: c • v ∈ Set_1a
       unfold Set_1a at *
       -- New goal: c • v ∈ {v | (v 0) + (2 * v 1) + (3 * v 2) = 0}
       simp only [Set.mem_setOf_eq] at *
       -- New goal: ((c • v) 0) + (2 * (c • v) 1) + (3 * (c • v) 2) = 0
       simp only [Pi.smul_apply]
       -- New goal: (c • v 0) + (2 * c • v 1) + (3 * c • v 2) = 0
       simp only [smul_eq_mul]
       -- New goal:
       --   (c * v 0) + (2 * (c * v 1)) + (3 * (c * v 2)) = 0
       calc (c * v 0) + (2 * (c * v 1)) + (3 * (c * v 2))
          = c * ((v 0) + (2 * v 1) + (3 * v 2)) := by ring
        _ = c * 0                               := by rw [hv]
        _ = 0                                   := by ring
  }
  rfl

-----------------------------------------------------------------------------
-- Exercise (b)
-- NOT a subspace. Assuming that a set with this definition is a subspace of
-- 𝔽³ leads to a contradiction.
-----------------------------------------------------------------------------
section CharZeroExercise
-- For this exercise we need to make 𝔽 a field of characteristic 0 (e.g., ℚ, ℝ, ℂ).
-- This excludes finite fields like GF(2), GF(3), GF(p) and their extensions.
variable [CharZero 𝔽]

def Set_1b : Set (Fin 3 → 𝔽) := {v | (v 0) + (2 * v 1) + (3 * v 2) = 4}

theorem axler_1C_1b :
    ¬∃ S : Submodule 𝔽 (Fin 3 → 𝔽), (S : Set (Fin 3 → 𝔽)) = Set_1b := by
  -- "¬" makes the goal False
  rintro ⟨S, hS⟩
  -- "zero_mem" proves that the zero vector must be in any submodule,
  -- therefore it's in this one as well.
  have h_0vec_in_set : (0 : Fin 3 → 𝔽) ∈ (S : Set _) := S.zero_mem

  -- Replace the symbol "Set_1b" with it's definition.
  unfold Set_1b at *

  --Replace (h_0vec_in_set : 0 ∈ ↑S) with the details of the definition of set S.
  rw [hS, Set.mem_setOf_eq] at h_0vec_in_set
  -- Now (h_0vec_in_set : (0 0) + (2 * 0 1) + (3 * 0 2) = 4)

  -- Apply the zero function (0 i = 0)
  simp only [Pi.zero_apply] at h_0vec_in_set
  -- Now (h_0vec_in_set : 0 + (2 * 0) + (3 * 0) = 4)

  -- a * 0 = 0
  simp only [mul_zero] at h_0vec_in_set
  -- Now (h_0vec_in_set : 0 + 0 + 0 = 4)

  -- a + 0 = a
  simp only [add_zero] at h_0vec_in_set
  -- Now (h_0vec_in_set : 0 = 4)

  -- "norm_num" can prove that "0 = 4" is False in characteristic 0
  norm_num at h_0vec_in_set

end CharZeroExercise

-----------------------------------------------------------------------------
-- Exercise (c)
-- NOT a subspace. Assuming that a set with this definition is a subspace of
-- 𝔽³ leads to a contradiction.
-----------------------------------------------------------------------------
def Set_1c : Set (Fin 3 → 𝔽) := {x | (x 0) * (x 1) * (x 2) = 0}

theorem axler_1C_1c :
    ¬∃ S : Submodule 𝔽 (Fin 3 → 𝔽), (S : Set (Fin 3 → 𝔽)) = Set_1c := by
      -- "¬" makes the goal False
  rintro ⟨S, hS⟩

  -- Replace the symbol "Set_1c" with it's definition.
  unfold Set_1c at *

  -- Consider these two vectors in the set.
  have h_1_0_1_in_S : ![1, 0, 1] ∈ (S : Set (Fin 3 → 𝔽)) := by
    rw [hS, Set.mem_setOf_eq]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

  have h_0_1_0_in_S : ![0, 1, 0] ∈ (S : Set (Fin 3 → 𝔽)) := by
    rw [hS, Set.mem_setOf_eq]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

  -- Their sum must also be in the set.
  have h_sum := S.add_mem h_1_0_1_in_S h_0_1_0_in_S

  -- Prove their sum is ![1, 1, 1]
  have h_eq : ![1, 0, 1] + ![0, 1, 0] = (![1, 1, 1] : Fin 3 → 𝔽) := by
    ext i; fin_cases i <;> simp

  -- Replace ![1, 0, 1] + ![0, 1, 0] with ![1, 1, 1]
  rw [h_eq] at h_sum

  -- Rename h_sum
  have h_1_1_1_in_S := h_sum; clear h_sum

  --- ![1, 1, 1] not in set since 1*1*1 ≠ 0
  have h_1_1_1_not_in_S : ¬![1, 1, 1] ∈ (S : Set (Fin 3 → 𝔽)) := by
    rw [hS, Set.mem_setOf_eq]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

  -- The two contradictory hypotheses prove False.
  exact absurd h_1_1_1_in_S h_1_1_1_not_in_S

-----------------------------------------------------------------------------
-- Exercise (d)
-- Yes, this is a subspace. All the elements of the set meet the conditions.
-----------------------------------------------------------------------------
def Set_1d : Set (Fin 3 → 𝔽) := {v | (v 0) = (5 * v 2)}

theorem axler_1C_1d : ∃ W : Submodule 𝔽 (Fin 3 → 𝔽), (W : Set (Fin 3 → 𝔽))
                                                                  = Set_1d := by
  use {
    carrier := Set_1d
    zero_mem' := by
      -- Goal: 0 ∈ Set_1d
      unfold Set_1d at *
      -- New goal: 0 ∈ {v | (v 0) = (5 * v 2)}
      simp only [Set.mem_setOf_eq] at *
      -- New goal: (0 0) = (5 * 0 2)
      simp only [Pi.zero_apply]
      -- New goal: 0 = (5 * 0)
      ring
    add_mem' {a b} ha hb := by
      -- Goal: a + b ∈ Set_1d
      unfold Set_1d at *
      -- New goal: a + b ∈ {v | (v 0) = (5 * v 2)}
      simp only [Set.mem_setOf_eq] at *
      -- New goal: (a + b) 0 = (5 * (a + b) 2)
      simp only [Pi.add_apply]
      -- New goal: (a 0 + b 0) = (5 * (a 2 + b 2))
      calc (a 0 + b 0)
         = (5 * a 2) + (5 * b 2) := by rw [ha, hb]
       _ = (5 * (a 2 + b 2))     := by ring
    smul_mem' c v hv := by
       -- Goal: c • v ∈ Set_1d
       unfold Set_1d at *
       -- New goal: c • v ∈ {v | (v 0) = (5 * v 2)}
       simp only [Set.mem_setOf_eq] at *
       -- New goal: ((c • v) 0) = (5 * (c • v) 2)
       simp only [Pi.smul_apply]
       -- New goal: (c • v 0) = (5 * c • v 2)
       simp only [smul_eq_mul]
       -- New goal:
       --   (c * v 0) = (5 * (c * v 2))
       calc (c * v 0)
         = (c * (5 * v 2))  := by rw [hv]
        _ = (5 * (c * v 2)) := by ring
  }
  rfl
