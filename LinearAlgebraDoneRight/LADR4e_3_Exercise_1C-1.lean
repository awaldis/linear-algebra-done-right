import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

/-!
# Exercise 1C.1 - For each of the following subsets of 𝔽³, determine whether it
# is a subspaceof 𝔽³.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]
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
