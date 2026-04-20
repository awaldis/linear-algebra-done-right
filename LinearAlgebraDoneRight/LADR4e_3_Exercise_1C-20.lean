import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/-!
# Exercise 1C.20 - Find a subspace W of F⁴ such that F⁴ = U ⊕ W.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024

The code will show that W = {(0, x, 0, y) : x, y ∈ 𝔽} is a subspace that meets
criteria.
-/
variable {𝔽 : Type*} [Field 𝔽]

-- ═══════════════════════════════════════════════════════════════════════════
-- Define U = {(x, x, y, y) : x, y ∈ 𝔽} as a subspace of 𝔽⁴.
-- ═══════════════════════════════════════════════════════════════════════════
def U : Submodule 𝔽 (Fin 4 → 𝔽) where
  carrier := { v : Fin 4 → 𝔽 | (v 0 = v 1) ∧ (v 2 = v 3) }

  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    -- Goal: 0 = 0 ∧ 0 = 0
    exact ⟨rfl, rfl⟩

  -- Show that if a and b are both in U, then a + b is in U.
  -- Specifically, (a + b) 0 = (a + b) 1 and
  --               (a + b) 2 = (a + b) 3
  add_mem' := by
    intro a b h_a_in_set h_b_in_set
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    -- h_a_in_set : a 0 = a 1 ∧ a 2 = a 3
    -- h_b_in_set : b 0 = b 1 ∧ b 2 = b 3
    obtain ⟨h_a0_eq_a1, h_a2_eq_a3⟩ := h_a_in_set
    obtain ⟨h_b0_eq_b1, h_b2_eq_b3⟩ := h_b_in_set
    constructor
    · -- Goal: a 0 + b 0 = a 1 + b 1
      rw [h_a0_eq_a1, h_b0_eq_b1]
    · -- Goal: a 2 + b 2 = a 3 + b 3
      rw [h_a2_eq_a3, h_b2_eq_b3]

  -- Show that if u is in U and c ∈ 𝔽, then c • u is in U.
  smul_mem' := by
    intro c u h_u_in_set
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    obtain ⟨h_u0_eq_u1, h_u2_eq_u3⟩ := h_u_in_set
    constructor
    · -- Goal: c * u 0 = c * u 1
      rw [h_u0_eq_u1]
    · -- Goal: c * u 2 = c * u 3
      rw [h_u2_eq_u3]

-- ═══════════════════════════════════════════════════════════════════════════
-- Define W = {(0, x, 0, y) : x, y ∈ 𝔽} as a subspace of 𝔽⁴.
-- ═══════════════════════════════════════════════════════════════════════════
def W : Submodule 𝔽 (Fin 4 → 𝔽) where
  carrier := { v : Fin 4 → 𝔽 | (v 0 = 0) ∧ (v 2 = 0) }

  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    simp only [Pi.zero_apply]
    tauto

  -- Show that if a and b are both in U, then a + b is in U.
  -- Specifically, (a + b) 0 = 0 and
  --               (a + b) 2 = 0
  add_mem' := by
    intro a b h_a_in_set h_b_in_set
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *

    obtain ⟨h_a0_eq_0, h_a2_eq_0⟩ := (h_a_in_set : a 0 = 0 ∧ a 2 = 0)
    obtain ⟨h_b0_eq_0, h_b2_eq_0⟩ := (h_b_in_set : b 0 = 0 ∧ b 2 = 0)
    constructor
    · -- Goal: a 0 + b 0 = 0
      rw [h_a0_eq_0, h_b0_eq_0, zero_add]
    · -- Goal: a 2 + b 2 = 0
      rw [h_a2_eq_0, h_b2_eq_0, zero_add]

  -- Show that if u is in U and c ∈ 𝔽, then c • u is in U.
  smul_mem' := by
    intro c u h_u_in_set
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    obtain ⟨h_u0_eq_0, h_u2_eq_0⟩ := h_u_in_set
    constructor
    · -- Goal: c * u 0 = 0
      rw [h_u0_eq_0, mul_zero]
    · -- Goal: c * u 2 = 0
      rw [h_u2_eq_0, mul_zero]

-- ═══════════════════════════════════════════════════════════════════════════
-- Show that subspaces U and W intersect only at zero.  Therefore, their sum
-- is a direct sum by theorem 1.46.
-- ═══════════════════════════════════════════════════════════════════════════
theorem U_intersect_W_eq_zero :
  ∀ v : Fin 4 → 𝔽, (v ∈ U) ∧ (v ∈ W) → (v = 0) := by

  intro v ⟨h_v_in_U, h_v_in_W⟩

  unfold U at h_v_in_U
  unfold W at h_v_in_W

  obtain ⟨h_v0_eq_v1,   h_v2_eq_v3⟩   := h_v_in_U
  obtain ⟨h_v0_eq_zero, h_v2_eq_zero⟩ := h_v_in_W

  have h_v1_eq_zero : v 1 = 0 := by rw [h_v0_eq_v1.symm, h_v0_eq_zero ]
  have h_v3_eq_zero : v 3 = 0 := by rw [h_v2_eq_v3.symm, h_v2_eq_zero ]

  ext i
  simp only [Pi.zero_apply]
  fin_cases i <;> assumption

-- ═══════════════════════════════════════════════════════════════════════════
-- Show that the sum of subspaces U and W equal all of 𝔽⁴.  This is not
-- necessary to prove it's a direct sum, but is a requirement of the problem
-- statement.
-- ═══════════════════════════════════════════════════════════════════════════
theorem sum_U_W_eq_F4 :
  ∀ (v : Fin 4 → 𝔽), ∃ (u w : Fin 4 → 𝔽), (u ∈ U) ∧ (w ∈ W) ∧ (v = u + w) := by

  intro v

  -- Define our proposed members of U and W that will supposedly meet the
  -- criteria of the theorem.
  let u : Fin 4 → 𝔽 := fun i => match i with
    | 0 => v 0
    | 1 => v 0
    | 2 => v 2
    | 3 => v 2

  let w : Fin 4 → 𝔽 := fun i => match i with
    | 0 => 0
    | 1 => v 1 - v 0
    | 2 => 0
    | 3 => v 3 - v 2

  use u, w

  -- Break out the three AND clauses in the goal into three separate goals.
  refine ⟨ ?_, ?_, ?_⟩

  · -- Goal 1: u ∈ U
    unfold U
    constructor
    · rfl -- u 0 = u 1
    · rfl -- u 2 = u 3

  · -- Goal 2: w ∈ W
    unfold W
    constructor
    · rfl -- w 0 = 0
    · rfl -- w 2 = 0

  · -- Goal 3: v = u + w
    ext i
    fin_cases i
    · calc v 0 = v 0 + 0   := by ring
           _   = u 0 + w 0 := by simp [u, w]

    · calc v 1 = v 0 + (v 1 - v 0) := by ring
           _   = u 1 + w 1         := by simp [u, w]

    · calc v 2 = v 2 + 0   := by ring
           _   = u 2 + w 2 := by simp [u, w]

    · calc v 3 = v 2 + (v 3 - v 2) := by ring
           _   = u 3 + w 3         := by simp [u, w]
