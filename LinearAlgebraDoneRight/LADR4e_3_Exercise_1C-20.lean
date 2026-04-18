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
-/
variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]

-- ═══════════════════════════════════════════════════════════════════════════
-- Define U = {(x, x, y, y) : x, y ∈ 𝔽}
-- ═══════════════════════════════════════════════════════════════════════════

/-- U is the subspace of 𝔽⁴ consisting of vectors (x, x, y, y).
    Equivalently, vectors where coordinate 0 = coordinate 1
    and coordinate 2 = coordinate 3. -/
def U : Submodule 𝔽 (Fin 4 → 𝔽) where
  carrier := { v : Fin 4 → 𝔽 | v 0 = v 1 ∧ v 2 = v 3 }

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
-- Define U = {(x, -x, y, -y) : x, y ∈ 𝔽}
-- ═══════════════════════════════════════════════════════════════════════════

/-- U is the subspace of 𝔽⁴ consisting of vectors (x, x, y, y).
    Equivalently, vectors where coordinate 0 = coordinate 1
    and coordinate 2 = coordinate 3. -/
def W : Submodule 𝔽 (Fin 4 → 𝔽) where
  carrier := { v : Fin 4 → 𝔽 | v 0 = -(v 1) ∧ v 2 = -(v 3) }

  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    simp only [Pi.zero_apply]
    simp only [neg_zero]
    tauto

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
    · -- Goal: a 0 + b 0 = -(a 1 + b 1)
      rw [h_a0_eq_a1, h_b0_eq_b1, neg_add]
    · -- Goal: a 2 + b 2 = -(a 3 + b 3)
      rw [h_a2_eq_a3, h_b2_eq_b3, neg_add]

  -- Show that if u is in U and c ∈ 𝔽, then c • u is in U.
  smul_mem' := by
    intro c u h_u_in_set
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    obtain ⟨h_u0_eq_u1, h_u2_eq_u3⟩ := h_u_in_set
    constructor
    · -- Goal: c * u 0 = -(c * u 1)
      rw [h_u0_eq_u1, mul_neg]
    · -- Goal: c * u 2 = -(c * u 3)
      rw [h_u2_eq_u3, mul_neg]
