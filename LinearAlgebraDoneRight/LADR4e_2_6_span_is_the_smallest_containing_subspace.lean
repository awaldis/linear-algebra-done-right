import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]

/-!
# Theorem 2.6 - span is the smallest containing subspace
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
-- ═══════════════════════════════════════════════════════════════════════════
-- Define the span as a subspace of V.
-- ═══════════════════════════════════════════════════════════════════════════
def spanSubspace {m : ℕ} (vector_list : Fin m → V ) : Submodule 𝔽 V where

  carrier := { v : V | ∃ (a : Fin m → 𝔽), v = ∑ k, a k • vector_list k }
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    use 0
    simp only [Pi.zero_apply]
    norm_num

  add_mem' := by
    intro v₁ v₂ h_v₁_in_set h_v₂_in_set
    simp only [Set.mem_setOf_eq] at *

    obtain ⟨a_list, h_v₁_eq_a_lincomb⟩ := h_v₁_in_set
    obtain ⟨c_list, h_v₂_eq_c_lincomb⟩ := h_v₂_in_set

    use a_list + c_list

    calc v₁ + v₂
        = ∑ k, a_list k • vector_list k + v₂  := by rw [h_v₁_eq_a_lincomb]
      _ = ∑ k, a_list k • vector_list k + ∑ k, c_list k • vector_list k
                                              := by rw [h_v₂_eq_c_lincomb]
      _ = ∑ k, (a_list • vector_list) k + ∑ k, (c_list • vector_list) k
                                              := by norm_num
      _ = ∑ k, ((a_list • vector_list) k + (c_list • vector_list) k )
                                              := by rw[Finset.sum_add_distrib]

      _ = ∑ k, (a_list + c_list ) k • vector_list k := by simp [add_smul]

  smul_mem' := by
    intro c v h_v_in_set
    simp only [Set.mem_setOf_eq] at *
    obtain ⟨a_list, h_v_eq_lincomb⟩ := h_v_in_set

    use c • a_list
    calc c • v
        = c • ∑ k, a_list k • vector_list k   := by rw [h_v_eq_lincomb]
      _ = ∑ k, c • a_list k • vector_list k   := by rw [Finset.smul_sum]
      _ = ∑ k, (c • a_list) k • vector_list k := by simp [mul_smul]

-- ═══════════════════════════════════════════════════════════════════════════
-- Show that each vector in the list is contained in the span of the list.
-- ═══════════════════════════════════════════════════════════════════════════
theorem each_vector_in_span {m : ℕ} (vector_list : Fin m → V ) :
    ∀ k, vector_list k ∈ spanSubspace (𝔽 := 𝔽) vector_list := by

  intro k
  unfold spanSubspace
  -- Use a function that behaves like a vector where the kth coordinate
  -- is 1 and the rest are 0. This is the "aₖ=1 and all other a's are zero"
  -- from the book.
  use fun i => if i = k then 1 else 0
  simp only
  -- Goal: vector_list k = ∑ x, (if x = k then 1 else 0) • vector_list x
  simp [Finset.sum_ite_eq']

-- ═══════════════════════════════════════════════════════════════════════════
-- Show that spanSubspace is the smallest subspace of V that contain all the
-- vectors in the list.
-- ═══════════════════════════════════════════════════════════════════════════
theorem spanSubspace_is_smallest {m : ℕ} (vector_list : Fin m → V )
                                         (W : Submodule 𝔽 V)
  (h_W_contains_every_vₖ : ∀ k, vector_list k ∈ W) :
  ((spanSubspace (𝔽 := 𝔽) vector_list) ≤ W) := by

  intro v h_v_in_spanSubspace

  unfold spanSubspace at *

  obtain ⟨ a_list, h_v_eq_lincomb ⟩ := h_v_in_spanSubspace

  rw[h_v_eq_lincomb]

  -- If every vector in a list is in a subspace then their sum is also in the
  -- subspace.
  apply Submodule.sum_mem
  intro c _
  exact Submodule.smul_mem W (a_list c) (h_W_contains_every_vₖ c)
