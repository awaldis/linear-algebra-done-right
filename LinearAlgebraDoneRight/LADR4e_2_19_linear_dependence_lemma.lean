import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]

/-!
# Theorem 2.19 - linear dependence lemma
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
-- Define linear dependence and independence
-- ═══════════════════════════════════════════════════════════════════════════

def linearly_independent {m : ℕ} (vector_list : Fin m → V ) : Prop :=
   ∀ (a : Fin m → 𝔽), (∑ k, a k • vector_list k = 0 ) → a = 0

def linearly_dependent {m : ℕ} (vector_list : Fin m → V ) : Prop :=
   ∃ (a : Fin m → 𝔽), (a ≠ 0) ∧ (∑ k, a k • vector_list k = 0 )

-- ═══════════════════════════════════════════════════════════════════════════
-- Verify that the definitions behave as expected.
-- ═══════════════════════════════════════════════════════════════════════════
theorem linearly_dependent_iff_not_linearly_independent
                               {m : ℕ} (vector_list : Fin m → V ) :
    linearly_dependent (𝔽 := 𝔽 ) vector_list ↔
    ¬ linearly_independent (𝔽 := 𝔽 ) vector_list := by
    constructor
    · unfold linearly_dependent
      unfold linearly_independent
      intro h_lin_dep
      obtain ⟨ a_list, h_lin_dep_conjunction ⟩ := h_lin_dep
      obtain⟨ h_alist_nonzero, h_lin_comb_eq_zero ⟩ := h_lin_dep_conjunction
      intro h_lin_indep
      specialize h_lin_indep a_list
      specialize h_lin_indep h_lin_comb_eq_zero
      exact absurd h_lin_indep h_alist_nonzero

    · unfold linearly_dependent
      unfold linearly_independent
      intro h_lin_indep
      push_neg at h_lin_indep
      obtain⟨ a_list, h_lin_indep_conjunction ⟩ := h_lin_indep
      obtain⟨ h_lin_comb_eq_zer, h_alist_nonzero ⟩ := h_lin_indep_conjunction
      use a_list


-- ═══════════════════════════════════════════════════════════════════════════
-- linear dependence lemma
-- ═══════════════════════════════════════════════════════════════════════════

-- TBD
