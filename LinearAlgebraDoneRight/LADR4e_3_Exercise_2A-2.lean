import LinearAlgebraDoneRight.LADR4e_2_6_span_is_the_smallest_containing_subspace
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false

/-!
# Exercise 2A.2 - Prove or give a counterexample: If 𝑣₁, 𝑣₂, 𝑣₃, 𝑣₄ spans 𝑉,
# then the list 𝑣₁ − 𝑣₂, 𝑣₂ − 𝑣₃, 𝑣₃ − 𝑣₄, 𝑣₄ also spans 𝑉.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]

variable {n : ℕ}
variable {v₁ v₂ v₃ v₄ : Fin n → 𝔽}

-- ═══════════════════════════════════════════════════════════════════════════
-- The exercises only asks for one direction but will prove both.
-- ═══════════════════════════════════════════════════════════════════════════
theorem simple_span_eq_diff_span :
    {v : Fin n → 𝔽 | v ∈ spanSubspace (𝔽 := 𝔽) ![v₁, v₂, v₃, v₄]} =
    {v : Fin n → 𝔽 | v ∈ spanSubspace (𝔽 := 𝔽) ![(v₁ - v₂), (v₂ - v₃), (v₃ - v₄), v₄]} := by

  ext v
  simp only [Set.mem_setOf_eq] at *
  unfold spanSubspace
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq]

  constructor
  · -- If it's in the simple span then it's in the difference span.
    intro h_v_is_in_the_span
    obtain ⟨ a_list, h_v_eq_lincomb⟩ := h_v_is_in_the_span

    use ![a_list 0,
          a_list 0 + a_list 1,
          a_list 0 + a_list 1 + a_list 2,
          a_list 0 + a_list 1 + a_list 2 + a_list 3
         ]
    rw[h_v_eq_lincomb]
    simp[Fin.sum_univ_four]
    funext j
    simp only [Pi.add_apply]
    simp only [Pi.smul_apply]
    simp only [Pi.sub_apply]
    simp only [smul_eq_mul]
    ring

  · -- If it's in the difference span then it's in the simple span.
    intro h_v_is_in_the_span
    obtain ⟨ a_list, h_v_eq_lincomb⟩ := h_v_is_in_the_span
    use ![a_list 0,
          a_list 1 - a_list 0,
          a_list 2 - a_list 1,
          a_list 3 - a_list 2
         ]

    rw[h_v_eq_lincomb]
    simp[Fin.sum_univ_four]
    funext j
    simp only [Pi.add_apply]
    simp only [Pi.smul_apply]
    simp only [Pi.sub_apply]
    simp only [smul_eq_mul]
    ring
