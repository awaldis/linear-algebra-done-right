import LinearAlgebraDoneRight.LADR4e_2_6_span_is_the_smallest_containing_subspace
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false

/-!
# Exercise 2A.1 - Find a list of four distinct vectors in 𝐅³ whose span equals
# {(𝑥, 𝑦, 𝑧) ∈ 𝐅³ ∶ 𝑥 + 𝑦 + 𝑧 = 0}.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]

-- The distinct vectors requested.
def v₁ : Fin 3 → 𝔽 := ![1, -1,  0]
def v₂ : Fin 3 → 𝔽 := ![0,  1, -1]
def v₃ : Fin 3 → 𝔽 := ![1,  0, -1]
def v₄ : Fin 3 → 𝔽 := ![1, -2,  1]

def span_list : Fin 4 → (Fin 3 → 𝔽) := ![v₁, v₂, v₃, v₄]

-- ═══════════════════════════════════════════════════════════════════════════
-- Show that the span of the distinct vectors is equal to the set of all
-- vectors whose sum of coordinates is zero.
-- ═══════════════════════════════════════════════════════════════════════════
theorem span_eq_zero_sum_set :
                     {v : Fin 3 → 𝔽 | v ∈ spanSubspace (𝔽 := 𝔽) span_list} =
                     {v : Fin 3 → 𝔽 | v 0 + v 1 + v 2 = 0} := by
  ext v
  constructor
  · -- if a vector is in the span then it matches the set definition.
    intro h_v_is_in_the_span
    obtain ⟨ a_list, h_v_eq_lincomb⟩ := h_v_is_in_the_span
    simp only [Set.mem_setOf_eq] at *
    rw[h_v_eq_lincomb]
    simp[span_list]
    simp[v₁, v₂, v₃, v₄]
    simp[Fin.sum_univ_four]
    ring
  · -- if a vector matches the set definition then it's in the span.
    intro h_set_member_definition
    simp only [Set.mem_setOf_eq] at *
    unfold spanSubspace
    -- Use x (v 0) and -z (-v 2) as the a₁ and a₂ coefficients.  a₃ and a₄ can
    -- be zero.
    use ![v 0, -v 2, 0, 0]
    ext i
    fin_cases i
    · -- v 0 = (v 0 * 1) + (the other three terms are zero)
      simp [span_list, v₁, v₂, v₃, v₄, Fin.sum_univ_four]

    · -- v 1 = (v 0 * -1) + (-v 2 * 1) + (the last two terms are zero)
      simp only [Fin.mk_one, Fin.isValue, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp only [Fin.isValue, span_list]
      simp only [v₁, v₂, v₃, v₄]
      simp only [Matrix.cons_val']
      simp only [Matrix.cons_val_one]
      simp only [Matrix.cons_val_zero]
      simp only [Matrix.cons_val_fin_one]
      simp only [Fin.sum_univ_four]
      simp only [mul_neg, mul_one, Matrix.cons_val]
      simp only [mul_zero, add_zero, zero_mul, neg_zero]
      -- New goal: v 1 = -v 0 + -v 2
      rw[add_eq_zero_iff_eq_neg] at h_set_member_definition
      rw[←eq_neg_add_iff_add_eq] at h_set_member_definition
      exact h_set_member_definition

    · -- v 2 = ((-v 2) * -1) + (the other three terms are zero)
      simp [span_list, v₁, v₂, v₃, v₄, Fin.sum_univ_four]
