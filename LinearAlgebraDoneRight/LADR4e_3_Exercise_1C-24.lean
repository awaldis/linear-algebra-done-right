import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/-!
# Exercise 1C.24 - A function 𝑓 ∶ 𝐑 → 𝐑 is called even if
#                    𝑓 (−𝑥) = 𝑓 (𝑥)
# for all 𝑥 ∈ 𝐑. A function 𝑓 ∶ 𝐑 → 𝐑 is called odd if
#                    𝑓 (−𝑥) = − 𝑓 (𝑥)
# for all 𝑥 ∈ 𝐑. Let 𝑉e denote the set of real-valued even functions on 𝐑
# and let 𝑉o denote the set of real-valued odd functions on 𝐑. Show that
# 𝐑ᴿ = 𝑉e ⊕ 𝑉o.
#
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
-- ═══════════════════════════════════════════════════════════════════════════
-- Define Vₑ
-- ═══════════════════════════════════════════════════════════════════════════
def Vₑ : Submodule ℝ ( ℝ → ℝ ) where
  carrier := { f : ℝ → ℝ  | ∀ (x : ℝ), f (-x) = f x }

  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    simp only [Pi.zero_apply]
    tauto

  -- Show that if a and b are both in U, then a + b is in U.
  add_mem' := by
    intro a b h_a_in_set h_b_in_set
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *

    intro x
    specialize h_a_in_set x
    specialize h_b_in_set x
    rw[h_a_in_set, h_b_in_set]

  -- Show that if u is in U and c ∈ 𝔽, then c • u is in U.
  smul_mem' := by
    intro c u h_u_in_set
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *

    intro x
    specialize h_u_in_set x
    rw[h_u_in_set]

-- ═══════════════════════════════════════════════════════════════════════════
-- Define Vₒ
-- ═══════════════════════════════════════════════════════════════════════════
def Vₒ : Submodule ℝ ( ℝ → ℝ ) where
  carrier := { f : ℝ → ℝ  | ∀ (x : ℝ), f (-x) = -f x }

  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    simp only [Pi.zero_apply]
    ring_nf
    tauto

  -- Show that if a and b are both in U, then a + b is in U.
  add_mem' := by
    intro a b h_a_in_set h_b_in_set
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *

    intro x
    specialize h_a_in_set x
    specialize h_b_in_set x
    rw[h_a_in_set, h_b_in_set]
    ring

  -- Show that if u is in U and c ∈ 𝔽, then c • u is in U.
  smul_mem' := by
    intro c u h_u_in_set
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *

    intro x
    specialize h_u_in_set x
    rw[h_u_in_set]
    ring

-- ═══════════════════════════════════════════════════════════════════════════
-- Show that subspaces Vₑ and Vₒ intersect only at zero.  Therefore, their sum
-- is a direct sum by theorem 1.46.
-- ═══════════════════════════════════════════════════════════════════════════
theorem Vₑ_intersect_Vₒ_eq_zero :
  ∀ v : ℝ → ℝ, (v ∈ Vₑ) ∧ (v ∈ Vₒ) → (v = 0) := by

  intro v ⟨h_v_in_Vₑ, h_v_in_Vₒ⟩

  unfold Vₑ at h_v_in_Vₑ
  unfold Vₒ at h_v_in_Vₒ

  -- Extract the carrier sets from the submodule structure.

  simp only [Submodule.mem_mk]       at h_v_in_Vₑ
  simp only [AddSubmonoid.mem_mk]    at h_v_in_Vₑ
  simp only [AddSubsemigroup.mem_mk] at h_v_in_Vₑ

  simp only [Submodule.mem_mk]       at h_v_in_Vₒ
  simp only [AddSubmonoid.mem_mk]    at h_v_in_Vₒ
  simp only [AddSubsemigroup.mem_mk] at h_v_in_Vₒ

  simp only [Set.mem_setOf_eq] at h_v_in_Vₑ
  simp only [Set.mem_setOf_eq] at h_v_in_Vₒ

  ext x

  have h_even_func : v (-x) =  v x := h_v_in_Vₑ x
  have h_odd_func  : v (-x) = -v x := h_v_in_Vₒ x

  have h_even_odd_eq : v x = -v x := by
    calc v x = v (-x) := by rw [h_even_func]
       _     = -v x   := by rw [h_odd_func]

  simp only [Pi.zero_apply]
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- Show that the sum of subspaces Vₑ and Vₒ equal to the space of all
-- real-valued functions.  This is not necessary to prove it's a direct sum,
-- but is a requirement of the problem statement.
-- ═══════════════════════════════════════════════════════════════════════════
theorem sum_Vₑ_Vₒ_eq_all_funcs :
  ∀ (v : ℝ → ℝ), ∃ (u w : ℝ → ℝ), (u ∈ Vₑ) ∧ (w ∈ Vₒ) ∧ (v = u + w) := by

  intro v

  -- Define our proposed members of Vₑ and Vₒ that will supposedly meet the
  -- criteria of the theorem.
  let u : ℝ → ℝ := fun x => (v x + v (-x)) / 2
  let w : ℝ → ℝ := fun x => (v x - v (-x)) / 2

  use u, w

  -- Break out the three AND clauses in the goal into three separate goals.
  refine ⟨?_, ?_, ?_⟩

  · -- Goal 1: u ∈ Vₑ
    unfold Vₑ
    simp only [Submodule.mem_mk]
    simp only [AddSubmonoid.mem_mk]
    simp only [AddSubsemigroup.mem_mk]
    simp only [Set.mem_setOf_eq]
    intro x
    simp only [u]
    simp only [neg_neg]
    ring_nf

  · -- Goal 2: w ∈ Vₒ
    unfold Vₒ
    simp only [Submodule.mem_mk]
    simp only [AddSubmonoid.mem_mk]
    simp only [AddSubsemigroup.mem_mk]
    simp only [Set.mem_setOf_eq]
    intro x
    simp only [w]
    simp only [neg_neg]
    ring_nf

  · -- Goal 3: v = u + w
    ext x
    rw [Pi.add_apply]
    simp only [u, w]
    ring
