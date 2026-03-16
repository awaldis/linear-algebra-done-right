import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false

/-!
# Exercise 1C.4 - Suppose 𝑏 ∈ 𝐑. Show that the set of continuous real-valued
# functions 𝑓 on the interval [0, 1] such that ∫₀¹ 𝑓 = 𝑏 is a subspace of
# 𝐑^[0,1] if and only if 𝑏 = 0.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]

def set_of_integrals (b : ℝ) : Set (ℝ → ℝ) :=
  { f | ContinuousOn f (Set.Icc 0 1) ∧ ∫ x in (0:ℝ)..1, f x = b }

theorem subspace_iff_integ_eq_zero (b : ℝ) :
  (∃ (S : Submodule ℝ (ℝ → ℝ)), (S : Set (ℝ → ℝ)) = set_of_integrals b)
                                                                  ↔ b = 0 := by
  constructor
  · -- Forward direction - If S is a subspace then b = 0
    intro ⟨S, hS⟩
    unfold set_of_integrals at *
    -- Use the fact that the zero vector MUST be in the set to show that
    -- b MUST be zero.
    have h_0vec_in_set : (0 : ℝ → ℝ) ∈ (S : Set _) := S.zero_mem
    rw [hS, Set.mem_setOf_eq] at h_0vec_in_set
    rcases h_0vec_in_set with ⟨h_is_contin_on_int, h_integ_0_is_b⟩
    have h_integ_zero : ∫ x in (0:ℝ)..1, (0 : ℝ → ℝ) x = 0 := intervalIntegral.integral_zero
    rw [h_integ_0_is_b] at h_integ_zero
    exact h_integ_zero

  · -- Reverse direction - If b = 0 then S is a subspace.
    intro h_b_eq_zero
    use {
    carrier := set_of_integrals b
    ----------------------------------------------------------------------------
    zero_mem' := by
      unfold set_of_integrals at *
      simp only [Set.mem_setOf_eq] at *
      constructor
      · -- Goal: ContinuousOn 0 (Set.Icc 0 1)
        exact continuousOn_const
      · -- Goal: ∫ (x : ℝ) in 0..1, 0 x = b
        have h_integ_zero : ∫ x in (0:ℝ)..1, (0 : ℝ → ℝ) x = 0 :=
                                                 intervalIntegral.integral_zero
        rw [h_b_eq_zero, h_integ_zero]
    ----------------------------------------------------------------------------
    add_mem' := by
      -- Let f and g be functions that are elements of the set.
      intro f g hf hg
      unfold set_of_integrals at *
      simp only [Set.mem_setOf_eq] at *
      rcases hf with ⟨h_f_is_contin_on_int, h_f_integ_on_0_1_is_b⟩
      rcases hg with ⟨h_g_is_contin_on_int, h_g_integ_on_0_1_is_b⟩

      constructor
      · -- Goal: ContinuousOn (f + g) (Set.Icc 0 1)
        exact ContinuousOn.add h_f_is_contin_on_int
                               h_g_is_contin_on_int
      · -- Goal: ∫ (x : ℝ) in 0..1, (f + g) x = b

        -- Show that the unordered closed interval is the same as the ordered one.
        have h_uIcc : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le (by norm_num)

        -- Modify the continuity hypotheses to use the unordered interval.
        rw [← h_uIcc] at h_f_is_contin_on_int
        rw [← h_uIcc] at h_g_is_contin_on_int

        -- Prove integratability.  "intervalIntegral" requires an unordered interval.
        have h_f_integrable_on_0_1 : IntervalIntegrable f
                                     MeasureTheory.MeasureSpace.volume 0 1 :=
                           ContinuousOn.intervalIntegrable h_f_is_contin_on_int

        have h_g_integrable_on_0_1 : IntervalIntegrable g
                                     MeasureTheory.MeasureSpace.volume 0 1 :=
                           ContinuousOn.intervalIntegrable h_g_is_contin_on_int

        simp only [Pi.add_apply]
        -- Goal: ∫ (x : ℝ) in 0..1, f x + g x = b

        rw [intervalIntegral.integral_add h_f_integrable_on_0_1
                                          h_g_integrable_on_0_1 ]
        -- Goal: (∫ (x : ℝ) in 0..1, f x) + ∫ (x : ℝ) in 0..1, g x = b

        rw[h_f_integ_on_0_1_is_b, h_g_integ_on_0_1_is_b]
        -- Goal: b + b = b
        subst (h_b_eq_zero : b = 0)
        ring
    ----------------------------------------------------------------------------
    smul_mem' := by
      -- Let c be a scalar and f be an arbitary function from the set.
      intro c f hf
      unfold set_of_integrals at *
      simp only [Set.mem_setOf_eq] at *
      rcases hf with ⟨h_f_is_contin_on_int, h_f_integ_on_0_1_is_b⟩

      constructor
      · -- Goal: ContinuousOn (c • f) (Set.Icc 0 1)
        exact ContinuousOn.const_smul h_f_is_contin_on_int c

      · -- Goal: ∫ (x : ℝ) in 0..1, (c • f) x = b

        -- Show that the unordered closed interval is the same as the ordered one.
        have h_uIcc : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le (by norm_num)

        -- Modify the continuity hypothesis to use the unordered interval.
        rw [← h_uIcc] at h_f_is_contin_on_int

        -- Prove integratability. "intervalIntegral" requires an unordered interval.
        have h_f_integrable_on_0_1 : IntervalIntegrable f
                                     MeasureTheory.MeasureSpace.volume 0 1 :=
                           ContinuousOn.intervalIntegrable h_f_is_contin_on_int

        simp only [Pi.smul_apply]
        -- Goal: ∫ (x : ℝ) in 0..1, c • f x = b

        simp only [smul_eq_mul]
        -- Goal: ∫ (x : ℝ) in 0..1, c * f x = b

        rw [intervalIntegral.integral_const_mul]
        -- Goal: c * ∫ (x : ℝ) in 0..1, f x = b

        rw[h_f_integ_on_0_1_is_b]
        -- Goal: c * b = b
        subst (h_b_eq_zero : b = 0)
        ring
    }
    rfl
