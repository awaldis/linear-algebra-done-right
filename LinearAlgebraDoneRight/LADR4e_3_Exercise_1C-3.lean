import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false

/-!
# Exercise 1C.3 - Show that the set of differentiable real-valued functions 𝑓 on the interval
# (−4, 4) such that 𝑓′(−1) = 3 𝑓(2) is a subspace of 𝐑^(−4,4).
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]

def set_3 : Set (ℝ → ℝ) :=
  { f | DifferentiableOn ℝ f (Set.Ioo (-4 : ℝ) 4) ∧ deriv f (-1 : ℝ) = (3 : ℝ) * f 2 }

theorem subspace_iff_deriv_eq_zero :
  (∃ (S : Submodule ℝ (ℝ → ℝ)), (S : Set (ℝ → ℝ)) = set_3) := by
    use {
    carrier := set_3
    zero_mem' := by
      unfold set_3 at *
      simp only [Set.mem_setOf_eq] at *
      constructor
      · -- Goal: DifferentiableOn ℝ 0 (Set.Ioo -4 4)
        exact differentiableOn_const 0
      · -- Goal: deriv 0 (-1) = 3 * 0 2
        have h_deriv_zero : deriv (0 : ℝ → ℝ) (-1 : ℝ) = 0 := deriv_const (-1 : ℝ) (0 : ℝ)
        have h_3f_zero : 3 * (0 : ℝ → ℝ) (2 : ℝ) = 0 := by simp
        -- We now have proof that both sides of the = are zero.
        rw [h_3f_zero, h_deriv_zero]

    add_mem' := by
      -- Let f and g be differentiable functions
      intro f g hf hg
      unfold set_3 at *
      simp only [Set.mem_setOf_eq] at *
      rcases hf with ⟨h_f_is_diffable_on_int, h_f_deriv_eq_3f⟩
      rcases hg with ⟨h_g_is_diffable_on_int, h_g_deriv_eq_3f⟩

      constructor
      · -- Goal: DifferentiableOn ℝ (f + g) (Set.Ioo -4 4)
        exact DifferentiableOn.add h_f_is_diffable_on_int
                                   h_g_is_diffable_on_int
      · -- Goal: deriv (f + g) (-1) = 3 * (f + g) 2
        have h_neg1_mem : (-1 : ℝ) ∈ Set.Ioo (-4 : ℝ) 4 := by norm_num

        -- Convert differentiable "On" to "At"
        have h_f_diffable_at_neg1 : DifferentiableAt ℝ f (-1 : ℝ) :=
          h_f_is_diffable_on_int.differentiableAt (IsOpen.mem_nhds isOpen_Ioo h_neg1_mem )

        have h_g_diffable_at_neg1 : DifferentiableAt ℝ g (-1 : ℝ) :=
          h_g_is_diffable_on_int.differentiableAt (IsOpen.mem_nhds isOpen_Ioo h_neg1_mem )

        rw [deriv_add h_f_diffable_at_neg1
                      h_g_diffable_at_neg1,
                      h_f_deriv_eq_3f,
                      h_g_deriv_eq_3f ]
        -- Goal: 3 * f 2 + 3 * g 2 = 3 * (f + g) 2
        simp only [Pi.add_apply]
        -- Goal: 3 * f 2 + 3 * g 2 = 3 * (f 2 + g 2)
        ring

    smul_mem' := by
      -- Let c be a scalar and f be a differentiable function
      intro c f hf
      unfold set_3 at *
      simp only [Set.mem_setOf_eq] at *
      rcases hf with ⟨h_f_is_diffable_on_int, h_f_deriv_eq_3f⟩

      constructor
      · -- DifferentiableOn ℝ (c • f) (Set.Ioo 0 3)
        exact DifferentiableOn.const_smul h_f_is_diffable_on_int c
      · -- Goal: deriv (c • f) (-1) = 3 * (c • f) 2
        have h_neg1_mem : (-1 : ℝ) ∈ Set.Ioo (-4 : ℝ) 4 := by norm_num

        -- Convert differentiable "On" to "At"
        have h_f_diffable_at_2 : DifferentiableAt ℝ f (-1 : ℝ)  :=
          h_f_is_diffable_on_int.differentiableAt (IsOpen.mem_nhds isOpen_Ioo h_neg1_mem )

        rw [deriv_const_smul c h_f_diffable_at_2, h_f_deriv_eq_3f ]
        -- Goal: c • (3 * f 2) = 3 * (c • f) 2
        simp only [Pi.smul_apply]
        -- Goal: c • (3 * f 2) = 3 * c • f 2
        simp
        -- Goal: c * (3 * f 2) = 3 * (c * f 2)
        ring
    }
    rfl
