import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false

/-!
# Exercise 1C.2 - Verify all assertions about subspaces in Example 1.35.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]

-----------------------------------------------------------------------------
-- Exercise (a)
-- Show this set is a subspace if and only if b = 0.
-----------------------------------------------------------------------------
def set_2a (b : 𝔽) : Set (Fin 4 → 𝔽) := { x | x 2 = 5 * x 3 + b }

theorem subspace_iff_b_eq_zero (b : 𝔽) :
  (∃ (S : Submodule 𝔽 (Fin 4 → 𝔽)), (S : Set (Fin 4 → 𝔽)) = set_2a b)
                                                                  ↔ b = 0 := by
  constructor
  · -- Forward direction - If S is a subspace then b = 0
    intro ⟨S, hS⟩
    unfold set_2a at *
    -- Use the fact that the zero vector MUST be in the set to show that
    -- b MUST be zero.
    have h_0vec_in_set : (0 : Fin 4 → 𝔽) ∈ (S : Set _) := S.zero_mem
    rw [hS, Set.mem_setOf_eq] at h_0vec_in_set
    simp only [Pi.zero_apply] at h_0vec_in_set
    simp only [mul_zero] at h_0vec_in_set
    simp only [zero_add] at h_0vec_in_set
    exact h_0vec_in_set.symm

  · -- Reverse direction - If b = 0 then S is a subspace.
    intro h_b_eq_zero
    use {
    carrier := set_2a b
    zero_mem' := by
      unfold set_2a at *
      simp only [Set.mem_setOf_eq] at *
      simp only [Pi.zero_apply]
      subst h_b_eq_zero
      ring
    add_mem' {a b} ha hb := by
      unfold set_2a at *
      simp only [Set.mem_setOf_eq] at *
      simp only [Pi.add_apply]
      subst h_b_eq_zero
      calc a 2 + b 2
         = (5 * a 3 + 0) + (5 * b 3 + 0) := by rw [ha, hb]
       _ = 5 * (a 3 + b 3) + 0           := by ring
    smul_mem' c v hv := by
       unfold set_2a at *
       simp only [Set.mem_setOf_eq] at *
       simp only [Pi.smul_apply]
       simp only [smul_eq_mul]
       subst h_b_eq_zero
       calc c * v 2
          = c * (5 * v 3 + 0) := by rw [hv]
        _ = 5 * (c * v 3) + 0 := by ring
    }
    rfl

/-!
Exercise 1C.2 (b)

The set of continuous real-valued functions on the interval [0,1]
is a subspace of ℝ^[0,1] (i.e. of all functions [0,1] → ℝ).
-/
-- Define the interval [0, 1] as a subtype to serve as our domain
abbrev I := Set.Icc (0 : ℝ) (1 : ℝ)

-- Define the set of continuous functions from I to ℝ
def set_2b : Set (I → ℝ) := { f | Continuous f }

theorem continuous_functions_is_subspace :
  ∃ (S : Submodule ℝ (I → ℝ)), (S : Set (I → ℝ)) = set_2b := by
  use {
    carrier := set_2b
    zero_mem' := by
      unfold set_2b
      simp only [Set.mem_setOf_eq]
      -- The zero function is identically 0, which is continuous
      exact continuous_zero
    add_mem' := by
      -- Let f and g be continuous functions
      intro f g hf hg
      unfold set_2b at *
      simp only [Set.mem_setOf_eq] at *
      -- The sum of two continuous functions is continuous
      exact Continuous.add hf hg
    smul_mem' := by
      -- Let c be a scalar and f be a continuous function
      intro c f hf
      unfold set_2b at *
      simp only [Set.mem_setOf_eq] at *
      -- Scalar multiplication of a continuous function is continuous
      exact Continuous.const_smul hf c
  }
  rfl

/-!
Exercise 1C.2 (c)

The set of differentiable real-valued functions on ℝ is a subspace of ℝ^ℝ.
-/
-- Define the set of differentiable functions from ℝ to ℝ
def set_2c : Set (ℝ → ℝ) := { f | Differentiable ℝ f }

theorem differentiable_functions_is_subspace :
  ∃ (S : Submodule ℝ (ℝ → ℝ)), (S : Set (ℝ → ℝ)) = set_2c := by
  use {
    carrier := set_2c
    zero_mem' := by
      unfold set_2c
      simp only [Set.mem_setOf_eq]
      -- The zero function is identically the constant 0, which is differentiable
      exact differentiable_const 0
    add_mem' := by
      -- Let f and g be differentiable functions
      intro f g hf hg
      unfold set_2c at *
      simp only [Set.mem_setOf_eq] at *
      -- The sum of two differentiable functions is differentiable
      exact Differentiable.add hf hg
    smul_mem' := by
      -- Let c be a scalar and f be a differentiable function
      intro c f hf
      unfold set_2c at *
      simp only [Set.mem_setOf_eq] at *
      -- Scalar multiplication of a differentiable function is differentiable
      exact Differentiable.const_smul hf c
  }
  rfl

/-!
Exercise 1C.2 (d)

The set of differentiable real-valued functions 𝑓 on the interval (0, 3) such
that 𝑓′(2) = 𝑏 is a subspace of ℝ^(0,3) if and only if 𝑏 = 0.
-/

def set_2d (b : ℝ) : Set (ℝ → ℝ) :=
  { f | DifferentiableOn ℝ f (Set.Ioo 0 3) ∧ deriv f 2 = b }

theorem subspace_iff_deriv_eq_zero (b : ℝ) :
  (∃ (S : Submodule ℝ (ℝ → ℝ)), (S : Set (ℝ → ℝ)) = set_2d b) ↔ b = 0 := by
  constructor
  · -- Forward direction - If S is a subspace then b = 0
    intro ⟨S, hS⟩
    unfold set_2d at *
    -- Use the fact that the zero vector MUST be in the set to show that
    -- b MUST be zero.
    have h_0vec_in_set : (0 : ℝ → ℝ) ∈ (S : Set _) := S.zero_mem
    rw [hS, Set.mem_setOf_eq] at h_0vec_in_set
    rcases h_0vec_in_set with ⟨h_is_diffable_on_int, h_deriv_0_is_b⟩
    have h_deriv_zero : deriv (0 : ℝ → ℝ) 2 = 0 := deriv_const 2 (0 : ℝ)
    rw [h_deriv_0_is_b] at h_deriv_zero
    exact h_deriv_zero

  · -- Reverse direction - If b = 0 then S is a subspace.
    intro h_b_eq_zero
    use {
    carrier := set_2d b
    zero_mem' := by
      unfold set_2d at *
      simp only [Set.mem_setOf_eq] at *
      constructor
      · -- Goal: DifferentiableOn ℝ 0 (Set.Ioo 0 3)
        exact differentiableOn_const 0
      · -- Goal: deriv 0 2 = b
        have h_deriv_zero : deriv (0 : ℝ → ℝ) 2 = 0 := deriv_const 2 (0 : ℝ)
        rw [h_b_eq_zero, h_deriv_zero]

    add_mem' := by
      -- Let f and g be differentiable functions
      intro f g hf hg
      unfold set_2d at *
      simp only [Set.mem_setOf_eq] at *
      rcases hf with ⟨h_f_is_diffable_on_int, h_f_deriv_at2_is_b⟩
      rcases hg with ⟨h_g_is_diffable_on_int, h_g_deriv_at2_is_b⟩

      constructor
      · -- Goal: DifferentiableOn ℝ (f + g) (Set.Ioo 0 3)
        exact DifferentiableOn.add h_f_is_diffable_on_int
                                   h_g_is_diffable_on_int
      · -- Goal: deriv (f + g) 2 = b
        have h_2_mem : (2 : ℝ) ∈ Set.Ioo (0 : ℝ) 3 := by norm_num

        -- Convert differentiable "On" to "At"
        have h_f_diffable_at_2 : DifferentiableAt ℝ f 2 :=
          h_f_is_diffable_on_int.differentiableAt (IsOpen.mem_nhds isOpen_Ioo h_2_mem )

        have h_g_diffable_at_2 : DifferentiableAt ℝ g 2 :=
          h_g_is_diffable_on_int.differentiableAt (IsOpen.mem_nhds isOpen_Ioo h_2_mem )

        rw [deriv_add h_f_diffable_at_2
                      h_g_diffable_at_2,
                      h_f_deriv_at2_is_b,
                      h_g_deriv_at2_is_b ]
        -- New Goal: b + b = b
        subst h_b_eq_zero
        ring

    smul_mem' := by
      -- Let c be a scalar and f be a differentiable function
      intro c f hf
      unfold set_2d at *
      simp only [Set.mem_setOf_eq] at *
      rcases hf with ⟨h_f_is_diffable_on_int, h_f_deriv_at2_is_b⟩

      constructor
      · -- DifferentiableOn ℝ (c • f) (Set.Ioo 0 3)
        exact DifferentiableOn.const_smul h_f_is_diffable_on_int c
      · -- Goal: deriv (c • f) 2 = b
        have h_2_mem : (2 : ℝ) ∈ Set.Ioo (0 : ℝ) 3 := by norm_num

        -- Convert differentiable "On" to "At"
        have h_f_diffable_at_2 : DifferentiableAt ℝ f 2 :=
          h_f_is_diffable_on_int.differentiableAt (IsOpen.mem_nhds isOpen_Ioo h_2_mem )

        rw [deriv_const_smul c h_f_diffable_at_2, h_f_deriv_at2_is_b ]
        -- New goal: c • b = b
        subst h_b_eq_zero
        simp
    }
    rfl
