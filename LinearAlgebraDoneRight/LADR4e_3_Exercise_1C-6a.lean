import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false

/-!
# Exercise 1C.6 - (a) Is {(𝑎, 𝑏, 𝑐) ∈ 𝐑³ ∶ 𝑎³ = 𝑏³} a subspace of 𝐑³?
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/

def R3_1st_2_cubed_eq_subset : Set (Fin 3 → ℝ) := {v | (v 0)^3 = (v 1)^3}

--------------------------------------------------------------------------------
-- We need this lemma to show that a³=b³ implies a=b for the "add_mem" proof.
-- Mathlib does not seem to have a simple proof for this so I had to get Google
-- Gemini to give me this one.
--------------------------------------------------------------------------------
lemma real_cube_inj {a b : ℝ} (h : a ^ 3 = b ^ 3) : a = b := by
  -- Step 1: Factor the difference of cubes
  have h_factor : (a - b) * (a^2 + a * b + b^2) = 0 := by
    calc (a - b) * (a^2 + a * b + b^2)
      _ = a^3 - b^3 := by ring
      _ = b^3 - b^3 := by rw [h]
      _ = 0         := by ring

  -- Step 2: A product is zero iff at least one factor is zero
  cases mul_eq_zero.mp h_factor with
  | inl h_sub =>
    -- Case 1: (a - b) = 0 implies a = b
    exact sub_eq_zero.mp h_sub
  | inr h_quad =>
    -- Case 2: The quadratic factor is zero.
    -- We complete the square to isolate the variables.
    -- Note: (3 / 4 : ℝ) ensures Lean uses real division, not integer division.
    have h_sq : (a + b / 2)^2 + (3 / 4 : ℝ) * b^2 = 0 := by
      calc (a + b / 2)^2 + (3 / 4 : ℝ) * b^2
        _ = a^2 + a * b + b^2 := by ring
        _ = 0                 := h_quad

    -- nlinarith natively knows that squares of reals are non-negative.
    -- If a sum of non-negative terms is 0, it deduces both terms must be 0.
    have hb : b = 0 := by nlinarith
    have ha : a = 0 := by nlinarith

    -- If both are 0, they are trivially equal.
    rw [ha, hb]

theorem R3_1st_2_cubed_eq_subspace :
  ∃ (S : Submodule ℝ  (Fin 3 → ℝ)), (S :Set (Fin 3 → ℝ)) =
                                                 R3_1st_2_cubed_eq_subset := by
    use {
    carrier := R3_1st_2_cubed_eq_subset

    zero_mem' := by
      unfold R3_1st_2_cubed_eq_subset at *
      simp only [Set.mem_setOf_eq] at *
      rw [Pi.zero_apply,Pi.zero_apply]

    add_mem' := by
      -- Let f and g be differentiable functions
      intro v1 v2 h_v1_cubed_eq h_v2_cubed_eq
      unfold R3_1st_2_cubed_eq_subset at *
      simp only [Set.mem_setOf_eq] at *
      rw [Pi.add_apply,Pi.add_apply]

      -- Use the lemma proved above to convert a³=b³ to a=b.
      have h_v1_eq : v1 0 = v1 1 := real_cube_inj h_v1_cubed_eq
      have h_v2_eq : v2 0 = v2 1 := real_cube_inj h_v2_cubed_eq

      rw [h_v1_eq, h_v2_eq]

    smul_mem' := by
      intro c v h_v1_cubed_eq
      unfold R3_1st_2_cubed_eq_subset at *
      simp only [Set.mem_setOf_eq] at *
      rw [Pi.smul_apply, Pi.smul_apply]
      rw [smul_pow, smul_pow]
      rw [h_v1_cubed_eq]
          }
    rfl
