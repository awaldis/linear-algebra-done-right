import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/-!
# Exercise 1C.6 - (b) Is {(𝑎, 𝑏, 𝑐) ∈ ℂ³ ∶ 𝑎³ = 𝑏³} a subspace of ℂ³?
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/

def C3_1st_2_cubed_eq_subset : Set (Fin 3 → ℂ) := {v | (v 0)^3 = (v 1)^3}

noncomputable def ω      : ℂ := ⟨-1/2,  Real.sqrt 3 /2⟩
noncomputable def ω_sqrd : ℂ := ⟨-1/2, -Real.sqrt 3 /2⟩

lemma ω_cubed_eq_one : ω ^ 3 = 1 := by

  -- We must explicitly prove that squaring the square root of 3 equals 3.
  -- The `by positivity` tactic automatically proves that 3 >= 0,
  -- which is required before Lean allows you to cancel a square root.
  -- "nlinarith" (below) will need this fact.
  have h_sqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by positivity)

  -- Split the number on each side of the equation into real and imaginary
  -- cases and prove each one separately.
  unfold ω
  apply Complex.ext

  -----------------------------------------------------------------------------
  -- Real case: Prove the Real parts are equal
  · -- Unfold omega and expand the cube (omega * omega * omega)
    simp only [pow_succ]  --expand to ω^0 * ω * ω * ω
    simp only [pow_zero]  --            1 * ω * ω * ω
    simp only [one_mul]   --                ω * ω * ω
    simp only [Complex.mul_re]
    simp only [Complex.mul_im]
    simp only [Complex.one_re]

    ring_nf

    -- Now we hand the expanded algebra and our square root fact to `nlinarith`
    -- (non-linear arithmetic), which will crunch the fractions down to 1.
    nlinarith [h_sqrt]

  -----------------------------------------------------------------------------
  -- Imaginary case: Prove the Imaginary parts are equal
  · -- Unfold omega and expand the cube
    simp only [pow_succ]
    simp only [pow_zero]
    simp only [one_mul]
    simp only [Complex.mul_im]
    simp only [Complex.mul_re]
    simp only [Complex.one_im]

    ring_nf

    -- "nlinarith" (below) will need this fact.
    have h_3sqrt : (Real.sqrt 3) ^ 3 = 3 * (Real.sqrt 3) := by
      calc Real.sqrt 3 ^ 3
         = Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
       _ =               3 * Real.sqrt 3 := by rw [h_sqrt]

    -- `nlinarith` will crunch the fractions down to 0, matching the imaginary
    -- part of 1.
    nlinarith [h_3sqrt]

lemma ω_sqrd_cubed_eq_one : ω_sqrd ^ 3 = 1 := by

  -- We must explicitly prove that squaring the square root of 3 equals 3.
  -- The `by positivity` tactic automatically proves that 3 >= 0,
  -- which is required before Lean allows you to cancel a square root.
  -- "nlinarith" (below) will need this fact.
  have h_sqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by positivity)

  -- Split the number on each side of the equation into real and imaginary
  -- cases and prove each one separately.
  unfold ω_sqrd
  apply Complex.ext

  -----------------------------------------------------------------------------
  -- Real case: Prove the Real parts are equal
  · -- Unfold omega and expand the cube (omega * omega * omega)
    simp only [pow_succ]  --expand to ω^0 * ω * ω * ω
    simp only [pow_zero]  --            1 * ω * ω * ω
    simp only [one_mul]   --                ω * ω * ω
    simp only [Complex.mul_re]
    simp only [Complex.mul_im]
    simp only [Complex.one_re]

    ring_nf

    -- Now we hand the expanded algebra and our square root fact to `nlinarith`
    -- (non-linear arithmetic), which will crunch the fractions down to 1.
    nlinarith [h_sqrt]

  -----------------------------------------------------------------------------
  -- Imaginary case: Prove the Imaginary parts are equal
  · -- Unfold omega and expand the cube
    simp only [pow_succ]
    simp only [pow_zero]
    simp only [one_mul]
    simp only [Complex.mul_im]
    simp only [Complex.mul_re]
    simp only [Complex.one_im]

    ring_nf

    -- "nlinarith" (below) will need this fact.
    have h_3sqrt : (Real.sqrt 3) ^ 3 = 3 * (Real.sqrt 3) := by
      calc Real.sqrt 3 ^ 3
         = Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
       _ =               3 * Real.sqrt 3 := by rw [h_sqrt]

    -- `nlinarith` will crunch the fractions down to 0, matching the imaginary
    -- part of 1.
    nlinarith [h_3sqrt]

lemma add_ω_to_ω_sqrd : ω + ω_sqrd = -1 := by
  unfold ω ω_sqrd
  apply Complex.ext
  · -- Real case: Prove the Real parts are equal
    simp only [Complex.add_re]
    simp only [Complex.neg_re]
    simp only [Complex.one_re]
    ring

  · -- Imaginary case: Prove the Imaginary parts are equal
    simp only [Complex.add_im]
    simp only [Complex.neg_im]
    simp only [Complex.one_im]
    ring

--------------------------------------------------------------------------------
-- Now that we have the necessary definitions and lemmas, here is the theorem
-- and it's proof.
--------------------------------------------------------------------------------
theorem C3_1st_2_cubed_eq_not_subspace :
  ¬ ∃ (S : Submodule ℝ  (Fin 3 → ℂ)), (S :Set (Fin 3 → ℂ)) =
                                                 C3_1st_2_cubed_eq_subset := by
  intro ⟨S, hS⟩

  -- Prove (-1,2,0) IS NOT in the subspace set.
  have h_neg1_2_0_not_in_set : ¬![-1, 2, 0] ∈ C3_1st_2_cubed_eq_subset := by
    unfold C3_1st_2_cubed_eq_subset
    simp only [Set.mem_setOf_eq]
    simp [Matrix.cons_val_zero]
    norm_num

  -- Prove (-1,2,0) IS in the subspace set.
  have h_neg1_2_0_in_set : ![-1, 2, 0] ∈ C3_1st_2_cubed_eq_subset := by

    have h_ω_1_0_in_subspace : ![ω, 1, 0] ∈ S := by
      have : ![ω, 1, 0] ∈ C3_1st_2_cubed_eq_subset := by
        unfold C3_1st_2_cubed_eq_subset
        simp only [Set.mem_setOf_eq]
        simp [Matrix.cons_val_zero]
        exact ω_cubed_eq_one
      rw [← hS] at this
      rw [SetLike.mem_coe] at this
      exact this

    have h_ω_sqrd_1_0_in_subspace : ![ω_sqrd, 1, 0] ∈ S := by
      have : ![ω_sqrd, 1, 0] ∈ C3_1st_2_cubed_eq_subset := by
        unfold C3_1st_2_cubed_eq_subset
        simp only [Set.mem_setOf_eq]
        simp [Matrix.cons_val_zero]
        exact ω_sqrd_cubed_eq_one
      rw [← hS] at this
      rw [SetLike.mem_coe] at this
      exact this

    have h_neg1_2_0_in_subspace : ![-1, 2, 0] ∈ S := by
      have h_sum_is_member: ![ω, 1, 0] + ![ω_sqrd, 1, 0] ∈ S :=
                         S.add_mem h_ω_1_0_in_subspace h_ω_sqrd_1_0_in_subspace

      have h_sum_eq_neg1_2_0 : ![ω, 1, 0] + ![ω_sqrd, 1, 0] = ![-1, 2, 0] := by
        ext i
        fin_cases i -- Prove the three addition operations individually.
        · simp
          exact add_ω_to_ω_sqrd
        · simp; ring
        · simp

      rwa [h_sum_eq_neg1_2_0] at h_sum_is_member

    rw [← hS]
    rw [SetLike.mem_coe]
    exact h_neg1_2_0_in_subspace

  -- Assuming S is a subspace leads to a contradiction.
  exact absurd h_neg1_2_0_in_set h_neg1_2_0_not_in_set
