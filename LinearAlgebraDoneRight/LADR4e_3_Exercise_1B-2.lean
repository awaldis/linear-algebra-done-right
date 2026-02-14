import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.NeZero -- for inv_mul_cancel₀
/-!
# Exercise 1B.2 - Suppose 𝑎 ∈ 𝐅, 𝑣 ∈ 𝑉, and 𝑎𝑣 = 0. Prove that 𝑎 = 0 or 𝑣 = 0
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]

theorem axler_1B_2 (a : 𝔽) (v : V) (h : a • v = 0) : a = 0 ∨ v = 0 := by
  by_cases ha : a = 0
  · left; -- show a = 0
    -- In this branch we are assuming a = 0 so we are done.
    exact ha
  · right; -- show v = 0
    -- In this branch we are assuming a ≠ 0 and so we are allowed
    -- to use a⁻¹ * a = 1.
      calc v
          = (1:𝔽) • v     := by rw [one_smul]
        _ = (a⁻¹ * a) • v := by simp [inv_mul_cancel₀ ha]
        _ = a⁻¹ • (a • v) := by rw [mul_smul]
        _ = a⁻¹ • (0:V)   := by rw [h]
        _ = (0:V)         := by rw [smul_zero]
