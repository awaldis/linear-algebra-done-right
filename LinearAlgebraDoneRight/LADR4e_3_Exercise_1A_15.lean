import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Action.Defs -- (for smul_eq_mul)
/-!
# Exercise 1A.15 - distributivity of scalar multiplication
# with respect to scalar addition in 𝔽ⁿ
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]
variable {n : ℕ}
variable {x : Fin n → 𝔽}
variable {a : 𝔽}
variable {b : 𝔽}

theorem dist_of_smul_wrt_sadd : (a + b) • x = a • x + b • x  := by
calc (a + b) • x
      -- Convert vector x to functional form.
    = (a + b) • fun i=>x i := by simp[funext]

      -- Move the scalar inside the function.
  _ = fun i=> ((a + b): 𝔽) • ((x i): 𝔽) := by rw [Pi.smul_def]

      -- Convert to field multiplication.
  _ = fun i=> (a + b) * (x i) := by simp [smul_eq_mul]

      -- Now we can use regular field distribution.
  _ = fun i=> a * (x i) + b * (x i) := by simp [right_distrib]

      -- Convert back to scalar multiplication.
  _ = fun i=> a • (x i) + b • (x i) := by ext i; rw [smul_eq_mul, smul_eq_mul]
  _ = fun i=> (a • x) i + (b • x) i := by ext i; rw [Pi.smul_apply, Pi.smul_apply]

      -- Convert x back to vectors.
  _ = a • x + b • x := by rw [← Pi.add_def]
