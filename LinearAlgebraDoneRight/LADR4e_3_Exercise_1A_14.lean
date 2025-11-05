import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Action.Defs
/-!
# Exercise 1A.14 - distributivity of scalar multiplication
# with respect to vector addition in 𝔽ⁿ
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]
variable {n : ℕ}
variable {x : Fin n → 𝔽}
variable {y : Fin n → 𝔽}
variable {α : 𝔽} -- use α instead of λ since λ has special meaning in Lean.

theorem dist_of_smul_wrt_vec_add : α • (x + y) = α • x + α • y  := by
calc α • (x + y)
      -- Convert vectors x and y to functional form.
    = α • (fun i=>x i + y i)  := by rw [Pi.add_def]

      -- Move the scalar inside the function.
  _ = fun i=> α • (x i + y i) := by rw [Pi.smul_def]

      -- Convert to field multiplication.
  _ = fun i=> α * (x i + y i) := by ext i; rw [smul_eq_mul]

      -- Now we can use regular field distribution.
  _ = fun i=> (α * x i) + (α * y i) := by simp [left_distrib]

      -- Convert back to scalar multiplication.
  _ = fun i=> (α • x i) + (α • y i) := by ext i; rw [smul_eq_mul, smul_eq_mul]
  _ = fun i=> ((α • x) i) + ((α • y) i) := by ext i; rw [Pi.smul_apply, Pi.smul_apply]

      -- Convert x and y back to vectors without function extension.
  _ = α • x + α • y := by rw [← Pi.add_def]
