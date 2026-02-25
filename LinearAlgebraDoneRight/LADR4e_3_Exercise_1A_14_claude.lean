import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
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
  -- Use funext to prove function equality by showing equality at each point
  funext i
  -- Now we need to show: (α • (x + y)) i = (α • x + α • y) i
  simp [Pi.smul_apply, Pi.add_apply, mul_add]
