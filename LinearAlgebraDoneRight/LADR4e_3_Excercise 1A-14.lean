-----------------------------------------------------------
-- Exercise 1A-14 - distributivity of scalar multiplication
-- with respect to vector addition in 𝔽ⁿ
-----------------------------------------------------------
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic

variable {𝔽 : Type*} [Field 𝔽]
variable {n : ℕ}
variable {x : Fin n → 𝔽}
variable {y : Fin n → 𝔽}
variable {α : 𝔽} -- use α instead of λ since λ has special meaning in Lean.

example : α • (x + y) = α • x + α • y  := by
calc α • (x + y)
      -- Convert vector x + y to functional form.
    = α • fun i=>(x + y) i := by rfl

      -- Move the α inside the function, this is equivalent to
      -- multiplying each point in the vector individually.
      -- Since ((x + y) i) ∈ 𝔽, we can use field multiplication.
  _ = fun i=> α * (x + y) i := by rfl

      -- Index x and y separately.
  _ = fun i=> α * (x i + y i) := by rfl

      -- Use field distribution
  _ = fun i=> (α * x i) + (α * y i) := by simp [left_distrib]

      -- Reduce x and y back to a vectors.
  _ = α • x + α • y := by rfl
