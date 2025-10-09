-----------------------------------------------------------
-- Exercise 1A-15 - distributivity of scalar multiplication
-- with respect to scalar addition in 𝔽ⁿ
-----------------------------------------------------------
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic

variable {𝔽 : Type*} [Field 𝔽]
variable {n : ℕ}
variable {x : Fin n → 𝔽}
variable {a : 𝔽}
variable {b : 𝔽}

example : (a + b) • x = a • x + b • x  := by
calc (a + b) • x
      -- Convert vector x to functional form.
    = (a + b) • fun i=>x i := by rfl

      -- Move the (a + b) inside the function, this is equivalent to
      -- multiplying each point in the vector individually.
      -- Since (x i) ∈ 𝔽, we can use field multiplication.
  _ = fun i=> (a + b) * (x i) := by rfl

      -- Use field distribution.
  _ = fun i=> a * (x i) + b * (x i) := by simp [right_distrib]

      -- Reduce x back to vectors.
  _ = a • x + b • x := by rfl
