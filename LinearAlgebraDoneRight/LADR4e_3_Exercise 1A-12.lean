---------------------------------------------------------
-- Exercise 1A.12 - associativity of multiplication in 𝔽ⁿ
---------------------------------------------------------
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic

variable {𝔽 : Type*} [Field 𝔽]
variable {n : ℕ}
variable {x : Fin n → 𝔽}
variable {a : 𝔽}
variable {b : 𝔽}

example : (a * b) • x  = a • (b • x) := by
calc (a * b) • x
      -- Convert vector x to functional form
    = (a * b) • fun i=>(x i) := by rfl

      -- Move the (a * b) inside the function, this is equivalent to
      -- multiplying each point in the vector individually.
      -- Since (x i) ∈ 𝔽, we can use field multiplication.
  _ = fun i=>(a * b) * (x i) := by rfl

      -- Rearrange according to field associativity.
  _ = fun i=>a * (b * (x i)) := by simp [mul_assoc]

      -- Move the "a" back outside the function.
  _ = a • fun i=>(b * (x i))  := by rfl

      -- Move the "b" back outside the function.
  _ = a • ( b • fun i=>(x i))  := by rfl

      -- Reduce x back to a vector.
  _ = a • (b • x) := by rfl
