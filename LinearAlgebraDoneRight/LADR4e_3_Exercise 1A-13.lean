---------------------------------------------------------
-- Exercise 1A-13 - multiplicative identity in 𝔽ⁿ
---------------------------------------------------------
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic

variable {𝔽 : Type*} [Field 𝔽]
variable {n : ℕ}
variable {x : Fin n → 𝔽}

example : (1 : 𝔽) • x  = x := by
calc (1 : 𝔽) • x
      -- Convert vector x to functional form
    = (1 : 𝔽) • fun i=>(x i) := by rfl

      -- Move the 1 inside the function, this is equivalent to
      -- multiplying each point in the vector individually.
      -- Since (x i) ∈ 𝔽, we can use field multiplication.
  _ = fun i=> (1 : 𝔽) * (x i) := by rfl

      -- Multiplying by one gives the same value back.
  _ = fun i=>(x i) := by simp only [one_mul]

      -- Reduce x back to a vector.
  _ = x := by rfl
