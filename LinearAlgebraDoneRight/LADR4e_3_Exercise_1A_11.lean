------------------------------------------------------
-- Exercise 1A.11 - associativity of addition in 𝔽ⁿ
------------------------------------------------------
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic

variable {𝔽 : Type*} [Field 𝔽]
variable {n : ℕ}
variable {x : Fin n → 𝔽}
variable {y : Fin n → 𝔽}
variable {z : Fin n → 𝔽}

example : (x + y) + z = x + (y + z) := by
calc (x + y) + z
    = fun i => ((x + y) + z ) i := by rw [Pi.add_def]
  _ = fun i => (x + (y + z)) i  := by rw [add_assoc]
  _ = x + (y + z)               := by rw [Pi.add_def]
