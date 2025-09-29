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
      -- Convert vector x to functional form , scaled by (a*b).
    = fun i => (a * b) • (x i) := by rw [Pi.smul_def]

      -- Since (x i) ∈ 𝔽, scalar mult IS field mult
  _ = fun i => (a * b) * (x i) := by rfl

      -- Rearrange according to field associativity.
  _ = fun i => a * (b * (x i)) := by simp [mul_assoc]

      -- Convert back to scaler multiplication.
  _ = fun i => a • (b • (x i)) := by rfl

      -- Reduce x back to a vector.
  _ = a • (b • x) := by simp [Pi.smul_def]
