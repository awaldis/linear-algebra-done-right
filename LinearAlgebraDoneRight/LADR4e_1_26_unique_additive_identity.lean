------------------------------------------------------
-- 1.26 - unique additive identity
-- Follows the proof in the book step-by-step
------------------------------------------------------
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable {zero' : V} -- candidate second additive identity

example
  -- zero' is an additive identity
  (h_zero'_add_id : ∀ v : V, v + zero' = v)

  -- Show that zero' and the original zero are identical.
  : zero' = (0 : V) := by
  calc zero'
      = zero' + 0 := by rw [add_zero]
    _ = 0 + zero' := by rw [add_comm]
    _ = (0 : V)   := by simpa using h_zero'_add_id
