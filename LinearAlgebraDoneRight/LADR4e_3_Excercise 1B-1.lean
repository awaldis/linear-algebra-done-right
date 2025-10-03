------------------------------------------------------
-- Exercise 1B-1 - Prove that -(-v)=v for every v ∈ V
------------------------------------------------------
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable {v : V}

example : -(-v) = v := by
  calc -(-v)
      = -(-v) + (0:V)      := by rw [add_zero]
    _ = -(-v) + (-v + v)   := by rw [neg_add_cancel]
    _ = (-(-v) + (-v)) + v := by rw [add_assoc]
    _ =        0       + v := by rw [neg_add_cancel]
    _ = v                  := by rw [zero_add]
