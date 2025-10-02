------------------------------------------------------
-- 1.32 - the number -1 times a vector
------------------------------------------------------
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable {v : V}
variable {w : V} -- additive inverse of v as defined below

example
  -- define 'w' as the symbol for additive inverse of 'v'
  (h_w_add_inv : v + w = (0 : V))

  : (-1:𝔽) • v = w := by
  calc (-1:𝔽) • v
      =  (0:V)  + (-1:𝔽) • v := by rw [zero_add]
    _ = (v + w) + (-1:𝔽) • v   := by rw [h_w_add_inv]
    _ = (w + v) + (-1:𝔽) • v   := by simp [add_comm]
    _ =  w + v  + (-1:𝔽) • v   := by rw[]
    _ =  w + v  + -(1 • v)     := by simp [neg_smul]
    _ = w + (1 • v) + -(1 • v) := by rw [one_nsmul]
    _ = w                      := by rw [add_neg_cancel_right]
