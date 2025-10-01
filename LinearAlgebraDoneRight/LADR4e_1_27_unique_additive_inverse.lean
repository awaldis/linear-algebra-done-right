------------------------------------------------------
-- 1.27 - unique additive inverse
-- Follows the proof in the book step-by-step
------------------------------------------------------
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable {v : V}
variable {w : V}  -- first candidate for additive inverse
variable {w' : V} -- second candidate for additive inverse

example
  -- `w` and `w'` are both additive inverses of `v`
  (h_w_add_inv : v + w = (0 : V))
  (h_w'_add_inv : v + w' = (0 : V))

  -- Show that w and w' must be identical.
  : w = w' := by
  calc w
      = w +    0     := by rw [add_zero]
    _ = w + (v + w') := by rw [h_w'_add_inv]
    _ = (w + v) + w' := by rw [add_assoc]
    _ = (v + w) + w' := by simp [add_comm]
    _ =    0    + w' := by rw [h_w_add_inv]
    _ =    w'   + 0  := by rw [add_comm]
    _ = w'           := by rw [add_zero]
