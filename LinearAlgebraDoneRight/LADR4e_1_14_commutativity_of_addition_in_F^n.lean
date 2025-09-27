------------------------------------------------------
-- 1.14 - commutativity of addition in 𝔽ⁿ
-- Follows the proof in the book step-by-step
------------------------------------------------------
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic

variable {𝔽 : Type*} [Field 𝔽]
variable {n : ℕ}
variable {x : Fin n → 𝔽}
variable {y : Fin n → 𝔽}

example : x + y = y + x := by
calc x + y
    = fun i => x i + y i  := by rw   [Pi.add_def]
  _ = fun i => (x + y) i  := by simp [Pi.add_apply]
  _ = fun i => (y + x) i  := by rw   [add_comm]
  _ = fun i => y i + x i  := by simp [Pi.add_apply]
  _ = y + x               := by rw   [Pi.add_def]
