import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic
/-!
# Exercise 1B.1 - Prove that -(-v)=v for every v ∈ V
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable {v : V}

theorem double_negative_equals_positive : -(-v) = v := by
  calc -(-v)
      = -(-v) + (0:V)      := by rw [add_zero]
    _ = -(-v) + (-v + v)   := by rw [neg_add_cancel]
    _ = (-(-v) + (-v)) + v := by rw [add_assoc]
    _ =        0       + v := by rw [neg_add_cancel]
    _ = v                  := by rw [zero_add]
