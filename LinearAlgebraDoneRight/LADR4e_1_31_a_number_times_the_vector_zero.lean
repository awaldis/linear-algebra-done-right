-------------------------------------------------------------
-- 1.31 - a number times the vector 0
-------------------------------------------------------------
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable {a : 𝔽}

example
  : a • (0:V) = (0:V) := by
  calc a • (0:V)
      = a • ((0:V) + (0:V))      := by rw[add_zero]
    _ = a • (0:V) + a • (0:V)    := by rw[smul_add]
    _ = a • (0:V) + a • (-0:V)   := by rw[neg_zero]
    _ = a • (0:V) + -(a • (0:V)) := by rw[smul_neg]
      -- same expression with V types made explicit
    _ = (a • (0:V) : V) + -(a • (0:V) : V) := by rw[]
    -- Both operands in the addition operation are type V so the result must be
    -- type V.
    -- The second operand is the additive inverse of the first so the result
    -- must be zero.
    -- Therefore, the result must be the zero vector in the V vector space.
    _ = (0:V) := by rw[add_neg_eq_zero]
