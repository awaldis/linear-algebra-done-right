-------------------------------------------------------------
-- 1.30 - the number zero times any vector is the zero vector
-------------------------------------------------------------
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable {v : V}

example
  : (0:𝔽) • v = (0:V) := by
  calc (0:𝔽) • (v : V)
      = ((0:𝔽) + (0:𝔽)) • v                    := by rw[add_zero]
    _ = (0:𝔽) • v + (0:𝔽) • v                  := by rw[add_smul]
    _ = (0:𝔽) • v + -(0:𝔽) • v                 := by rw[neg_zero]
    _ = (0:𝔽) • v + -((0:𝔽) • v)               := by rw[neg_smul]
      -- same expression with V types made explicit
    _ = (((0:𝔽) • v) : V) + -(((0:𝔽) • v) : V) := by rw[]
    -- Both operands in the addition operation are type V so the result must be
    -- type V.
    -- The second operand is the additive inverse of the first so the result
    -- must be zero.
    -- Therefore, the result must be the zero vector in the V vector space.
    _ = (0:V)                                := by rw[add_neg_eq_zero]
