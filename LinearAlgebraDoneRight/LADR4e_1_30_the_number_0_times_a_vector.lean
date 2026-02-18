import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic
/-!
# Theorem 1.30 - The number zero times any vector is the zero vector.
0𝑣 = 0 for every 𝑣 ∈ 𝑉
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable {v : V}

-- Key step - "add_smul" (scalar multiplication distributes over scalar
-- addition) turns scalar multiplication to vector addition.  From there
-- we show one vector is the additive inverse of the other.

theorem scalar_0_times_any_vector_is_0 : (0:𝔽) • v = (0:V) := by
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
