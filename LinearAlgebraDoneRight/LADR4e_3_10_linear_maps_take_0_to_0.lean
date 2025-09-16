------------------------------------------------------
-- 3.10 - linear maps take 0 to 0
------------------------------------------------------
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable {W : Type*} [AddCommGroup W] [Module 𝔽 W]

theorem linear_map_zero_to_zero (T : V →ₗ[𝔽] W) : T (0:V) = (0:W) :=
calc T (0:V)
    = T ((0:V) + (0:V))           := by rw [add_zero] -- a + 0 = a
  _ = T ((0:V) + (-0:V))          := by rw [SubNegZeroMonoid.neg_zero] -- 0 = -0
  _ = T (0:V)  + T (-0:V)         := by rw [@LinearMap.map_add] -- f (x + y) = f x + f y
  _ = T (0:V)  + -(T (0:V))       := by rw [@LinearMap.map_neg] -- f (-x) = -f x
  _ = (T (0:V):W)  + -(T (0:V):W) := by rw[] -- same expression with W types made explicit
    -- Both operands in the addition operation are type W so the result must be type W.
    -- The second operand is the additive inverse of the first so the result must be zero.
    -- Therefore, the result must be the zero vector in the W vector space.
  _ = (0:W)                       := by rw [@add_neg_eq_zero]
