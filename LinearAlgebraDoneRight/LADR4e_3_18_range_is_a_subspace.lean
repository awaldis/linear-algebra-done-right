------------------------------------------------------
-- 3.18 - the range is a subspace
-- In order to be a subspace of W, the range of T must follow these three
-- conditions:
-- rangeT contains additive identity (clearly follows from theorem 3.10)
-- rangeT closed under addition (shown below)
-- rangeT closed under scalar multiplication (shown below)
------------------------------------------------------
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable {W : Type*} [AddCommGroup W] [Module 𝔽 W]
variable (T : V →ₗ[𝔽] W)

------------------------------------------------------
-- rangeT closed under addition
------------------------------------------------------
example (w₁ w₂ : W) : w₁ ∈ {w | ∃ v, T v = w} →
                      w₂ ∈ {w | ∃ v, T v = w} →
                 w₁ + w₂ ∈ {w | ∃ v, T v = w} := by
  intro h_w₁_in_range_of_T
  intro h_w₂_in_range_of_T
  rcases h_w₁_in_range_of_T with ⟨v₁, h_Tv₁_produces_w₁⟩
  rcases h_w₂_in_range_of_T with ⟨v₂, h_Tv₂_produces_w₂⟩
  use v₁ + v₂
  -- New Goal: T (v₁ + v₂) = w₁ + w₂
  calc T (v₁ + v₂)
    = T v₁ + T v₂ := by rw [LinearMap.map_add]
    _ = w₁ + T v₂ := by rw [h_Tv₁_produces_w₁]
    _ = w₁ + w₂   := by rw [h_Tv₂_produces_w₂]
  -- Since (T (v₁ + v₂) ∈ range T)) and T (v₁ + v₂) = w₁ + w₂
  -- then (w₁ + w₂) ∈ range T

------------------------------------------------------
-- rangeT closed under scalar multiplication
------------------------------------------------------
example (c : 𝔽) (w : W) : w ∈ {w | ∃ v, T v = w} →
                      c • w ∈ {w | ∃ v, T v = w} := by
  intro h_w_in_range_of_T
  rcases h_w_in_range_of_T with ⟨v, h_Tv_produces_w⟩
  use c • v
  -- New Goal: T (c • v) = c • w
  calc T (c • v)
      = c • T v := by rw [LinearMap.map_smul]
    _ = c • w   := by rw [h_Tv_produces_w]
  -- Since (T (c • v)) ∈ range T)) and T (c • v)) = c • w
  -- then (c • w)) ∈ range T
