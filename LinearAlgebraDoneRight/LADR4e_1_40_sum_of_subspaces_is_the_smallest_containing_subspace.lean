import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]

/-!
`sumSet Vᵢ` is the set of all finite sums `∑ i, f i` with each `f i ∈ Vᵢ i`.
-/
def sumSet {m : ℕ} (Vᵢ : Fin m → Submodule 𝔽 V) : Set V :=
  {x | ∃ f : Fin m → V, (∀ i, f i ∈ Vᵢ i) ∧ x = ∑ i, f i}

-- Let's consider a finite collection of m subspaces, indexed by Fin m.
variable {m : ℕ} (U : Fin m → Subspace 𝔽 V)

-- ##################################################################
-- Part 1: Show that the sum is a subspace (Explicit Proof)
-- ##################################################################

-- We first define the set of vectors that constitute the sum.
-- This is the set of all vectors `v` that can be written as a sum of
-- elements `f i`, where each `f i` is from the corresponding subspace `U i`.
-- def sum_carrier := {v : V | ∃ f : Fin m → V, (∀ i, f i ∈ U i) ∧ v = (Finset.univ).sum f}

-- Now, we prove that this set, equipped with the vector space operations,
-- forms a subspace by proving the three required properties.
theorem sum_is_subspace :
  ∃ (S : Submodule 𝔽 V), (S : Set V) = sumSet U := by

  -- We'll construct the subspace S by verifying all requirements
  use {

  -- The underlying set of vectors is the one defined above.
  carrier := sumSet U

  -- Proof 1: The subspace must contain the zero vector.
  zero_mem' := by
    show 0 ∈ sumSet U
    unfold sumSet
    -- Current goal: 0 ∈ {x | ∃ f, (∀ (i : Fin m), f i ∈ U i) ∧ x = ∑ i, f i}

    -- We need to show that `0` can be written as a sum of vectors from the subspaces.
    -- We can achieve this by picking the zero vector from each subspace `U i`.
    use (fun _ => 0) -- Use the function that maps every input to the zero vector `0`.
    -- Current goal: (∀ (i : Fin m), (fun x ↦ 0) i ∈ U i) ∧ 0 = ∑ i, (fun x ↦ 0) i
    -- We now have two goals:
    -- 1. Show that each component `0` is in the corresponding subspace `U i`.
    -- 2. Show that the sum of all these zero vectors is `0`.
    constructor
    · -- Goal 1: For any `i`, `0 ∈ U i`. This is true by the definition of a subspace.
      -- Current goal: ∀ (i : Fin m), 0 ∈ U i OR
      --               ∀ (i : Fin m), (fun x ↦ 0) i ∈ U i
      intro i
      -- Current goal: 0 ∈ U i
      exact (U i).zero_mem
    · -- Goal 2: The sum of `0`s is `0`.
      show 0 = ∑ i, 0
      exact Finset.sum_const_zero.symm

  -- Proof 2: The subspace must be closed under addition.
  add_mem' := by
    -- Current goal: ∀ {a b : V}, a ∈ sumSet U → b ∈ sumSet U → a + b ∈ sumSet U
    -- We take two arbitrary vectors `v₁` and `v₂` from our set.
    intro v₁ v₂

    -- Current goal: v₁ ∈ sumSet U → v₂ ∈ sumSet U → v₁ + v₂ ∈ sumSet U
    intro hv₁
    -- Current goal: v₂ ∈ sumSet U → v₁ + v₂ ∈ sumSet U
    intro hv₂
    -- Current goal: v₁ + v₂ ∈ sumSet U

    -- The assumption `hv₁` means `v₁` can be written as a sum using some function `f₁`.
    rcases hv₁ with ⟨f₁, hf₁_mem, hf₁_sum⟩
    -- The assumption `hv₂` means `v₂` can be written as a sum using some function `f₂`.
    rcases hv₂ with ⟨f₂, hf₂_mem, hf₂_sum⟩
    -- We need to show that `v₁ + v₂` can also be written as such a sum.
    -- We propose the function `f₁ + f₂`, which maps each index `i` to `f₁ i + f₂ i`.
    use (f₁ + f₂)
    -- Again, we have two goals:
    -- 1. Show that each component `f₁ i + f₂ i` is in the corresponding subspace `U i`.
    -- 2. Show that the sum of these components equals `v₁ + v₂`.
    constructor
    · -- Goal 1: For any `i`, show `f₁ i + f₂ i ∈ U i`.
      intro i
      -- Since `U i` is a subspace, it's closed under addition.
      -- We know `f₁ i ∈ U i` and `f₂ i ∈ U i`, so their sum is also in `U i`.
      exact (U i).add_mem (hf₁_mem i) (hf₂_mem i)

    · -- Goal 2: Show that the sum equals `v₁ + v₂`.
      calc v₁ + v₂
          = ∑ i, f₁ i + v₂        := by rw [hf₁_sum]
        _ = ∑ i, f₁ i + ∑ i, f₂ i := by rw [hf₂_sum]
        _ = ∑ i, (f₁ i + f₂ i)    := by rw [Finset.sum_add_distrib]
        _ = ∑ i, (f₁ + f₂) i      := by rw [Pi.add_def]

  -- Proof 3: The subspace must be closed under scalar multiplication.
  smul_mem' := by
    -- We take an arbitrary scalar `c` and a vector `v` from our set.
    intro c v hv
    -- The assumption `hv` means `v` can be written as a sum using some function `f`.
    rcases hv with ⟨f, hf_mem, hf_sum⟩
    -- We need to show `c • v` can be written as a sum.
    -- We propose the function `c • f`, which maps each index `i` to `c • f i`.
    use (c • f)
    -- Two goals, as before:
    -- 1. Show that each `c • f i` is in the subspace `U i`.
    -- 2. Show that the sum of these components equals `c • v`.
    constructor
    · -- Goal 1: For any `i`, show `c • f i ∈ U i`.
      intro i
      -- Since `U i` is a subspace, it's closed under scalar multiplication.
      -- We know `f i ∈ U i`, so `c • f i` is also in `U i`.
--        exact Subspace.smul_mem (U i) c (hf_mem i)
      exact (U i).smul_mem c (hf_mem i)
    · -- Goal 2: Show the sum equals `c • v`.
      -- We use the property that scalar multiplication distributes over a sum
      -- and substitute the known sum for `v`.
      calc c • v
        = c • ∑ i, f i   := by rw [hf_sum]
      _ = ∑ i, c • f i   := by rw [Finset.smul_sum]
      _ = ∑ i, (c • f) i := by rw [@Pi.smul_def]
  }
  rfl
