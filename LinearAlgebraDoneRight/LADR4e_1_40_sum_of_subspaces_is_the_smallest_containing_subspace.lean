import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]

/-!
`sumSet Vᵢ` is the set of all finite sums `∑ i, vector_list i` with each vector
chosen, one each, from a list of subspaces (`Vᵢ`)
 `vector_list i ∈ Vᵢ i`.
-/
def sumSet {m : ℕ} (Vᵢ : Fin m → Submodule 𝔽 V) : Set V :=
  {x | ∃ vector_list : Fin m → V, (∀ i, vector_list i ∈ Vᵢ i) ∧
   x = ∑ i, vector_list i}

-- Let's consider a finite collection of m subspaces, indexed by Fin m.
variable {m : ℕ} (Vᵢ : Fin m → Subspace 𝔽 V)

-- ##################################################################
-- Part 1: Show that the sum is a subspace (Explicit Proof)
-- ##################################################################

-- We first define the set of vectors that constitute the sum.
-- This is the set of all vectors `v` that can be written as a sum of
-- elements `f i`, where each `f i` is from the corresponding subspace `Vᵢ i`.
-- def sum_carrier := {v : V | ∃ f : Fin m → V, (∀ i, f i ∈ Vᵢ i) ∧ v = (Finset.univ).sum f}

-- Now, we prove that this set, equipped with the vector space operations,
-- forms a subspace by proving the three required properties.
theorem sum_is_subspace :
  ∃ (S : Submodule 𝔽 V), (S : Set V) = sumSet Vᵢ := by

  -- We'll construct the subspace S by verifying all requirements
  use {

  -- The underlying set of vectors is the one defined above.
  carrier := sumSet Vᵢ

  -- Proof 1: The subspace must contain the zero vector.
  zero_mem' := by
    show 0 ∈ sumSet Vᵢ
    unfold sumSet
    -- Current goal: 0 ∈ {x | ∃ f, (∀ (i : Fin m), f i ∈ Vᵢ i) ∧ x = ∑ i, f i}

    -- We need to show that `0` can be written as a sum of vectors from the subspaces.
    -- We can achieve this by picking the zero vector from each subspace `Vᵢ i`.
    use (fun _ => 0) -- Use the function that maps every input to the zero vector `0`.
    -- Current goal: (∀ (i : Fin m), (fun x ↦ 0) i ∈ Vᵢ i) ∧ 0 = ∑ i, (fun x ↦ 0) i
    -- We now have two goals:
    -- 1. Show that each component `0` is in the corresponding subspace `Vᵢ i`.
    -- 2. Show that the sum of all these zero vectors is `0`.
    constructor
    · -- Goal 1: For any `i`, `0 ∈ Vᵢ i`. This is true by the definition of a subspace.
      -- Current goal: ∀ (i : Fin m), 0 ∈ Vᵢ i OR
      --               ∀ (i : Fin m), (fun x ↦ 0) i ∈ Vᵢ i
      intro i
      -- Current goal: 0 ∈ Vᵢ i
      exact (Vᵢ i).zero_mem
    · -- Goal 2: The sum of `0`s is `0`.
      show 0 = ∑ i, 0
      exact Finset.sum_const_zero.symm

  -- Proof 2: The subspace must be closed under addition.
  add_mem' := by
    -- Current goal: ∀ {a b : V}, a ∈ sumSet Vᵢ → b ∈ sumSet Vᵢ → a + b ∈ sumSet Vᵢ
    -- We take two arbitrary vectors `v₁` and `v₂` from our set.
    intro v₁ v₂

    -- New goal: v₁ ∈ sumSet Vᵢ → v₂ ∈ sumSet Vᵢ → v₁ + v₂ ∈ sumSet Vᵢ
    intro (hv₁_in_set : v₁ ∈ sumSet Vᵢ)
    -- New goal: v₂ ∈ sumSet Vᵢ → v₁ + v₂ ∈ sumSet Vᵢ
    intro (hv₂_in_set : v₂ ∈ sumSet Vᵢ)
    -- New goal: v₁ + v₂ ∈ sumSet Vᵢ

    -- Since v₁ is in the set, we can extract assumptions based on the set definition.
    rcases hv₁_in_set with ⟨
      -- There exists a list of vectors associated with v₁ that meet the other criteria.
      (v₁list : Fin m → V),
      -- We can prove that each vector in the list is a member of it's respective subspace.
      (hv₁list_mem : ∀ (i : Fin m), v₁list i ∈ Vᵢ i),
      -- We can prove that summing the list of vectors produces v₁.
      (hv₁list_sum : v₁ = ∑ i, v₁list i)⟩

    -- The assumption `hv₂` means `v₂` can be written as a sum using some function `f₂`.
    rcases hv₂_in_set with ⟨f₂, hf₂_mem, hf₂_sum⟩

    -- We need to show that `v₁ + v₂` can also be written as such a sum.
    -- We propose the function `v₁list + f₂`, which maps each index `i` to `v₁list i + f₂ i`.
    use (v₁list + f₂)

    -- Again, we have two goals:
    -- 1. Show that each component `v₁list i + f₂ i` is in the corresponding subspace `Vᵢ i`.
    -- 2. Show that the sum of these components equals `v₁ + v₂`.
    constructor
    · -- Goal 1: For any `i`, show `v₁list i + f₂ i ∈ Vᵢ i`.
      intro i
      -- Since each `Vᵢ i` is a subspace, they are all closed under addition.
      -- We know `v₁list i ∈ Vᵢ i` and `f₂ i ∈ Vᵢ i`, so their sum is also in `Vᵢ i`.
      exact (Vᵢ i).add_mem (hv₁list_mem i) (hf₂_mem i)

    · -- Goal 2: Show that the sum equals `v₁ + v₂`.
      calc v₁ + v₂
          = ∑ i, v₁list i + v₂        := by rw [hv₁list_sum]
        _ = ∑ i, v₁list i + ∑ i, f₂ i := by rw [hf₂_sum]
        _ = ∑ i, (v₁list i + f₂ i)    := by rw [Finset.sum_add_distrib]
        _ = ∑ i, (v₁list + f₂) i      := by rw [Pi.add_def]

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
    -- 1. Show that each `c • f i` is in the subspace `Vᵢ i`.
    -- 2. Show that the sum of these components equals `c • v`.
    constructor
    · -- Goal 1: For any `i`, show `c • f i ∈ Vᵢ i`.
      intro i
      -- Since `Vᵢ i` is a subspace, it's closed under scalar multiplication.
      -- We know `f i ∈ Vᵢ i`, so `c • f i` is also in `Vᵢ i`.
--        exact Subspace.smul_mem (Vᵢ i) c (hf_mem i)
      exact (Vᵢ i).smul_mem c (hf_mem i)
    · -- Goal 2: Show the sum equals `c • v`.
      -- We use the property that scalar multiplication distributes over a sum
      -- and substitute the known sum for `v`.
      calc c • v
        = c • ∑ i, f i   := by rw [hf_sum]
      _ = ∑ i, c • f i   := by rw [Finset.smul_sum]
      _ = ∑ i, (c • f) i := by rw [@Pi.smul_def]
  }
  rfl
