import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]

/-!
# Theorem 1.45 - Condition for a direct sum

## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024

A sum V₁ + ... + Vₘ is a direct sum if and only if the only way to write
0 as a sum v₁ + ... + vₘ, where each vₖ ∈ Vₖ, is by taking each vₖ equal to 0.
-/

--------------------------------------------------------------------------------
-- Let's consider a finite collection of m subspaces, indexed by Fin m.
variable {m : ℕ} (Vᵢ : Fin m → Submodule 𝔽 V)

/-- An element is in the sum V₁ + ... + Vₘ if it can be written as
a sum of elements from each Vᵢ.
-/
def InSumOfSubspaces (v : V) : Prop :=
  ∃ (vlist : Fin m → V), (∀ i, vlist i ∈ Vᵢ i) ∧ v = ∑ i, vlist i

--------------------------------------------------------------------------------
/-- The sum V₁ + ... + Vₘ is a direct sum if every element in the sum
can be written uniquely as a sum of elements from the Vᵢ.
-/
def IsDirectSum : Prop :=
  ∀ v : V, InSumOfSubspaces Vᵢ v →
    ∃! (vlist : Fin m → V), (∀ i, vlist i ∈ Vᵢ i) ∧ v = ∑ i, vlist i

/-- The only way to write 0 as a sum v₁ + ... + vₘ with each vₖ ∈ Vₖ
is by taking each vₖ equal to 0.
-/
def ZeroUniqueness : Prop :=
  ∀ (vlist : Fin m → V), (∀ i, vlist i ∈ Vᵢ i) →
    (∑ i, vlist i = 0) → (∀ i, vlist i = 0)

--------------------------------------------------------------------------------
/-- Theorem 1.45: V₁ + ... + Vₘ is a direct sum if and only if
the only way to write 0 as a sum is with all components equal to 0.
-/
theorem direct_sum_iff_zero_unique :
  IsDirectSum Vᵢ ↔ ZeroUniqueness Vᵢ := by

  constructor

  ------------------------------------------------------------------------------
  -- PART 1: Direct sum implies zero has unique representation
  -- "First suppose V₁ + ... + Vₘ is a direct sum."
  ------------------------------------------------------------------------------
  · --This goal: IsDirectSum Vᵢ → ZeroUniqueness Vᵢ
    intro (h_direct : IsDirectSum Vᵢ)
    -- We need to prove: ZeroUniqueness Vᵢ
    unfold ZeroUniqueness

    intro (vlist : Fin m → V)
    intro (h_vlist_mem : ∀ i, vlist i ∈ Vᵢ i)
    intro (h_vlist_sum_zero : ∑ i, vlist i = 0)
    -- Goal: ∀ i, vlist i = 0

    -- "Then the definition of direct sum implies that the only way to write 0
    -- as a sum v₁ + ... + vₘ, where each vₖ ∈ Vₖ, is by taking each vₖ equal to 0."

    -- Since 0 is in the sum (every subspace contains 0)
    have h_zero_in_sum : InSumOfSubspaces Vᵢ 0 := by
      unfold InSumOfSubspaces
      use fun i => 0
      constructor
      · intro i
        exact Submodule.zero_mem (Vᵢ i)
      · simp

    -- By the direct sum property, 0 has a unique representation
    unfold IsDirectSum at h_direct
    obtain ⟨zero_rep, h_zero_rep, h_unique⟩ := h_direct 0 h_zero_in_sum

    -- Extract properties of zero_rep
    obtain ⟨h_zero_rep_mem, h_zero_rep_sum⟩ := h_zero_rep

    -- We know that all zeros is one way to write 0
    have h_all_zeros_works : (fun i => 0) = zero_rep := by
      -- Apply uniqueness
      apply h_unique
      constructor
      · -- Show that the all-zeros function gives vectors in the right subspaces
        intro i
        exact Submodule.zero_mem (Vᵢ i)
      · -- Show that the sum of all zeros is 0
        simp

    -- But vlist also sums to 0 and has elements in the right subspaces
    have h_vlist_equals_zero_rep : vlist = zero_rep := by
      -- Apply uniqueness again
      apply h_unique
      exact ⟨h_vlist_mem, h_vlist_sum_zero.symm⟩

    -- Therefore vlist equals the all-zeros function
    intro i
    calc vlist i = zero_rep i := by rw [h_vlist_equals_zero_rep]
               _ = (fun i => 0) i := by rw [← h_all_zeros_works]
               _ = 0 := by rfl

  ------------------------------------------------------------------------------
  -- PART 2: Zero uniqueness implies direct sum
  -- "Now suppose that the only way to write 0 as a sum v₁ + ... + vₘ, where
  -- each vₖ ∈ Vₖ, is by taking each vₖ equal to 0."
  ------------------------------------------------------------------------------
  · --This goal: ZeroUniqueness Vᵢ → IsDirectSum Vᵢ
    intro (h_zero_unique : ZeroUniqueness Vᵢ)
    -- We need to prove: IsDirectSum Vᵢ
    unfold IsDirectSum

    intro v
    intro (h_v_in_sum : InSumOfSubspaces Vᵢ v)

    -- "To show that V₁ + ... + Vₘ is a direct sum, let v ∈ V₁ + ... + Vₘ."
    -- "We can write v = v₁ + ... + vₘ for some v₁ ∈ V₁,...,vₘ ∈ Vₘ."

    -- Since v is in the sum, it has at least one representation
    have h_a_vector_list_exists : ∃ vlist : Fin m → V, (∀ i, vlist i ∈ Vᵢ i) ∧ v = ∑ i, vlist i
      := by
      -- This follows directly from the definition of being in the sum
      unfold InSumOfSubspaces at h_v_in_sum
      exact h_v_in_sum

    obtain ⟨vlist, h_vlist_mem, h_vlist_sum⟩ := h_a_vector_list_exists

    -- Now we need to show this representation is unique
    use vlist

    constructor
    · -- First show that vlist works
      exact ⟨h_vlist_mem, h_vlist_sum⟩

    · -- "To show that this representation is unique, suppose we also have
      -- v = u₁ + ... + uₘ, where u₁ ∈ V₁,...,uₘ ∈ Vₘ."
      intro ulist
      intro ⟨h_ulist_mem, h_ulist_sum⟩

      -- "Subtracting these two equations, we have
      -- 0 = (v₁ - u₁) + ... + (vₘ - uₘ)."
      have h_sum_of_diffs_is_zero : ∑ i, (vlist i - ulist i) = 0 := by
        calc ∑ i, (vlist i - ulist i)
            = ∑ i, vlist i - ∑ i, ulist i := by rw [← Finset.sum_sub_distrib]
          _ =      v       - ∑ i, ulist i := by rw [h_vlist_sum]
          _ =      v       -      v       := by rw [h_ulist_sum]
          _ =              0              := by rw [sub_eq_zero]

      -- "Because v₁ - u₁ ∈ V₁,...,vₘ - uₘ ∈ Vₘ..."
      have h_diff_mem : ∀ i, vlist i - ulist i ∈ Vᵢ i := by
        intro i
        -- Each Vᵢ is a subspace, so closed under subtraction
        exact Submodule.sub_mem (Vᵢ i) (h_vlist_mem i) (h_ulist_mem i)

      -- "...the equation above implies that each vₖ - uₖ equals 0."
      unfold ZeroUniqueness at h_zero_unique

      -- All the differences are members of their respective subspaces and those differences
      -- sum to zero.  Since uniqueness of the summands that sum to zero is a given
      -- (0+...+0 = 0), then all the differences must be zero.
      have h_all_diffs_zero := h_zero_unique (fun i => vlist i - ulist i)
                                             h_diff_mem
                                             h_sum_of_diffs_is_zero

      -- "Thus v₁ = u₁,...,vₘ = uₘ, as desired."
      ext i
      -- Goal: vlist i = ulist i
      have h_diff_zero : vlist i - ulist i = 0 := h_all_diffs_zero i
      calc ulist i
          = (0:V)               + ulist i  := by rw [zero_add]
        _ = (vlist i - vlist i) + ulist i  := by simp only [sub_self]
        _ =  vlist i - (vlist i - ulist i) := by rw [sub_add]
        _ =  vlist i - (0:V)               := by rw [h_diff_zero]
        _ =  vlist i                       := by rw [sub_eq_self]
