import LinearAlgebraDoneRight.LADR4e_1_45_condition_for_a_direct_sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable (U W : Submodule 𝔽 V)

/-- Package two subspaces into a `Fin 2 → Submodule 𝔽 V` family. -/
def V₂ (U W : Submodule 𝔽 V) : Fin 2 → Submodule 𝔽 V
  | 0 => U
  | 1 => W

theorem if_2_subspace_intersect_only_zero_then_direct_sum :
  ((U : Set V) ∩ (W : Set V)) = ({0} : Set V) →
     IsDirectSum (V₂ (U := U) (W := W)) := by

  -- Using the imported 1.45 theorem, we can replace the direct sum goal
  -- a zero uniqueness goal since they are equivalent.
  rw [direct_sum_iff_zero_unique]
  -- New goal: ↑U ∩ ↑W = {0} → ZeroUniqueness (V₂ U W)

  intro h_intersect_is_zero

  intro vlist
  intro h_vlist_mem h_vlist_sum_zero

  -- `h_vlist_mem` gives us:
  have h_u_mem : vlist 0 ∈ U := by
      exact h_vlist_mem 0
  have h_w_mem : vlist 1 ∈ W := by
      exact h_vlist_mem 1

  -- `h_sum_zero_fin` gives us `u + w = 0`:
  have h_sum_zero : vlist 0 + vlist 1 = 0 := by
    -- Simplify the sum over `Fin 2`
    simp [Fin.sum_univ_two] at h_vlist_sum_zero
    exact h_vlist_sum_zero

-- "The equation above implies that u = -w."
  have h_u_eq_neg_w : vlist 0 = - (vlist 1) := by
    rw [add_eq_zero_iff_eq_neg] at h_sum_zero
    exact h_sum_zero

-- "...= -w ∈ W."
-- We show that `u` (which is `vlist 0`) is also in `W`.
  have h_u_in_W : vlist 0 ∈ W := by
    rw [h_u_eq_neg_w]
    -- Since `vlist 1 ∈ W`, `- (vlist 1)` is also in `W`.
    exact Submodule.neg_mem W h_w_mem

-- "Thus u ∈ U ∩ W."
  have h_u_in_intersect : vlist 0 ∈ (U : Set V) ∩ (W : Set V) := by
    --rw [Submodule.mem_inf]
    -- We have both `vlist 0 ∈ U` and `vlist 0 ∈ W`
    exact ⟨h_u_mem, h_u_in_W⟩

 -- "Hence u = 0"
  have h_u_is_zero : vlist 0 = 0 := by
    -- Our hypothesis `h_intersect_is_zero` means "any element in U ⊓ W is 0"
    rw [Set.mem_singleton_iff.symm]
    rw [← h_intersect_is_zero]
    -- Apply this to `vlist 0`
    exact h_u_in_intersect

  -- "...which... implies that w = 0"
  have h_w_is_zero : vlist 1 = 0 := by
    -- We know `vlist 0 + vlist 1 = 0`
    rw [h_u_is_zero] at h_sum_zero -- The equation becomes `0 + vlist 1 = 0`
    simp at h_sum_zero              -- This simplifies to `vlist 1 = 0`
    exact h_sum_zero

  -- "completing the proof."
  -- Our goal is `∀ i, vlist i = 0`. We show this for `i = 0` and `i = 1`.
  intro i
  fin_cases i
  · -- Case i = 0
    exact h_u_is_zero
  · -- Case i = 1
    exact h_w_is_zero
