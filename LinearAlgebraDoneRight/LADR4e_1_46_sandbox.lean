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

  -- Break out the two vectors from vlist into `u` and `w` to make the
  -- correlation to the book more obvious.
  let u := vlist 0
  let w := vlist 1

  -- `h_vlist_mem` gives us:
  have h_u_mem : u ∈ U := by
      exact h_vlist_mem 0
  have h_w_mem : w ∈ W := by
      exact h_vlist_mem 1

  -- `h_vlist_sum_zero` gives us `u + w = 0`:
  have h_sum_zero : u + w = 0 := by
    -- Simplify the sum over `Fin 2`
    simp [Fin.sum_univ_two] at h_vlist_sum_zero
    exact h_vlist_sum_zero

-- "The equation above implies that u = -w."
  have h_u_eq_neg_w : u = -w := by
    calc u
        = u - 0       := by rw [sub_zero]
      _ = u - (u + w) := by rw [h_sum_zero]
      _ = -w          := by rw [sub_add_cancel_left]

-- "...= -w ∈ W."
-- We show that `u` is also in `W`.
  have h_u_in_W : u ∈ W := by
    rw [(h_u_eq_neg_w : u = -w)]
    -- New goal: -w ∈ W
    -- Since `w ∈ W`, `-w` is also in `W`.
    exact Submodule.neg_mem W h_w_mem

-- "Thus u ∈ U ∩ W."
  have h_u_in_intersect : u ∈ (U : Set V) ∩ (W : Set V) := by
    -- We have both `u ∈ U` and `u ∈ W`
    exact ⟨h_u_mem, h_u_in_W⟩

 -- "Hence u = 0"
  have h_u_is_zero : u = 0 := by
    rw [Set.mem_singleton_iff.symm] -- a ∈ {b} ↔ a = b
    -- New goal: u ∈ {0}
    rw [← h_intersect_is_zero]  -- ↑U ∩ ↑W = {0}
    -- New goal: u ∈ ↑U ∩ ↑W
    exact h_u_in_intersect

  -- Our goal is `∀ i, vlist i = 0`. We show this for `i = 0` and `i = 1`.
  intro i
  fin_cases i
  · -- **Case i = 0: vlist 0 = u = 0**
     -- "Hence u = 0"
     exact h_u_is_zero
  · -- **Case i = 1: vlist 1 = w = 0**
    -- "...which by the equation above implies that w = 0"
        calc w
      = 0 + w := by rw [right_eq_add]
    _ = u + w := by rw [h_u_is_zero]
    _ = 0     := by rw [h_sum_zero]

  -- "completing the proof."
