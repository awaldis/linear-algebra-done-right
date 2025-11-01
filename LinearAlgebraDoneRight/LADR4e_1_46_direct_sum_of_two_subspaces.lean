import LinearAlgebraDoneRight.LADR4e_1_45_condition_for_a_direct_sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
/-!
# Theorem 1.46 - Direct sum of two subspaces
Each direction of the iff is proved separately.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable (U W : Submodule 𝔽 V)

/-- Package two subspaces into a `Fin 2 → Submodule 𝔽 V` family.  This enables
this file to use imported definitions that are generalized to work with lists of
subspaces of **any** finite length.
-/
def V₂ (U W : Submodule 𝔽 V) : Fin 2 → Submodule 𝔽 V
  | 0 => U
  | 1 => W

theorem if_direct_sum_then_2_subspace_intersect_only_zero :
  IsDirectSum (V₂ (U := U) (W := W)) →
  ((U : Set V) ∩ (W : Set V)) = ({0} : Set V) := by

  -- Using the imported 1.45 theorem, we can replace the direct sum goal
  -- a zero uniqueness goal since they are equivalent.
  rw [direct_sum_iff_zero_unique]
  -- New goal: ZeroUniqueness (V₂ U W) → ↑U ∩ ↑W = {0}

  intro (h_zero_unique : ZeroUniqueness (V₂ U W))

  -- Introduce an arbitrary element of both sets
  -- Replaces the equality with a bidirectional membership statement (↔)
  ext v
  -- New goal: v ∈ ↑U ∩ ↑W ↔ v ∈ {0}

  -- To prove set equality, we show both inclusions
  constructor
  · -- First direction: v ∈ U ∩ W → v ∈ {0}

    intro ⟨h_v_in_U, h_v_in_W⟩
    -- New goal: v ∈ {0}

    -- This means v = 0 by:
    rw [Set.mem_singleton_iff] -- a ∈ {b} ↔ a = b
    -- New goal: v = 0

    -- Construct a vlist where vlist 0 = v and vlist 1 = -v
    let vlist : Fin 2 → V := fun i => if i = 0 then v else -v

    -- Show that this vlist has members in the right subspaces
    have h_vlist_mem : ∀ i, vlist i ∈ V₂ U W i := by
      intro i
      fin_cases i
      · -- Case i = 0: vlist 0 = v ∈ U
        simp only [vlist, V₂]
        exact h_v_in_U
      · -- Case i = 1: vlist 1 = -v ∈ W
        simp only [vlist, V₂]
        -- neg_mem proves (hx : x ∈ p) : -x ∈ p
        exact Submodule.neg_mem W h_v_in_W

    -- Show that this vlist sums to zero
    have h_vlist_sum_zero : ∑ i, vlist i = 0 := by
      rw [Fin.sum_univ_two]
      simp only [vlist]
      -- Goal: (if 0 = 0 then v else -v) + (if 1 = 0 then v else -v) = 0
      simp

    -- Apply h_zero_unique to conclude all components are zero
    have h_all_zero := h_zero_unique vlist h_vlist_mem h_vlist_sum_zero

    -- In particular, vlist 0 = v = 0
    have h_v_zero : vlist 0 = 0 := h_all_zero 0
    calc v = vlist 0 := by simp [vlist]
         _ = 0       := h_v_zero

  · -- Second direction: v ∈ {0} → v ∈ U ∩ W (trivial, since 0 is in both)
    intro h_v_in_singleton
    rw [Set.mem_singleton_iff] at h_v_in_singleton
    rw [h_v_in_singleton]
    constructor
    · exact Submodule.zero_mem U
    · exact Submodule.zero_mem W


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
