import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Exercise 1C.12 - Prove that the union of two subspaces of 𝑉 is a subspace
of 𝑉 if and only if one of the subspaces is contained in the other.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]

theorem union_is_subspace_iff (U W : Submodule 𝔽 V) :
  (∃ S : Submodule 𝔽 V, (S : Set V) = (U : Set V) ∪ (W : Set V)) ↔
                                                 (U ≤ W ∨ W ≤ U) := by
  constructor
  · -- FORWARD DIRECTION (⇒): If the union is a subspace, U ⊆ W or W ⊆ U.
    intro ⟨S, h_S_is_union_of_U_and_W⟩

    -- We use classical logic: Either U ≤ W is true, or it is false.
    by_cases hUW : U ≤ W
    · -- If U ≤ W is true, then the left side is proven immediately.
      exact Or.inl (hUW : U ≤ W)
    · -- If U ≤ W is false, then we must prove W ≤ U.
      apply Or.inr
      -- New goal: W ≤ U

      intro w (hw : w ∈ W)
      -- New goal:  w ∈ U

      -- In this branch we have ¬(U ≤ W), so there must exist some u ∈ U such
      -- that u ∉ W.  Let's prove it so we can use it.
      have h_at_least_one_u_not_in_W : ∃ u, u ∈ U ∧ u ∉ W := by
        -- Assume the opposite of the goal and show that it leads to a
        -- contradiction.
        by_contra h_no_u_not_in_W
        -- New goal: False
        -- Change the ¬∃ to ∀
        push_neg at h_no_u_not_in_W
        apply (hUW : ¬U ≤ W)
        -- New Goal: U ≤ W
        intro x (hx : x ∈ U)
        -- New goal: x ∈ W
        exact h_no_u_not_in_W x (hx : x ∈ U)

      -- Let's extract that specific element 'u'
      rcases h_at_least_one_u_not_in_W with ⟨u, h_u_in_U, h_u_not_in_W⟩

      -- Since u is in U, we can obtain a proof that u is in S.
      have h_u_in_S : u ∈ S := by
        -- Explicitly expose the set coercion so `rw` can find ↑S
        change u ∈ (S : Set V)
        rw [h_S_is_union_of_U_and_W, Set.mem_union]
        exact Or.inl h_u_in_U

      -- Since w is in W, we can obtain a proof that w is in S.
      have h_w_in_S : w ∈ S := by
        change w ∈ (S : Set V)
        rw [h_S_is_union_of_U_and_W, Set.mem_union]
        exact Or.inr hw

      -- Since S is a subspace, it is closed under addition.  So we can obtain
      -- a proof that the sum of two of it's members is also a member.
      have h_uw_sum_in_S : u + w ∈ S := S.add_mem h_u_in_S h_w_in_S

      -- Since S = U ∪ W, the sum u + w must be in U or in W.
      have h_uw_sum_in_union : u + w ∈ (U : Set V) ∪ (W : Set V) := by
        rw [← h_S_is_union_of_U_and_W]
        exact h_uw_sum_in_S

      -- Explicitly state the union as an 'Or' statement
      change (u + w ∈ U) ∨ (u + w ∈ W) at h_uw_sum_in_union

      -- Obtain a proof that (u + w) cannot be in W
      have h_uw_sum_not_in_W : u + w ∉ W := by
        -- In Lean, '∉' means 'implies False'. So we assume it is in W.
        intro (h_uw_sum_in_W : u + w ∈ W)
        --New goal: False

        -- If (u + w) ∈ W, then u = (u + w) - w must be in W.
        have hu_eq : u = (u + w) - w := by simp
        have h_u_in_W : u ∈ W := by
          rw [hu_eq]  -- New goal: u + w - w ∈ W
          exact W.sub_mem (h_uw_sum_in_W : u + w ∈ W) (hw : w ∈ W)

        -- This contradicts our earlier fact that u ∉ W.
        -- 'h_u_not_in_W' is a function that expects a proof of 'u ∈ W' to
        -- produce 'False'
        exact (h_u_not_in_W : u ∉ W) (h_u_in_W : u ∈ W)

      -- Use Disjunctive Syllogism to conclude (u + w) ∈ U
      -- Since we have (a ∨ b) and (¬b), Or.resolve_right gives us a.
      have h_uw_in_U : u + w ∈ U := Or.resolve_right
                            (h_uw_sum_in_union : u + w ∈ U ∨ u + w ∈ W)
                            (h_uw_sum_not_in_W :             u + w ∉ W)

      -- Now that we solidly have (u + w) ∈ U, we subtract u to get w ∈ U.
      have hw_eq : w = (u + w) - u := by simp
      -- Current goal: w ∈ U
      rw [hw_eq]
      -- New goal: u + w - u ∈ U
      exact U.sub_mem (h_uw_in_U : u + w ∈ U) (h_u_in_U : u ∈ U)
  -----------------------------------------------------------------------------
  · -- REVERSE DIRECTION (⇐): If U ⊆ W or W ⊆ U, the union is a subspace.
    -- This direction is pretty trivial since, on both sides of the OR, one
    -- subspace is completely contained by the other.  And we already know
    -- they are both subspaces.
    rintro ( (hUW : U ≤ W) | (hWU : W ≤ U) )
    · -- Case U ⊆ W: The union U ∪ W is just W.
      -- Goal: ∃ S, ↑S = ↑U ∪ ↑W
      use W
      -- New goal: ↑W = ↑U ∪ ↑W

      -- Set.union_eq_right.mpr proves (U ∪ W = W) given U ⊆ W.
      -- We add .symm to flip it to (W = U ∪ W) to match our exact goal.
      exact (Set.union_eq_right.mpr (hUW : U ≤ W)).symm

    · -- Case W ⊆ U: The union U ∪ W is just U.
      use U
      exact (Set.union_eq_left.mpr hWU).symm
