import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Exercise 1C.11 - Prove that the intersection of every collection of subspaces
of 𝑉 is a subspace of 𝑉.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]
variable {ι : Type*} -- The index type (can be anything)

-- Given a collection of subspaces, define a symbol that stands for the
-- intersection of all the subspaces (considered as sets).
def intersect_set (Vᵢ : ι → Submodule 𝔽 V) : Set V :=
  {x | ∀ i, x ∈ Vᵢ i}

theorem intersection_of_n_subspaces_is_subspace (Vᵢ : ι → Submodule 𝔽 V) :
  ∃ (S : Submodule 𝔽 V), (S : Set V) = intersect_set Vᵢ := by
  -- Show that the set meets the conditions for a subspace.
  use {
    carrier := intersect_set Vᵢ

    ----------------------------------------------------------------------------
    zero_mem' := by
       show 0 ∈ intersect_set Vᵢ
       intro i
       -- Every subspace must contain the zero vector.
       exact (Vᵢ i).zero_mem

    ----------------------------------------------------------------------------
    add_mem' := by
      -- Goal: ∀ {a b : V}, a     ∈ intersect_set Vᵢ →
      --                    b     ∈ intersect_set Vᵢ →
      --                    a + b ∈ intersect_set Vᵢ
      intro a b
      intro (h_a_in_intersect : a ∈ intersect_set Vᵢ)
      intro (h_b_in_intersect : b ∈ intersect_set Vᵢ)
      intro i

      -- New goal: a + b ∈ Vᵢ i

      -- Since we have proof that a and b are individually members of all the
      -- subspaces, we can use "add_mem" to prove that a + b is also a
      -- member of all the subspaces.
      apply (Vᵢ i).add_mem
      · exact h_a_in_intersect  i
      · exact h_b_in_intersect  i

    ----------------------------------------------------------------------------
    smul_mem' := by
      -- Goal: ∀ (c : 𝔽) {x : V},     x ∈ intersect_set Vᵢ →
      --                          c • x ∈ intersect_set Vᵢ
      intro c x
      intro (h_x_in_intersect : x ∈ intersect_set Vᵢ)
      intro i
      -- New goal: c • x ∈ Vᵢ i

      -- Since we have proof that x is a member of all the subspaces, we can
      -- use "smul_mem" to prove that c • x is also a member of all the
      -- subspaces.
      apply (Vᵢ i).smul_mem c
      · exact h_x_in_intersect  i
  }

  -- We have provided a witness S (via 'use').
  -- The remaining goal is to prove ↑S = intersect_set.
  -- Since we defined S.carrier := intersect_set, this reduces to "A = A".
  rfl
