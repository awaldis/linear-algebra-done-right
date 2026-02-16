import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Exercise 1C.10 - Suppose 𝑉1 and 𝑉2 are subspaces of 𝑉.
Prove that the intersection 𝑉1 ∩ 𝑉2 is a subspace of 𝑉.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]

theorem intersection_of_subspaces_is_subspace (V₁ V₂ : Submodule 𝔽 V) :
  ∃ (S : Submodule 𝔽 V), (S : Set V) = (V₁ : Set V) ∩ (V₂ : Set V) := by
  -- Show that the set meets the conditions for a subspace.
  use {
    carrier := (V₁ : Set V) ∩ (V₂ : Set V)

    ----------------------------------------------------------------------------
    zero_mem' := by
       show 0 ∈ (V₁ : Set V) ∩ (V₂ : Set V)
       -- Since they are both subspaces, they must both contain the zero vector.
       exact ⟨V₁.zero_mem, V₂.zero_mem⟩

    ----------------------------------------------------------------------------
    add_mem' := by
      -- Goal: ∀ {a b : V}, a     ∈ ↑V₁ ∩ ↑V₂ →
      --                    b     ∈ ↑V₁ ∩ ↑V₂ →
      --                    a + b ∈ ↑V₁ ∩ ↑V₂
      intro a b
      intro (ha_in_intersect : a ∈ (V₁ : Set V) ∩ (V₂ : Set V))
      intro (hb_in_intersect : b ∈ (V₁ : Set V) ∩ (V₂ : Set V))

      -- New goal: show a + b ∈ (V₁ : Set V) ∩ (V₂ : Set V)

      -- Break out proofs that both a and b are members of both sets.
      rcases ha_in_intersect with ⟨ (a_in_V₁:a ∈ (V₁ : Set V)),
                                    (a_in_V₂:a ∈ (V₂ : Set V))⟩
      rcases hb_in_intersect with ⟨ (b_in_V₁:b ∈ (V₁ : Set V)),
                                    (b_in_V₂:b ∈ (V₂ : Set V))⟩

      -- Now prove that a + b is a member of each set
      exact ⟨V₁.add_mem a_in_V₁ b_in_V₁, V₂.add_mem a_in_V₂ b_in_V₂⟩

    ----------------------------------------------------------------------------
    smul_mem' := by
      -- Goal: ∀ (c : 𝔽) {x : V}, x ∈ ↑V₁ ∩ ↑V₂ →
      --                      c • x ∈ ↑V₁ ∩ ↑V₂
      intro c x
      intro h_x_in_intersect
      -- New goal: c • x ∈ ↑V₁ ∩ ↑V₂

      -- Break out proofs that x is a member of both sets.
      rcases h_x_in_intersect with ⟨ (x_in_V₁:x ∈ (V₁ : Set V)),
                                     (x_in_V₂:x ∈ (V₂ : Set V))⟩

      -- Now prove that c•x is a member of each set.
      exact ⟨V₁.smul_mem c x_in_V₁, V₂.smul_mem c x_in_V₂⟩
  }

  -- We have provided a witness S (via 'use').
  -- The remaining goal is to prove ↑S = ↑V₁ ∩ ↑V₂.
  -- Since we defined S.carrier := ↑V₁ ∩ ↑V₂, this reduces to "A = A".
  rfl
