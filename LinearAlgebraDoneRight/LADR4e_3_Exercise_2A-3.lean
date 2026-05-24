import LinearAlgebraDoneRight.LADR4e_2_6_span_is_the_smallest_containing_subspace
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic  -- Needed for "ring"

set_option linter.style.emptyLine false

/-!
# Exercise 2A.3 - Prove or give a counterexample: If 𝑣₁, 𝑣₂, 𝑣₃, 𝑣₄ spans 𝑉,
# then the list 𝑣₁ − 𝑣₂, 𝑣₂ − 𝑣₃, 𝑣₃ − 𝑣₄, 𝑣₄ also spans 𝑉.
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]

variable {n : ℕ}
variable {v₁ v₂ v₃ v₄ : Fin n → 𝔽}

-- ═══════════════════════════════════════════════════════════════════════════
-- Define how to derive the "w" list from the "v" list.
-- ═══════════════════════════════════════════════════════════════════════════
def w_list {m : ℕ} (v_list : Fin m → V) : Fin m → V :=
  -- Since the input is (Fin m), k can be any value from 0 to m - 1
  -- We want the value of i to range from 0 to k so it needs to be type
  -- Fin (k.val + 1).
  -- We use k.val to coerce k to a ℕ.  We want to make clear that we want
  -- natural number arithmetic done here and not Fin m arithmetic.
  -- i needs to be coerced to Fin m so v_list can be applied to it.
  -- Fin.castLE can do that since k.isLt proves that k.val is less than
  -- m (Lean silently converts this to k.val + 1 ≤ m).
  fun k => ∑ (i : Fin (k.val + 1)), v_list (Fin.castLE k.isLt i)

-- ═══════════════════════════════════════════════════════════════════════════
-- Define the coefficients that convert the "w" list to the "v" list.
-- ═══════════════════════════════════════════════════════════════════════════
def diff_coeff {m : ℕ} (a_list : Fin m → 𝔽) : Fin m → 𝔽 :=
  fun k => if h : (k.val + 1 < m) then a_list k - a_list ⟨k.val + 1, h⟩
                                  else a_list k

-- ═══════════════════════════════════════════════════════════════════════════
--
-- ═══════════════════════════════════════════════════════════════════════════
lemma w_list_eq_ite_sum {m : ℕ} (v_list : Fin m → V) (k : Fin m) :
  w_list v_list k = ∑ j, if j ≤ k then v_list j else 0 := by
  unfold w_list
  rw [←Finset.sum_filter]
  apply Finset.sum_bij (fun (i : Fin (k.val + 1)) _ => Fin.castLE k.isLt i)
  · intro i _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change (Fin.castLE k.isLt i).val ≤ k.val
    have := i.isLt
    exact Nat.lt_succ_iff.mp i.isLt
  · intro i₁ _ i₂ _ heq
    apply_fun Fin.val at heq
    exact Fin.ext heq
  · intro b hb
    rw [Finset.mem_filter] at hb
    refine ⟨⟨b.val, Nat.lt_succ_of_le hb.2⟩, Finset.mem_univ _, ?_⟩
    rfl
  · intro i ?_
    rfl

-- ═══════════════════════════════════════════════════════════════════════════
--
-- ═══════════════════════════════════════════════════════════════════════════
lemma telescoping_sum {m : ℕ} (a_list : Fin m → 𝔽) (j : Fin m) :
  ∑ k ∈ Finset.univ.filter (fun k => j ≤ k), diff_coeff a_list k = a_list j := by

  match m, a_list, j with
  | n + 1, a_list, j =>
    induction j using Fin.reverseInduction with
    | last =>
      simp [Finset.ext]
      sorry
    | cast j ih =>
      sorry




-- ═══════════════════════════════════════════════════════════════════════════
--
-- ═══════════════════════════════════════════════════════════════════════════
lemma forward_lincomb {m : ℕ} (a_list : Fin m → 𝔽) (v_list : Fin m → V) :
  ∑ k, a_list k • v_list k = ∑ k, diff_coeff a_list k • w_list v_list k := by

  simp_rw [w_list_eq_ite_sum]
  simp_rw [Finset.smul_sum]
  simp_rw [smul_ite]
  simp_rw [smul_zero]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter]
  simp_rw [← Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _

-- ═══════════════════════════════════════════════════════════════════════════
-- The exercises only asks for one direction but will prove both.
-- ═══════════════════════════════════════════════════════════════════════════
theorem simple_span_eq_sum_span {m : ℕ} (v_list : Fin m → V) :
    spanSubspace (𝔽 := 𝔽) v_list = spanSubspace (𝔽 := 𝔽) (w_list v_list) := by

  ext v
  --simp only [Set.mem_setOf_eq] at *
  unfold spanSubspace
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq]

  constructor
  · -- If it's in the simple span then it's in the difference span.
    intro h_v_is_in_the_span
    obtain ⟨ a_list, h_v_eq_lincomb⟩ := h_v_is_in_the_span

    -- We want to use (a₁ - a₂), (a₂ - a₃), ... (aₘ₋₁ - aₘ), aₘ
    use diff_coeff a_list

    rw[h_v_eq_lincomb]
    simp
    funext j
    simp only [Pi.add_apply]
    simp only [Pi.smul_apply]
    simp only [Pi.sub_apply]
    simp only [smul_eq_mul]
    ring

  · -- If it's in the difference span then it's in the simple span.
    intro h_v_is_in_the_span
    obtain ⟨ a_list, h_v_eq_lincomb⟩ := h_v_is_in_the_span
    use ![a_list 0,
          a_list 1 - a_list 0,
          a_list 2 - a_list 1,
          a_list 3 - a_list 2
         ]

    rw[h_v_eq_lincomb]
    simp[Fin.sum_univ_four]
    funext j
    simp only [Pi.add_apply]
    simp only [Pi.smul_apply]
    simp only [Pi.sub_apply]
    simp only [smul_eq_mul]
    ring
