import LinearAlgebraDoneRight.LADR4e_2_6_span_is_the_smallest_containing_subspace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

variable {𝔽 : Type*} [Field 𝔽]
variable {V : Type*} [AddCommGroup V] [Module 𝔽 V]

/-!
# Theorem 2.19 - linear dependence lemma
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net), fourth
edition, Undergraduate Texts in Mathematics, Springer, 2024
-/
-- ═══════════════════════════════════════════════════════════════════════════
-- Define linear dependence and independence
-- ═══════════════════════════════════════════════════════════════════════════

def linearly_independent {m : ℕ} (vector_list : Fin m → V ) : Prop :=
   ∀ (a : Fin m → 𝔽), (∑ k, a k • vector_list k = 0 ) → a = 0

def LinearlyDependent {m : ℕ} (vector_list : Fin m → V ) : Prop :=
   ∃ (a : Fin m → 𝔽), (a ≠ 0) ∧ (∑ k, a k • vector_list k = 0 )

-- ═══════════════════════════════════════════════════════════════════════════
-- Verify that the definitions behave as expected.
-- ═══════════════════════════════════════════════════════════════════════════
theorem linearly_dependent_iff_not_linearly_independent
                               {m : ℕ} (vector_list : Fin m → V ) :
    LinearlyDependent (𝔽 := 𝔽 ) vector_list ↔
    ¬ linearly_independent (𝔽 := 𝔽 ) vector_list := by
    constructor
    · unfold LinearlyDependent
      unfold linearly_independent
      intro h_lin_dep
      obtain ⟨ a_list, h_lin_dep_conjunction ⟩ := h_lin_dep
      obtain⟨ h_alist_nonzero, h_lin_comb_eq_zero ⟩ := h_lin_dep_conjunction
      intro h_lin_indep
      specialize h_lin_indep a_list
      specialize h_lin_indep h_lin_comb_eq_zero
      exact absurd h_lin_indep h_alist_nonzero

    · unfold LinearlyDependent
      unfold linearly_independent
      intro h_lin_indep
      push_neg at h_lin_indep
      obtain⟨ a_list, h_lin_indep_conjunction ⟩ := h_lin_indep
      obtain⟨ h_lin_comb_eq_zer, h_alist_nonzero ⟩ := h_lin_indep_conjunction
      use a_list


-- ═══════════════════════════════════════════════════════════════════════════
-- Define the first k values in a list.
-- ═══════════════════════════════════════════════════════════════════════════
def takeFirst {V : Type*} {m : ℕ} (f : Fin m → V) (k : Fin m) :
    Fin k.val → V := fun i => f ⟨ i.val, lt_trans i.isLt k.isLt ⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- Remove the kth value from a list.
-- ═══════════════════════════════════════════════════════════════════════════
def removeAt {V : Type*} {m : ℕ} (f : Fin (m+1) → V) (k : Fin (m+1)) :
    Fin m → V := fun i => f (Fin.succAbove k i)

-- ═══════════════════════════════════════════════════════════════════════════
-- helper lemma
-- ═══════════════════════════════════════════════════════════════════════════
lemma lindep_removed_term_eq_lincomb_rest {𝔽 : Type*} [Field 𝔽] {V : Type*} [AddCommGroup V]
    [Module 𝔽 V] {m : ℕ} (v : Fin (m+1) → V) (a : Fin (m+1) → 𝔽) (k : Fin (m+1))
    (hk : a k ≠ 0) (h_lincomb_eq_0 : ∑ i, a i • v i = 0) :
    v k = ∑ (i : Fin m), (- (a k)⁻¹ * a (k.succAbove i)) • v (k.succAbove i) := by

  -- Split out the k term from the summation.
  have h_split_lincomb_eq_0 :
     a k • v k + ∑ i, a (k.succAbove i) • v (k.succAbove i) = 0 := by
       rw [← Fin.sum_univ_succAbove (f := fun j => a j • v j) (x := k)]
       exact h_lincomb_eq_0

  -- Put the k term and the summation on opposites sides of the equality.
  have h_split_k_eq_neg_lincomb :
             a k • v k = -∑ (i : Fin m), a (k.succAbove i) • v (k.succAbove i)
                        := by rw [eq_neg_iff_add_eq_zero, h_split_lincomb_eq_0]

  -- Isolate the kth vector.
  have h_kth_vector_calc :
          v k = (a k)⁻¹ • -∑ (i : Fin m), a (k.succAbove i) • v (k.succAbove i)
                       := by rw [← h_split_k_eq_neg_lincomb, inv_smul_smul₀ hk]

  -- Now the rest can be done in a calc.
  calc v k
      = (a k)⁻¹ • -∑ (i : Fin m), a (k.succAbove i) • v (k.succAbove i)
                                                         := h_kth_vector_calc
    _ = -(a k)⁻¹ • ∑ (i : Fin m), a (k.succAbove i) • v (k.succAbove i)
                                                         := by norm_num
    _ = ∑ (i : Fin m), -(a k)⁻¹ • a (k.succAbove i) • v (k.succAbove i)
                                                    := by rw [Finset.smul_sum]
    _ = ∑ (i : Fin m), -(a⁻¹) k • a (k.succAbove i) • v (k.succAbove i)
                                                            := by trivial
    _ = ∑ (i : Fin m), (-(a⁻¹) k * a (k.succAbove i)) • v (k.succAbove i)
                                        := by congr 1; ext i; rw [←mul_smul]

-- ═══════════════════════════════════════════════════════════════════════════
-- Show that {x : Fin n | x < k} and Fin k are equivalent.
-- ═══════════════════════════════════════════════════════════════════════════
def fin_filter_equiv_fin {n : ℕ} (k : Fin (n + 1)) :
  {x : Fin n // x.castSucc < k} ≃ Fin k.val where
    toFun     := fun x => ⟨x.val.val, x.property⟩
    invFun    := fun y => ⟨⟨y.val, by omega ⟩, y.isLt  ⟩
    left_inv  := by intro x; rfl
    right_inv := by intro x; rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- linear dependence lemma (first part)
-- ═══════════════════════════════════════════════════════════════════════════
theorem linear_dependence_lemma {m : ℕ} (vector_list : Fin m → V)
  (h_dep : LinearlyDependent (𝔽 := 𝔽) vector_list) :
  ∃ (k : Fin m),
  vector_list k ∈ spanSubspace (𝔽 := 𝔽) (takeFirst vector_list k) := by

  -- Unfold assumptions into the context...
  unfold LinearlyDependent at *

  obtain ⟨a_list, h_a_neq_0, h_lincomb_eq_0⟩ := h_dep

  rw[Function.ne_iff] at h_a_neq_0
  obtain⟨i, h_alist_i_neq_0⟩ := h_a_neq_0

  have h_m_ne_0 : m ≠ 0 := by rintro rfl; exact i.elim0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h_m_ne_0

  classical
  have h_nonempty :
   (Finset.filter (fun j => a_list j ≠ 0) Finset.univ).Nonempty := by
   use i
   rw [Finset.mem_filter]
   exact ⟨Finset.mem_univ i, h_alist_i_neq_0⟩

  let k := Finset.max' (Finset.filter (fun j => a_list j ≠ 0) Finset.univ)
    h_nonempty

  -- Now let's work on the goal.
  unfold spanSubspace
  use k

  simp only [Submodule.mem_mk]
  simp only [AddSubmonoid.mem_mk]
  simp only [AddSubsemigroup.mem_mk]
  simp only [Set.mem_setOf_eq]

  use (-(a_list k)⁻¹) • takeFirst a_list k

  have h_ak_ne_0 : a_list k ≠ 0 := by
    have h_k_mem := Finset.max'_mem
      (Finset.filter (fun j => a_list j ≠ 0) Finset.univ) h_nonempty
    rw [Finset.mem_filter] at h_k_mem
    exact h_k_mem.2

  -- Use a helper lemma to write the LHS as a linear combination of all the other
  -- vectors (other than k itself).
  rw [lindep_removed_term_eq_lincomb_rest vector_list a_list k h_ak_ne_0  h_lincomb_eq_0]

  -- Split the LHS sum into two sums: one below k and one above.
  rw [←Finset.sum_filter_add_sum_filter_not _ (fun i => i.castSucc < k)]

  -- Show that all the coefficients above k are zero.
  have h_a_is_zero_above_k : ∀ (j : Fin (n+1)), k < j → a_list j = 0 := by
    intro j h_k_lt_j
    --Suppose there is a j > k with nonzero coefficient.
    by_contra h_a_list_j_ne_0
    -- Then j would be in the set of nonzero coefficients.
    have h_j_in_nonzero_set : j ∈ (Finset.univ.filter (fun j => a_list j ≠ 0)) :=
                       Finset.mem_filter.mpr ⟨Finset.mem_univ j, h_a_list_j_ne_0⟩
    -- Then j could be equal to the max index of the coefficients which
    -- contradicts our assumption that k is the max value and j < k.
    exact absurd (Finset.le_max' _ j h_j_in_nonzero_set) (not_le.mpr h_k_lt_j)

  -- Show that the linear combination above k is zero.
  have h_lincomb_above_k_is_zero :
    ∑ x with ¬x.castSucc < k,
      (-(a_list k)⁻¹ * a_list (k.succAbove x))
                                     • vector_list (k.succAbove x) = 0 := by

    apply Finset.sum_eq_zero
    intro i h_i_gt_k
    rw [Finset.mem_filter] at h_i_gt_k
    rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.mp h_i_gt_k.2)]

    have h_k_lt_isucc : k < i.succ :=
      lt_of_le_of_lt (not_lt.mp h_i_gt_k.2) (i.castSucc_lt_succ)

    rw [h_a_is_zero_above_k _ h_k_lt_isucc]
    simp

  -- Make the sum above k disappear from the goal since it's zero.
  rw [h_lincomb_above_k_is_zero, add_zero]

  -- Show set and subtype equivalence.
  have h_subtype : ∀ (x : Fin n),
    x ∈ Finset.filter (fun x => x.castSucc < k)  Finset.univ ↔
                                                      x.castSucc < k := by simp

  -- Replace the set in the goal with it's equivalent subtype.
  rw [Finset.sum_subtype _ h_subtype]

  -- Replace the Fin ↑k index type with { x // x.castSucc < k } to make the
  -- indices have the same type.
  rw [← Equiv.sum_comp (fin_filter_equiv_fin k)]

  simp only [fin_filter_equiv_fin, Equiv.coe_fn_mk, takeFirst]

  -- New goal: the functions must be equivalent at each index.
  apply Finset.sum_congr rfl

  intro x hx
  rw[Fin.succAbove_of_castSucc_lt _ _ x.property]
  congr 1

-- ═══════════════════════════════════════════════════════════════════════════
-- linear dependence lemma (second part) - TBD
-- ═══════════════════════════════════════════════════════════════════════════
lemma linear_dependence_lemma_part2
  {n :ℕ} (vector_list : Fin (n+1) → V) (k : Fin (n+1))
  (h_vk_in_span : vector_list k ∈ spanSubspace (𝔽 := 𝔽) (takeFirst vector_list k)) :
  spanSubspace (𝔽 := 𝔽) vector_list =
  spanSubspace (𝔽 := 𝔽) (removeAt vector_list k) := by

  apply le_antisymm
  · -- Proving this direction is hard.
    intro u h_u_in_full_span
    obtain ⟨a_list,    h_a_list_full⟩      := h_u_in_full_span
    obtain ⟨a_list_tf, h_a_list_takeFirst⟩ := h_vk_in_span
    -- The rest is TBD
    sorry
  · -- Proving this direction is easy.
    apply spanSubspace_is_smallest
    intro i
    exact each_vector_in_span vector_list (k.succAbove i)
