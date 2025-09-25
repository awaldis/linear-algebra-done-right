---------------------------------------------------------
-- Exercise 3A-3 - A linear map is a matrix of scalars.
---------------------------------------------------------
import Mathlib.LinearAlgebra.StdBasis

variable {𝔽 : Type*} [Field 𝔽]
variable {m n : ℕ}

----------------------------------------------------------------------
-- helper theorem
----------------------------------------------------------------------
theorem expand_std_basis (x : Fin n → 𝔽) :
  -- Any vector x can be rewritten as the sum of the standard basis vectors each
  -- multiplied by its respective vector element.
   x = ∑ k : Fin n, x k • (Pi.basisFun 𝔽 (Fin n)) k := by
  simpa [eq_comm] using (Pi.basisFun 𝔽 (Fin n)).sum_repr x

----------------------------------------------------------------------
-- main theorem
----------------------------------------------------------------------
example (T : (Fin n → 𝔽) →ₗ[𝔽] (Fin m → 𝔽)) :
  ∃ (A : Fin m → Fin n → 𝔽),  -- there exists a matrix A
    ∀ (x : Fin n → 𝔽) (j : Fin m), -- for all vectors x and indices j
      T x j = ∑ (k : Fin n), (A j k) * (x k) := by

  let A : Fin m → Fin n → 𝔽 := fun j k => T (Pi.basisFun 𝔽 (Fin n) k) j
  refine ⟨A, ?_⟩
  -- New goal: ∀ (x : Fin n → 𝔽) (j : Fin m), T x j = ∑ k, A j k * x k
  intro x j
  -- New goal: T x j = ∑ k, A j k * x k

  calc T x j
    -- Replace x with the sum of basis vectors smuled with their respective coefficients.
    = T (∑ k : Fin n, x k • (Pi.basisFun 𝔽 (Fin n)) k) j     := by rw [← @expand_std_basis]

    -- By additivity of linear maps we can move T inside the summation.
    _ = (∑ k : Fin n, T (x k • (Pi.basisFun 𝔽 (Fin n) k))) j := by rw [@map_sum]

    -- By homogeneity of linear maps we can move "x k" smul outside of T.
    _ = (∑ k : Fin n, x k • T (Pi.basisFun 𝔽 (Fin n) k)) j   := by simp [Pi.smul_apply]

    -- Now move the j inside the summation to allow regular multiplication.
    _ =  ∑ k : Fin n, x k * T (Pi.basisFun 𝔽 (Fin n) k) j    := by simp [smul_eq_mul]

    -- Now commutate around the "*".
    _ =  ∑ k : Fin n, T (Pi.basisFun 𝔽 (Fin n) k) j * x k    := by simp [mul_comm]

    -- Replace "(Pi.basisFun 𝔽 (Fin n) k) j" with "A j k" as we defined it above.
    _ =  ∑ k : Fin n, (A j k) * (x k)                            := by rw []
    -- QED
