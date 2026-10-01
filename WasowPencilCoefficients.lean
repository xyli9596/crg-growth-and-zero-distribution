import WasowReductionDescent

/-! The coefficients surviving the elimination of a nilpotent shift block.
The polynomial records its actual last-row entries, so its nonvanishing and
degree bound are conclusions, not extra assumptions on the reduced pencil. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
namespace WasowPencilCoefficients

def rowPolynomial {h : ℕ} (v : Fin (h+1) → ℂ) : Polynomial ℂ :=
  ∑ i, Polynomial.monomial i.val (v i)

theorem rowPolynomial_coeff {h : ℕ} (v : Fin (h+1) → ℂ) (i : Fin (h+1)) :
    (rowPolynomial v).coeff i.val = v i := by
  classical
  simp only [rowPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg (fun he => hji (Fin.ext he))]
  · simp

theorem rowPolynomial_eq_zero_iff {h : ℕ} (v : Fin (h+1) → ℂ) :
    rowPolynomial v = 0 ↔ ∀ i, v i = 0 := by
  constructor
  · intro hv i
    have he := congrArg (fun p : Polynomial ℂ => p.coeff i.val) hv
    simpa only [rowPolynomial_coeff, Polynomial.coeff_zero] using he
  · intro hv
    simp [rowPolynomial, hv]

theorem rowPolynomial_ne_zero_iff {h : ℕ} (v : Fin (h+1) → ℂ) :
    rowPolynomial v ≠ 0 ↔ ∃ i, v i ≠ 0 := by
  simp only [ne_eq, rowPolynomial_eq_zero_iff, not_forall]

theorem natDegree_rowPolynomial_lt {h : ℕ} (v : Fin (h+1) → ℂ) :
    (rowPolynomial v).natDegree < h+1 := by
  apply Nat.lt_succ_of_le
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le (v i)).trans (by omega)

theorem rowPolynomial_eq_sum_C_mul_X_pow {h : ℕ} (v : Fin (h+1) → ℂ) :
    rowPolynomial v = ∑ i, Polynomial.C (v i) * X^i.val := by
  simp only [rowPolynomial, Polynomial.C_mul_X_pow_eq_monomial]

/-- Thus every nonzero rectangular last row gives a nonzero reduced entry
of degree strictly below its column block size. -/
theorem neg_rowPolynomial_nonzero_degree {h : ℕ} (v : Fin (h+1) → ℂ)
    (hv : ∃ i, v i ≠ 0) :
    -rowPolynomial v ≠ 0 ∧ (-rowPolynomial v).natDegree < h+1 := by
  exact ⟨neg_ne_zero.mpr ((rowPolynomial_ne_zero_iff v).mpr hv),
    by simpa only [Polynomial.natDegree_neg] using natDegree_rowPolynomial_lt v⟩

#print axioms rowPolynomial_coeff
#print axioms rowPolynomial_eq_zero_iff
#print axioms rowPolynomial_ne_zero_iff
#print axioms natDegree_rowPolynomial_lt
#print axioms rowPolynomial_eq_sum_C_mul_X_pow
#print axioms neg_rowPolynomial_nonzero_degree
end WasowPencilCoefficients
