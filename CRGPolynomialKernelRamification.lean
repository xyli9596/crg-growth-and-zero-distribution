import CRGPolynomialKernelCoefficients
import CRGPolynomialKernelPuiseux

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial
open scoped Topology BigOperators
namespace CRGPolynomialKernel
open CRGExponentialCoefficients

def CoefficientData.ramification {n : ℕ} (D : CoefficientData n) : ℕ :=
  ∏ell : Fin D.count,D.power ell

theorem CoefficientData.ramification_positive {n : ℕ} (D : CoefficientData n) :
    0<D.ramification := by
  exact Finset.prod_pos (fun ell _=>D.power_positive ell)

theorem CoefficientData.power_dvd_ramification {n : ℕ} (D : CoefficientData n) (ell : Fin D.count) :
    D.power ell ∣ D.ramification :=
  Finset.dvd_prod_of_mem D.power (Finset.mem_univ ell)

theorem normalizedExponent_nonzero {Q : Polynomial ℂ} (hQ : 0<Q.natDegree) :
    normalizedExponent Q ≠ 0 := by
  intro hz
  have he : Q=Polynomial.C (Q.coeff 0) := sub_eq_zero.mp hz
  rw [he,Polynomial.natDegree_C] at hQ
  exact Nat.lt_irrefl 0 hQ

theorem normalizedExponent_nonconstant {Q : Polynomial ℂ} (hQ : 0<Q.natDegree) :
    0<(normalizedExponent Q).natDegree := by
  simpa only [sub_zero] using distinct_normalized_nonconstant
    (normalizedExponent_zero Q) (by simp : (0:Polynomial ℂ).coeff 0=0)
    (normalizedExponent_nonzero hQ)

#print axioms CoefficientData.ramification_positive
#print axioms CoefficientData.power_dvd_ramification
#print axioms normalizedExponent_nonconstant
end CRGPolynomialKernel
