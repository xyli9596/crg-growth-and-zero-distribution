import CRGLinearKernelHolomorphicExpansion
import CRGPolynomialKernelCoefficients

/-! Actual finite coefficient data from manuscript Corollary 5.2.
The fields give the integral representation and its source hypotheses. -/
set_option autoImplicit false
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace CRGLinearKernel
open CRGExponentialCoefficients CRGLinearKernelEntire

structure CoefficientData (n : ℕ) where
  count : ℕ
  exponential : Fin n → ℂ → ℂ
  isExponential : ∀ k, IsExponentialPolynomial (exponential k)
  lower : Fin count → ℝ
  upper : Fin count → ℝ
  interval_positive : ∀ ell, lower ell < upper ell
  slope : Fin count → ℂ
  slope_nonzero : ∀ ell, slope ell ≠ 0
  weight : Fin n → Fin count → ℂ → ℂ
  weight_holomorphic : ∀ k ell, AnalyticOnNhd ℂ (weight k ell)
    (Complex.ofReal '' Icc (lower ell) (upper ell))

def CoefficientData.coefficient {n : ℕ} (D : CoefficientData n) (k : Fin n) (z : ℂ) : ℂ :=
  D.exponential k z + ∑ ell : Fin D.count,
    linearKernel (fun t => D.weight k ell (t:ℂ))
      (D.lower ell) (D.upper ell) (D.slope ell) z

theorem CoefficientData.differentiable_coefficient {n : ℕ}
    (D : CoefficientData n) (k : Fin n) : Differentiable ℂ (D.coefficient k) := by
  apply Differentiable.add
    (CRGPolynomialKernel.differentiable_exponentialPolynomial (D.isExponential k))
  apply Differentiable.fun_sum
  intro ell _
  apply differentiable_linearKernel (D.interval_positive ell).le
  exact (D.weight_holomorphic k ell).continuousOn.comp
    Complex.continuous_ofReal.continuousOn (mapsTo_image _ _)

theorem CoefficientData.endpoint_expansion {n : ℕ} (D : CoefficientData n)
    (k : Fin n) (ell : Fin D.count) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, ∀ c : ℝ,
      z≠0 → 0<c → c*‖D.slope ell*z‖≤|(D.slope ell*z).re| →
      ‖linearKernel (fun t=>D.weight k ell (t:ℂ)) (D.lower ell) (D.upper ell)
        (D.slope ell) z - CRGLinearKernelHolomorphicExpansion.endpointSum
          (D.weight k ell) (D.lower ell) (D.upper ell) (D.slope ell*z) N‖ ≤
        C/c*(‖Complex.exp ((D.slope ell*z)*(D.upper ell:ℂ))‖+
          ‖Complex.exp ((D.slope ell*z)*(D.lower ell:ℂ))‖)/‖z‖^(N+1) := by
  apply CRGLinearKernelHolomorphicExpansion.linearKernel_expansion_bound
    (D.interval_positive ell).le ?_ (D.slope_nonzero ell) N
  simpa only [uIcc_of_le (D.interval_positive ell).le] using D.weight_holomorphic k ell

#print axioms CoefficientData.differentiable_coefficient
#print axioms CoefficientData.endpoint_expansion
end CRGLinearKernel
