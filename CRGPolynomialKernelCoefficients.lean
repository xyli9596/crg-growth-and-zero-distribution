import CRGPolynomialKernelEntire
import CRGExponentialCoefficients

set_option autoImplicit false
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace CRGPolynomialKernel
open CRGExponentialCoefficients

/-- The paper's holomorphic-neighbourhood assumption on a weight. -/
def HolomorphicWeight (w : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ w (Complex.ofReal '' Icc (0 : ℝ) 1)

theorem continuous_weight_restriction {w : ℂ → ℂ} (hw : HolomorphicWeight w) :
    ContinuousOn (fun t : ℝ => w (t : ℂ)) (Icc 0 1) := by
  exact hw.continuousOn.comp Complex.continuous_ofReal.continuousOn (mapsTo_image _ _)

theorem analytic_weight_restriction {w : ℂ → ℂ} (hw : HolomorphicWeight w) :
    AnalyticOnNhd ℝ (fun t : ℝ => w (t : ℂ)) (Icc 0 1) := by
  intro t ht
  exact ((hw _ (mem_image_of_mem Complex.ofReal ht)).restrictScalars).comp
    (Complex.ofRealCLM.analyticAt t)

theorem differentiable_exponentialPolynomial {E : ℂ → ℂ}
    (hE : IsExponentialPolynomial E) : Differentiable ℂ E := by
  obtain ⟨N, P, Q, hE⟩ := hE
  have heq : E = fun z => ∑ i : Fin N, (P i).eval z * Complex.exp ((Q i).eval z) := funext hE
  rw [heq]
  apply Differentiable.fun_sum
  intro i _
  exact (P i).differentiable.mul ((Q i).differentiable.cexp)

/-- Actual coefficient functions in equation (5.3), with all source hypotheses
retained. Analyticity and asymptotics are not fields in this structure. -/
structure CoefficientData (n : ℕ) where
  count : ℕ
  exponential : Fin n → ℂ → ℂ
  isExponential : ∀ k, IsExponentialPolynomial (exponential k)
  phase : Fin count → Polynomial ℂ
  phase_nonconstant : ∀ ell, 0 < (phase ell).natDegree
  power : Fin count → ℕ
  power_positive : ∀ ell, 0 < power ell
  weight : Fin n → Fin count → ℂ → ℂ
  weight_holomorphic : ∀ k ell, HolomorphicWeight (weight k ell)

def CoefficientData.coefficient {n : ℕ} (D : CoefficientData n) (k : Fin n) (z : ℂ) : ℂ :=
  D.exponential k z + ∑ ell : Fin D.count,
    polynomialKernel (fun t => D.weight k ell (t : ℂ)) (D.phase ell) (D.power ell) z

/-- Every coefficient in the paper's polynomial-kernel class is entire. -/
theorem CoefficientData.differentiable_coefficient {n : ℕ} (D : CoefficientData n) (k : Fin n) :
    Differentiable ℂ (D.coefficient k) := by
  apply Differentiable.add (differentiable_exponentialPolynomial (D.isExponential k))
  apply Differentiable.fun_sum
  intro ell _
  exact differentiable_polynomialKernel
    (continuous_weight_restriction (D.weight_holomorphic k ell)) (D.phase ell) (D.power ell)

#print axioms analytic_weight_restriction
#print axioms CoefficientData.differentiable_coefficient
end CRGPolynomialKernel
