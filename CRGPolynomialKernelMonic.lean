import CRGPolynomialKernelDensityGroups
import CRGPuiseuxMonic

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial
open scoped Topology BigOperators
namespace CRGPolynomialKernel
open CRGPuiseuxMonic

/-- The top scalar coefficient has zero integral weight and is kept as 1. -/
def CoefficientData.fullWeight {n : ℕ} (D : CoefficientData n)
    (j : Fin (n+1)) (ell : Fin D.count) : ℝ → ℂ :=
  Fin.lastCases (fun _=>0) (fun k t=>D.weight k ell (t:ℂ)) j

theorem CoefficientData.fullWeight_analytic {n : ℕ} (D : CoefficientData n)
    (j : Fin (n+1)) (ell : Fin D.count) :
    AnalyticOnNhd ℝ (D.fullWeight j ell) (Icc 0 1) := by
  induction j using Fin.lastCases with
  | last =>
    simp only [CoefficientData.fullWeight,Fin.lastCases_last]
    exact fun _ _=>analyticAt_const
  | cast j =>
    simpa only [CoefficientData.fullWeight,Fin.lastCases_castSucc] using
      analytic_weight_restriction (D.weight_holomorphic j ell)

theorem CoefficientData.full_coefficient_representation {n : ℕ} (D : CoefficientData n)
    (j : Fin (n+1)) (z : ℂ) :
    fullCoefficient D.coefficient j z = fullCoefficient D.exponential j z +
      ∑ell : Fin D.count,polynomialKernel (D.fullWeight j ell) (D.phase ell) (D.power ell) z := by
  induction j using Fin.lastCases with
  | last => simp [fullCoefficient, CoefficientData.fullWeight, polynomialKernel]
  | cast j => simp only [fullCoefficient_castSucc,CoefficientData.coefficient,
      CoefficientData.fullWeight,Fin.lastCases_castSucc]

@[simp] theorem CoefficientData.fullWeight_last {n : ℕ} (D : CoefficientData n) (ell : Fin D.count) :
    D.fullWeight (Fin.last n) ell = 0  := by
  funext t
  simp [CoefficientData.fullWeight]

#print axioms CoefficientData.full_coefficient_representation
end CRGPolynomialKernel
