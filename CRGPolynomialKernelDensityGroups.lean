import CRGPolynomialKernelFormalGroups
import CRGPolynomialKernelCoefficients

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial MeasureTheory
open scoped Topology BigOperators
namespace CRGPolynomialKernel
open CRGExponentialCoefficients

def groupedPowerDensity {ι : Type*} (S : Finset ι) (w : ι → ℝ → ℂ)
    (m : ι → ℕ) (Q : ι → Polynomial ℂ) (u : ℝ) : ℂ :=
  ∑ ell ∈ S, powerDensity (w ell) (m ell) u * Complex.exp ((Q ell).coeff 0 * (u:ℂ))

theorem intervalIntegrable_groupedPowerDensity {ι : Type*} (S : Finset ι)
    (w : ι → ℝ → ℂ) (m : ι → ℕ) (Q : ι → Polynomial ℂ)
    (hw : ∀ell∈S,ContinuousOn (w ell) (Icc 0 1)) (hm : ∀ell∈S,0<m ell) :
    IntervalIntegrable (groupedPowerDensity S w m Q) volume 0 1 := by
  have he := IntervalIntegrable.sum S (fun ell hell =>
    (intervalIntegrable_powerDensity (hw ell hell) (hm ell hell)).mul_continuousOn
      (show ContinuousOn (fun u : ℝ=>Complex.exp ((Q ell).coeff 0*(u:ℂ))) (Set.uIcc 0 1) from by fun_prop))
  have hf : groupedPowerDensity S w m Q =
      ∑ell∈S,(fun u : ℝ=>powerDensity (w ell) (m ell) u*Complex.exp ((Q ell).coeff 0*(u:ℂ))) := by
    funext u
    simp only [groupedPowerDensity,Finset.sum_apply]
  rw [hf]
  exact he

theorem analyticOnNhd_groupedPowerDensity {ι : Type*} (S : Finset ι)
    (w : ι → ℝ → ℂ) (m : ι → ℕ) (Q : ι → Polynomial ℂ)
    (hw : ∀ell∈S,AnalyticOnNhd ℝ (w ell) (Icc 0 1)) (hm : ∀ell∈S,0<m ell) :
    AnalyticOnNhd ℝ (groupedPowerDensity S w m Q) (Ioc 0 1) := by
  intro u hu
  apply Finset.analyticAt_fun_sum
  intro ell hell
  exact ((analyticOnNhd_powerDensity ((hw ell hell).mono Ioc_subset_Icc_self) (hm ell hell)) u hu).mul
    ((analyticAt_cexp).restrictScalars.comp (analyticAt_const.mul (Complex.ofRealCLM.analyticAt u)))

/-- This is the manuscript's actual grouping of polynomial kernels differing
by constants, including different integer powers and different weights. -/
theorem polynomialKernel_grouped {ι : Type*} (S : Finset ι)
    (w : ι → ℝ → ℂ) (m : ι → ℕ) (Q : ι → Polynomial ℂ) (q : Polynomial ℂ)
    (hw : ∀ell∈S,ContinuousOn (w ell) (Icc 0 1)) (hm : ∀ell∈S,0<m ell)
    (hq : ∀ell∈S,normalizedExponent (Q ell)=q) (z : ℂ) :
    (∑ell∈S,polynomialKernel (w ell) (Q ell) (m ell) z) =
      laplaceIntegral (groupedPowerDensity S w m Q) (fun u=>(u:ℂ)) (q.eval z) := by
  unfold polynomialKernel
  have he : ∀ell∈S,
      laplaceIntegral (w ell) (fun t=>(t:ℂ)^(m ell)) ((Q ell).eval z) =
      laplaceIntegral (powerDensity (w ell) (m ell)) (fun u=>(u:ℂ))
        (q.eval z+(Q ell).coeff 0) := by
    intro ell hell
    rw [powerKernel_eq_densityIntegral _ (hm ell hell)]
    congr 1
    have hh := congrArg (Polynomial.eval z) (hq ell hell)
    simp only [normalizedExponent,Polynomial.eval_sub,Polynomial.eval_C] at hh
    exact (sub_eq_iff_eq_add).mp hh
  change (∑ell∈S,laplaceIntegral (w ell) (fun t=>(t:ℂ)^(m ell)) ((Q ell).eval z)) = _
  rw [Finset.sum_congr rfl he]
  exact group_constant_shifted_integrals S _ _ _ (fun ell hell=>
    intervalIntegrable_powerDensity (hw ell hell) (hm ell hell))

#print axioms intervalIntegrable_groupedPowerDensity
#print axioms analyticOnNhd_groupedPowerDensity
#print axioms polynomialKernel_grouped
end CRGPolynomialKernel
