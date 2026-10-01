import CRGPolynomialKernelEntire
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CRGPolynomialKernel

/-- Vanishing of all endpoint derivatives is actual vanishing of an analytic
weight on the connected interval; it is not an assumed cancellation rule. -/
theorem endpoint_derivatives_zero_implies_zero {v : ℝ → ℂ}
    (hv : AnalyticOnNhd ℝ v (Ioc 0 1))
    (hzero : ∀ j : ℕ, iteratedDeriv j v 1 = 0) :
    EqOn v 0 (Ioc 0 1) := by
  have hv1 : AnalyticAt ℝ v 1 := hv 1 ⟨zero_lt_one, le_rfl⟩
  have ho : ∀ n : ℕ, (n : ℕ∞) ≤ analyticOrderAt v 1 := fun n =>
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hv1).mpr (fun j _ => hzero j)
  have ht : analyticOrderAt v 1 = ⊤ := (ENat.eq_of_forall_natCast_le_iff (fun n => by simp [ho n]))
  exact hv.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioc
    ⟨zero_lt_one, le_rfl⟩ (analyticOrderAt_eq_top.mp ht)

/-- A nonzero analytic endpoint density has a nonzero finite endpoint jet. -/
theorem exists_nonzero_endpoint_derivative {v : ℝ → ℂ}
    (hv : AnalyticOnNhd ℝ v (Ioc 0 1))
    (hnonzero : ∃ t ∈ Ioc 0 1, v t ≠ 0) :
    ∃ j : ℕ, iteratedDeriv j v 1 ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨t, ht, hne⟩ := hnonzero
  exact hne (endpoint_derivatives_zero_implies_zero hv h ht)

/-- An identically zero combined density contributes zero to the actual integral. -/
theorem integral_zero_of_zero_density {v : ℝ → ℂ} (lam : ℂ)
    (hv : EqOn v 0 (Ioc 0 1)) :
    laplaceIntegral v (fun t => (t : ℂ)) lam = 0 := by
  rw [laplaceIntegral]
  have hzero : (∫ t : ℝ in (0 : ℝ)..1, v t * Complex.exp (lam * (t : ℂ))) =
      ∫ t : ℝ in (0 : ℝ)..1, (0 : ℂ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t
    intro ht
    rw [uIoc_of_le zero_le_one] at ht
    simp [hv ht]
  rw [hzero]
  simp

#print axioms endpoint_derivatives_zero_implies_zero
#print axioms exists_nonzero_endpoint_derivative
#print axioms integral_zero_of_zero_density
end CRGPolynomialKernel
