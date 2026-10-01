import CRGProgress
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Scalar differentiation of the literal forward and backward integrals.
These are mathematical lemmas with explicit continuity and integrability
hypotheses, not assumed ODE solutions. Their connection to the subtype-valued
fixed points in Halfline.lean is proved in WasowVolterra.lean. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace VolterraCalculus

/-- The derivative of an actual improper tail integral is minus its integrand. -/
theorem tail_hasDerivAt (h : ℝ → ℂ) (a r : ℝ) (hcont : Continuous h)
    (hL1 : IntegrableOn h (Ici a)) (har : a < r) :
    HasDerivAt (fun t => ∫ s in Ici t, h s) (-h r) r := by
  have hp := intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable a r) hcont.stronglyMeasurable.stronglyMeasurableAtFilter
    hcont.continuousAt
  have hd := hp.const_sub (∫ s in Ici a, h s)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds har] with t ht
  have hid := intervalIntegral.integral_Ici_sub_Ici' hL1 (hL1.mono_set (Ici_subset_Ici.mpr ht.le))
  exact (sub_eq_iff_eq_add.mp hid).symm ▸ by abel

/-- Forward variation of constants has the required scalar differential equation. -/
theorem forward_hasDerivAt (Δ h : ℝ → ℂ) (a r : ℝ) (d : ℂ)
    (hΔ : HasDerivAt Δ d r)
    (hc : Continuous (fun s => Complex.exp (-Δ s) * h s)) :
    HasDerivAt
      (fun t => Complex.exp (Δ t) * ∫ s in a..t, Complex.exp (-Δ s) * h s)
      (d * (Complex.exp (Δ r) * ∫ s in a..r, Complex.exp (-Δ s) * h s) + h r) r := by
  have hp := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable a r) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert hΔ.cexp.mul hp using 1 <;> first
  | rfl
  | (simp only [Complex.exp_neg, ← mul_assoc, mul_inv_cancel₀ (Complex.exp_ne_zero _), one_mul]; ring)

/-- Backward variation of constants has the same scalar differential equation.
The L1 hypothesis is on the weighted integrand of the actual improper integral. -/
theorem backward_hasDerivAt (Δ h : ℝ → ℂ) (a r : ℝ) (d : ℂ)
    (hΔ : HasDerivAt Δ d r) (har : a < r)
    (hc : Continuous (fun s => Complex.exp (-Δ s) * h s))
    (hL1 : IntegrableOn (fun s => Complex.exp (-Δ s) * h s) (Ici a)) :
    HasDerivAt
      (fun t => -Complex.exp (Δ t) * ∫ s in Ici t, Complex.exp (-Δ s) * h s)
      (d * (-Complex.exp (Δ r) * ∫ s in Ici r, Complex.exp (-Δ s) * h s) + h r) r := by
  have hp := tail_hasDerivAt (fun s => Complex.exp (-Δ s) * h s) a r hc hL1 har
  convert hΔ.cexp.neg.mul hp using 1 <;> first
  | rfl
  | (simp only [Pi.neg_apply, neg_mul, mul_neg, neg_neg, Complex.exp_neg, ← mul_assoc,
      mul_inv_cancel₀ (Complex.exp_ne_zero _), one_mul]; ring)

#print axioms tail_hasDerivAt
#print axioms forward_hasDerivAt
#print axioms backward_hasDerivAt
end VolterraCalculus
