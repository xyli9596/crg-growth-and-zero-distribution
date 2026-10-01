import CRGRay
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Instances.Matrix

/-!
Additional checked steps in the manuscript's ray reduction.
This module does not prove the rational-system normal-form theorem,
Gundersen's estimate, or the global CRG criterion.
-/
open Filter MeasureTheory Set
open scoped Topology
namespace CRGProgress

/-- A polynomially weighted exponential is integrable on the positive half-line.
Only K > -1 is needed at zero; on a ray tail one may enlarge K to a nonnegative one. -/
theorem polynomial_exp_integrable (K c C : ℝ) (hK : -1 < K) (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => C * (r ^ K * Real.exp (-c * r))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := K) (p := 1) hK (by norm_num) hc
  simpa only [Real.rpow_one, IntegrableOn] using h.const_mul C

/-- The actual perturbation is L1 when its norm has the claimed exponential bound. -/
theorem perturbation_integrable {E : Type*} [NormedAddCommGroup E]
    (R : ℝ → E) (K c C r₀ : ℝ) (hK : -1 < K) (hc : 0 < c) (hr₀ : 0 ≤ r₀)
    (hmeas : AEStronglyMeasurable R (volume.restrict (Ioi r₀)))
    (hbound : ∀ᵐ r ∂volume.restrict (Ioi r₀),
      ‖R r‖ ≤ C * (r ^ K * Real.exp (-c * r))) :
    IntegrableOn R (Ioi r₀) := by
  exact ((polynomial_exp_integrable K c C hK hc).mono_set
    (Ioi_subset_Ioi hr₀)).mono' hmeas hbound

/-- Choosing a large starting radius makes the L1 tail smaller than any tolerance. -/
theorem exists_small_tail {E : Type*} [NormedAddCommGroup E]
    (R : ℝ → E) (r₀ ε : ℝ) (_hR : IntegrableOn R (Ioi r₀)) (hε : 0 < ε) :
    ∃ a ≥ r₀, (∫ r in Ioi a, ‖R r‖) < ε := by
  have hlim : Tendsto (fun a : ℝ => ∫ r in Ioi a, ‖R r‖) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  have hsmall := hlim.eventually (gt_mem_nhds hε)
  obtain ⟨a, ha, hsmall⟩ := (hsmall.and (eventually_ge_atTop r₀)).exists
  exact ⟨a, hsmall, ha⟩

/-- Exact gauge cancellation for possibly noncommuting operators. The order of
T, its inverse S, A, and E is preserved throughout. -/
theorem gauge_cancellation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T S A D T' P : E →L[ℂ] E) (z z' : E)
    (hST : S.comp T = ContinuousLinearMap.id ℂ E)
    (hgauge : S.comp (A.comp T) - S.comp T' = D)
    (hsystem : T' z + T z' = A (T z) + P (T z)) :
    z' = D z + S (P (T z)) := by
  have hSTz : S (T z') = z' := by
    simpa using congrArg (fun L : E →L[ℂ] E => L z') hST
  have hDz : S (A (T z)) - S (T' z) = D z := by
    simpa using congrArg (fun L : E →L[ℂ] E => L z) hgauge
  have hx := congrArg S hsystem
  simp only [map_add] at hx
  rw [hSTz] at hx
  calc
    z' = (S (A (T z)) + S (P (T z))) - S (T' z) := by
      simpa only [add_sub_cancel_left] using congrArg (fun v => v - S (T' z)) hx
    _ = (S (A (T z)) - S (T' z)) + S (P (T z)) := by abel
    _ = _ := by rw [hDz]

/-- Operator norms supply the polynomial loss in the conjugated perturbation. -/
theorem conjugated_perturbation_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T S P : E →L[ℂ] E) :
    ‖S.comp (P.comp T)‖ ≤ ‖S‖ * ‖P‖ * ‖T‖ := by
  calc
    ‖S.comp (P.comp T)‖ ≤ ‖S‖ * ‖P.comp T‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖S‖ * (‖P‖ * ‖T‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

/-- A genuine derivative product rule supplies the equation used by the algebraic
cancellation theorem. No derivative identity is hidden in a normal-form interface. -/
theorem derivative_of_gauged_vector {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ → E →L[ℝ] E) (z : ℝ → E) (T' : E →L[ℝ] E) (z' : E) (r : ℝ)
    (hT : HasDerivAt T T' r) (hz : HasDerivAt z z' r) :
    HasDerivAt (fun s => T s (z s)) (T' (z r) + T r z') r := by
  exact hT.clm_apply hz

/-- The normalized matrix is eventually nonsingular once its entries converge to I.
This is the actual last invertibility step of the mixed-integral construction. -/
theorem eventually_det_ne_zero {α : Type*} {l : Filter α} (m : ℕ)
    (U : α → Matrix (Fin m) (Fin m) ℂ) (hU : Tendsto U l (𝓝 1)) :
    ∀ᶠ r in l, (U r).det ≠ 0 := by
  have hd : Continuous (fun M : Matrix (Fin m) (Fin m) ℂ => M.det) :=
    continuous_id.matrix_det
  have hlim : Tendsto (fun r => (U r).det) l (𝓝 (1 : ℂ)) := by
    simpa only [Matrix.det_one, Function.comp_def] using (hd.tendsto 1).comp hU
  exact hlim.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))

#print axioms eventually_det_ne_zero
#print axioms polynomial_exp_integrable
#print axioms perturbation_integrable
#print axioms exists_small_tail
#print axioms gauge_cancellation
#print axioms conjugated_perturbation_bound
#print axioms derivative_of_gauged_vector
end CRGProgress
