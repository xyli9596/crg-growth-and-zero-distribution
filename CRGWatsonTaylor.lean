import CRGPolynomialKernelCancellation
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace CRGWatson

/-- Taylor polynomial in the real integration variable, with complex coefficients. -/
def taylorPolynomial (w : ℝ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N, (t ^ j / (j.factorial : ℝ)) • iteratedDeriv j w 0

theorem continuous_taylorPolynomial (w : ℝ → ℂ) (N : ℕ) :
    Continuous (taylorPolynomial w N) := by
  unfold taylorPolynomial
  fun_prop

/-- Analytic weights have an all-orders Taylor remainder bound on the whole
integration interval. The bound is deduced rather than assumed. -/
theorem analytic_taylor_remainder_bound {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (hwa : AnalyticAt ℝ w 0) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 1,
      ‖w t - taylorPolynomial w N t‖ ≤ C * t ^ N := by
  obtain ⟨F, hFa, hF⟩ := hwa.exists_eq_sum_add_pow_mul N
  have hrep : ∀ t : ℝ, w t - taylorPolynomial w N t = t ^ N • F t := by
    intro t
    simpa only [taylorPolynomial, add_sub_cancel_left] using
      congrArg (fun z : ℂ => z - taylorPolynomial w N t) (hF t)
  have hFcont : ContinuousOn F (Icc 0 1) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      exact hFa.continuousAt.continuousWithinAt
    · have hne : ∀ᶠ x in 𝓝 t, x ≠ (0 : ℝ) :=
        (isOpen_compl_singleton.mem_nhds ht0)
      have heq : F =ᶠ[𝓝 t] (fun x => (x ^ N)⁻¹ • (w x - taylorPolynomial w N x)) := by
        filter_upwards [hne] with x hx
        rw [hrep x, inv_smul_smul₀ (pow_ne_zero _ hx)]
      have hratio : ContinuousWithinAt
          (fun x => (x ^ N)⁻¹ • (w x - taylorPolynomial w N x)) (Icc 0 1) t := by
        exact (((continuousAt_id.pow N).inv₀ (pow_ne_zero _ ht0)).continuousWithinAt).smul
          ((hw t ht).sub ((continuous_taylorPolynomial w N).continuousAt.continuousWithinAt))
      exact hratio.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds)
        (heq.self_of_nhds)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hFcont
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  rw [hrep t, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg ht.1]
  exact (mul_le_mul_of_nonneg_left ((hC t ht).trans (le_max_left _ _))
    (pow_nonneg ht.1 N)).trans_eq (mul_comm _ _)

/-- The nonnegative majorant integral has the Gamma scaling required by
Watson's lemma. -/
theorem gaussian_moment_bound {A : ℝ} (hA : 0 < A) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..1, t ^ N * Real.exp (-A * t ^ m)) ≤
      A ^ (-((N : ℝ) + 1) / (m : ℝ)) * (1 / (m : ℝ)) *
        Real.Gamma (((N : ℝ) + 1) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hN : (-1 : ℝ) < N := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow hN hmR hA
  calc
    _ = ∫ t : ℝ in Ioc 0 1, t ^ (N : ℝ) * Real.exp (-A * t ^ (m : ℝ)) := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      simp only [Real.rpow_natCast]
    _ ≤ ∫ t : ℝ in Ioi 0, t ^ (N : ℝ) * Real.exp (-A * t ^ (m : ℝ)) := by
      apply setIntegral_mono_set hi
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _)
      · exact Filter.Eventually.of_forall (fun t ht => ht.1)
    _ = _ := integral_rpow_mul_exp_neg_mul_rpow hmR hN hA

#print axioms analytic_taylor_remainder_bound
#print axioms gaussian_moment_bound
end CRGWatson
