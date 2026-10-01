import CRGLinearKernelIntegration
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! All-order endpoint expansion for analytic weights. The bound is uniform
over complex parameters satisfying a fixed angular separation from the
imaginary axis. This is the quantitative expansion in Corollary 5.2. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace CRGLinearKernelExpansion
open CRGLinearKernelIntegration

def endpointSum (w : ℝ → ℂ) (a b : ℝ) (ζ : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N,
    (-1 : ℂ)^j / ζ^(j+1) * endpoint (iteratedDeriv j w) a b ζ

theorem analytic_jet {w : ℝ → ℂ} {a b : ℝ}
    (hw : AnalyticOnNhd ℝ w [[a,b]]) (j : ℕ) :
    AnalyticOnNhd ℝ (iteratedDeriv j w) [[a,b]] := by
  simpa only [iteratedDeriv_eq_iterate] using hw.iterated_deriv j

theorem endpoint_expansion_exact {w : ℝ → ℂ} {a b : ℝ} {ζ : ℂ}
    (hw : AnalyticOnNhd ℝ w [[a,b]]) (hζ : ζ ≠ 0) (N : ℕ) :
    kernel w a b ζ - endpointSum w a b ζ N =
      (-1 : ℂ)^N / ζ^N * kernel (iteratedDeriv N w) a b ζ := by
  have hi := iterated_integration_by_parts (u := fun j => iteratedDeriv j w)
    hζ (fun j => (analytic_jet hw j).continuousOn)
    (fun j t ht => by
      simpa only [iteratedDeriv_succ] using
        ((analytic_jet hw j) t ht).differentiableAt.hasDerivAt) N
  have hi' : kernel w a b ζ = endpointSum w a b ζ N +
      (-1 : ℂ)^N / ζ^N * kernel (iteratedDeriv N w) a b ζ := by
    simpa [endpointSum] using hi
  rw [hi']
  abel

/-- Uniform endpoint asymptotics with one more inverse power than the last
displayed endpoint term. No remainder estimate is assumed. -/
theorem endpoint_expansion_bound {w : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hw : AnalyticOnNhd ℝ w [[a,b]]) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ : ℂ, ∀ c : ℝ,
      ζ ≠ 0 → 0 < c → c * ‖ζ‖ ≤ |ζ.re| →
      ‖kernel w a b ζ - endpointSum w a b ζ N‖ ≤
        C / c * (‖Complex.exp (ζ*(b:ℂ))‖ + ‖Complex.exp (ζ*(a:ℂ))‖) /
          ‖ζ‖^(N+1) := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa only [uIcc_of_le hab] using (analytic_jet hw N).continuousOn)
  let C : ℝ := max M 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ t ∈ Icc a b, ‖iteratedDeriv N w t‖ ≤ C := by
    intro t ht
    exact (hM t ht).trans (by dsimp [C]; linarith [le_max_left M 0])
  refine ⟨C,hC,?_⟩
  intro ζ c hζ hc hgap
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hre : ζ.re ≠ 0 := by
    intro hz
    simp only [hz,abs_zero] at hgap
    exact (not_le_of_gt (mul_pos hc hn)) hgap
  rw [endpoint_expansion_exact hw hζ N]
  have hr := norm_exact_remainder_le (u := fun j => iteratedDeriv j w)
    hab hC.le N hbound hre
  have hden : c * ‖ζ‖^(N+1) ≤ ‖ζ‖^N * |ζ.re| := by
    rw [pow_succ]
    calc
      c * (‖ζ‖^N * ‖ζ‖) = ‖ζ‖^N * (c*‖ζ‖) := by ring
      _ ≤ ‖ζ‖^N * |ζ.re| := mul_le_mul_of_nonneg_left hgap (by positivity)
  refine hr.trans ?_
  have hh := div_le_div_of_nonneg_left
    (show 0 ≤ C * (‖Complex.exp (ζ*(b:ℂ))‖ + ‖Complex.exp (ζ*(a:ℂ))‖) by positivity)
    (show 0 < c * ‖ζ‖^(N+1) by positivity) hden
  refine hh.trans_eq ?_
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

#print axioms analytic_jet
#print axioms endpoint_expansion_exact
#print axioms endpoint_expansion_bound
end CRGLinearKernelExpansion
