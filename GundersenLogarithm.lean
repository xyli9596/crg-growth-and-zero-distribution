import GundersenAngles
import LevinAnalytic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Genuine logarithmic differentiation along nonzero complex curves, and the
zero-free analytic factor estimate used in the Gundersen proof. -/
noncomputable section
open Set Filter Metric
open scoped Topology RealInnerProductSpace
namespace GundersenLogarithm

theorem hasDerivAt_log_norm {g : ℝ → ℂ} {g' : ℂ} {r : ℝ}
    (hg : HasDerivAt g g' r) (hnz : g r ≠ 0) :
    HasDerivAt (fun t => Real.log ‖g t‖) (g' / g r).re r := by
  have hh := (hg.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hnz))).div_const 2
  have he : (fun t => Real.log (‖g t‖ ^ 2) / 2) = (fun t => Real.log ‖g t‖) := by
    ext t
    rw [Real.log_pow]
    ring
  rw [he] at hh
  have hv : (g' / g r).re = 2 * ⟪g r, g'⟫ / ‖g r‖ ^ 2 / 2 := by
    rw [real_inner_eq_re_inner, RCLike.inner_apply, Complex.div_re,
      Complex.sq_norm, Complex.normSq_apply]
    change _ = 2 * (g' * (starRingEnd ℂ) (g r)).re /
      ((g r).re * (g r).re + (g r).im * (g r).im) / 2
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hv]
  exact hh

theorem norm_deriv_log_norm_le {g : ℝ → ℂ} {g' : ℂ} {r : ℝ}
    (hg : HasDerivAt g g' r) (hnz : g r ≠ 0) :
    ‖deriv (fun t => Real.log ‖g t‖) r‖ ≤ ‖g' / g r‖ := by
  rw [(hasDerivAt_log_norm hg hnz).deriv, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

/-- The logarithmic derivative of a holomorphic zero-free factor is controlled
by the local oscillation of its logarithmic modulus. -/
theorem logDeriv_bound_of_log_lipschitz {f : ℂ → ℂ} {z : ℂ} {C : ℝ}
    (hf : DifferentiableAt ℂ f z) (hnz : f z ≠ 0) (hC : 0 ≤ C)
    (h : ∀ᶠ w in 𝓝 z, |Real.log ‖f w‖ - Real.log ‖f z‖| ≤ C * ‖w - z‖) :
    ‖logDeriv f z‖ ≤ 2 * C := by
  have hb (u : ℂ) (hu : ‖u‖ = 1) : |(deriv f z * u / f z).re| ≤ C := by
    have hcurve : HasDerivAt (fun t : ℝ => f (z + (t : ℂ) * u)) (deriv f z * u) 0 := by
      simpa using ((show HasDerivAt f (deriv f z) (z + (0 : ℂ) * u) by simpa using hf.hasDerivAt).comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).mul_const u |>.const_add z)).comp_ofReal
    have hlog := hasDerivAt_log_norm hcurve (by simpa using hnz)
    have hcont : ContinuousAt (fun t : ℝ => z + (t : ℂ) * u) 0 := by fun_prop
    have he := (show Tendsto (fun t : ℝ => z + (t : ℂ) * u) (𝓝 0) (𝓝 z) by simpa using hcont.tendsto).eventually h
    have hlip : ∀ᶠ t : ℝ in 𝓝 0,
        ‖Real.log ‖f (z + (t : ℂ) * u)‖ - Real.log ‖f (z + (0 : ℂ) * u)‖‖ ≤ C * ‖t - 0‖ := by
      filter_upwards [he] with t ht
      simpa [norm_mul, hu, Real.norm_eq_abs] using ht
    simpa [Real.norm_eq_abs] using hlog.le_of_lip' hC hlip
  have hr := hb 1 (norm_one)
  have hi := hb Complex.I (Complex.norm_I)
  have hr' : |(logDeriv f z).re| ≤ C := by simpa [logDeriv] using hr
  have hi' : |(logDeriv f z).im| ≤ C := by
    simpa [logDeriv, mul_div_right_comm, Complex.mul_I_re] using hi
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

/-- An actual analytic estimate for the zero-free part: upper logarithmic growth
and one center lower bound imply a logarithmic derivative bound of size M / R. -/
theorem zero_free_logDeriv_bound {f : ℂ → ℂ} {c z : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hnz : ∀ w ∈ closedBall c R, f w ≠ 0)
    (hz : z ∈ ball c (R / 4))
    (hbound : ∀ w ∈ closedBall c R, Real.log ‖f w‖ ≤ M)
    (hcenter : -M ≤ Real.log ‖f c‖) :
    ‖logDeriv f z‖ ≤ 160 * M / R := by
  have hzR : z ∈ closedBall c R :=
    closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz)
  have h := logDeriv_bound_of_log_lipschitz (hf z hzR).differentiableAt (hnz z hzR)
    (show 0 ≤ 80 * M / R by positivity) ?_
  · convert h using 1; ring
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact CRGLevinAnalytic.log_norm_quarter_disk_oscillation hR hM hf hnz
    (ball_subset_closedBall hw) (ball_subset_closedBall hz) hbound hcenter

#print axioms hasDerivAt_log_norm
#print axioms norm_deriv_log_norm_le
#print axioms logDeriv_bound_of_log_lipschitz
#print axioms zero_free_logDeriv_bound
end GundersenLogarithm
