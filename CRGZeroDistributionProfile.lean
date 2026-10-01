import CRGIndicatorCorollary
import CRGZeroDistributionScaled

/-! The homogeneous indicators obtained in Corollary 3.6(1) are genuinely
harmonic on sectors between their change rays. Principal slit-plane charts
are used here to construct the fractional-power analytic profile. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric Complex InnerProductSpace
open scoped Topology
namespace CRGZeroDistributionProfile
open LevinGrowth LevinIndicatorModulus CRGPhaseDirections

/-- The normalized direction is the actual principal argument direction. -/
theorem normalizedDirection_eq_angleDirection {z : ℂ} (hz : z ≠ 0) :
    normalizedDirection z = CRGOrderLevin.angleDirection z.arg := by
  apply Subtype.ext
  simp only [normalizedDirection, dif_neg hz, CRGOrderLevin.angleDirection]
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  apply (div_eq_iff hn).mpr
  have hh := Complex.norm_mul_exp_arg_mul_I z
  simpa only [mul_comm] using hh.symm

/-- The actual complex fractional power has the expected polar leading term. -/
theorem cpow_real_polar {z : ℂ} (hz : z ≠ 0) (ρ : ℝ) :
    z ^ (ρ : ℂ) = (‖z‖^ρ : ℝ) * Complex.exp (((ρ*z.arg : ℝ) : ℂ)*Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero hz]
  have heq : Complex.log z * (ρ : ℂ) =
      ((Real.log ‖z‖ * ρ : ℝ) : ℂ) + (((ρ*z.arg : ℝ) : ℂ)*Complex.I) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.log_re, Complex.log_im] <;> ring
  rw [heq, Complex.exp_add]
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz), Complex.ofReal_exp]

/-- A finite-phase indicator formula gives the analytic fractional-power
profile on every open principal-argument sector where that formula holds. -/
theorem homogeneousIndicator_eq_cpow {h : Direction → ℝ} {c z : ℂ} {ρ : ℝ}
    (hz : z ≠ 0)
    (hh : h (CRGOrderLevin.angleDirection z.arg) = leadingReal c ρ z.arg) :
    homogeneousIndicator ρ h z = (c * z^(ρ : ℂ)).re := by
  rw [homogeneousIndicator, normalizedDirection_eq_angleDirection hz, hh, cpow_real_polar hz]
  unfold leadingReal
  have heq : c * ((‖z‖^ρ : ℝ) * Complex.exp (((ρ*z.arg : ℝ) : ℂ)*Complex.I)) =
      ((‖z‖^ρ : ℝ) : ℂ) * (c * Complex.exp (((ρ*z.arg : ℝ) : ℂ)*Complex.I)) := by ring
  rw [heq]
  simp [Complex.mul_re]

/-- The harmonicity conclusion is derived from the indicator formula;
no analytic or harmonic profile certificate is assumed for the indicator. -/
theorem homogeneousIndicator_harmonicOnNhd {h : Direction → ℝ} {c : ℂ} {ρ : ℝ}
    {U : Set ℂ} (hU : IsOpen U) (hslit : U ⊆ Complex.slitPlane)
    (hformula : ∀ z ∈ U,
      h (CRGOrderLevin.angleDirection z.arg) = leadingReal c ρ z.arg) :
    HarmonicOnNhd (homogeneousIndicator ρ h) U := by
  intro z hz
  have hza : AnalyticAt ℂ (fun w : ℂ => c * w^(ρ : ℂ)) z :=
    analyticAt_const.mul (analyticAt_id.cpow analyticAt_const (hslit hz))
  have heq : homogeneousIndicator ρ h =ᶠ[𝓝 z]
      (fun w : ℂ => (c * w^(ρ : ℂ)).re) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact homogeneousIndicator_eq_cpow (Complex.slitPlane_ne_zero (hslit hw)) (hformula w hw)
  exact (harmonicAt_congr_nhds heq).mpr hza.harmonicAt_re

#print axioms normalizedDirection_eq_angleDirection
#print axioms cpow_real_polar
#print axioms homogeneousIndicator_eq_cpow
#print axioms homogeneousIndicator_harmonicOnNhd
end CRGZeroDistributionProfile
