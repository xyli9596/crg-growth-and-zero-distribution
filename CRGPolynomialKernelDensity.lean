import CRGPolynomialKernelEntire
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CRGPolynomialKernel

/-- The density after the exact substitution `u = t^m`. -/
def powerDensity (w : ℝ → ℂ) (m : ℕ) (u : ℝ) : ℂ :=
  ((m : ℝ)⁻¹ * u ^ ((m : ℝ)⁻¹ - 1)) • w (u ^ (m : ℝ)⁻¹)

/-- The singular density at zero is permitted by the change-of-variables
formula, because the domain of substitution is `(0,1]`. -/
theorem powerKernel_eq_densityIntegral (w : ℝ → ℂ) {m : ℕ} (hm : 0 < m)
    (lam : ℂ) :
    laplaceIntegral w (fun t => (t : ℂ) ^ m) lam =
      laplaceIntegral (powerDensity w m) (fun u => (u : ℂ)) lam := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hmR
  have himg : (fun u : ℝ => u ^ (m : ℝ)⁻¹) '' Ioc 0 1 = Ioc 0 1 := by
    have h := (Real.continuous_rpow_const hp.le).continuousOn.image_Ioc_of_strictMonoOn
      zero_le_one ((Real.strictMonoOn_rpow_Ici_of_exponent_pos hp).mono Icc_subset_Ici_self)
    simpa [Real.zero_rpow hp.ne', Real.one_rpow] using h
  unfold laplaceIntegral
  rw [intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one, ← himg]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun u hu => (Real.hasDerivAt_rpow_const (Or.inl hu.1.ne')).hasDerivWithinAt)
    ((Real.rpow_left_injOn hp.ne').mono (fun u hu => hu.1.le))]
  rw [himg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have hu0 : 0 < u := hu.1
  have hpwr : (u ^ (m : ℝ)⁻¹) ^ m = u := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le, inv_mul_cancel₀ hmR.ne', Real.rpow_one]
  have hc : ((u ^ (m : ℝ)⁻¹ : ℝ) : ℂ) ^ m = (u : ℂ) := by
    rw [← Complex.ofReal_pow, hpwr]
  dsimp only
  rw [hc, abs_of_nonneg (mul_nonneg hp.le (Real.rpow_nonneg hu0.le _))]
  simp only [powerDensity, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- The transformed density is genuinely integrable at its singular endpoint. -/
theorem intervalIntegrable_powerDensity {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) {m : ℕ} (hm : 0 < m) :
    IntervalIntegrable (powerDensity w m) volume 0 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hmR
  have himg : (fun u : ℝ => u ^ (m : ℝ)⁻¹) '' Ioc 0 1 = Ioc 0 1 := by
    have h := (Real.continuous_rpow_const hp.le).continuousOn.image_Ioc_of_strictMonoOn
      zero_le_one ((Real.strictMonoOn_rpow_Ici_of_exponent_pos hp).mono Icc_subset_Ici_self)
    simpa [Real.zero_rpow hp.ne', Real.one_rpow] using h
  have hi : IntegrableOn w (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (hw.intervalIntegrable_of_Icc zero_le_one)
  have htrans := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    (show MeasurableSet (Ioc (0 : ℝ) 1) from measurableSet_Ioc)
    (fun u hu => (Real.hasDerivAt_rpow_const (Or.inl hu.1.ne')).hasDerivWithinAt)
    ((Real.rpow_left_injOn hp.ne').mono (fun u hu => hu.1.le)) w).mp
    (by simpa only [himg] using hi)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
  exact htrans.congr_fun (fun u hu => by
    dsimp only
    rw [abs_of_nonneg (mul_nonneg hp.le (Real.rpow_nonneg hu.1.le _))]
    rfl) measurableSet_Ioc

/-- Positive real powers are real analytic away from zero. -/
theorem analyticAt_rpow_positive {u : ℝ} (hu : 0 < u) (r : ℝ) :
    AnalyticAt ℝ (fun x : ℝ => x ^ r) u := by
  have ha : AnalyticAt ℝ (fun x : ℝ => Real.exp (Real.log x * r)) u :=
    ((analyticAt_log hu).mul (analyticAt_const (v := r))).rexp'
  apply ha.congr
  filter_upwards [eventually_gt_nhds hu] with x hx
  exact (Real.rpow_def_of_pos hx r).symm

/-- The transformed density is analytic throughout the punctured interval,
including at the growing endpoint. -/
theorem analyticOnNhd_powerDensity {w : ℝ → ℂ}
    (hw : AnalyticOnNhd ℝ w (Ioc 0 1)) {m : ℕ} (hm : 0 < m) :
    AnalyticOnNhd ℝ (powerDensity w m) (Ioc 0 1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  intro u hu
  have hp : 0 < (m : ℝ)⁻¹ := inv_pos.mpr hmR
  have hup : u ^ (m : ℝ)⁻¹ ∈ Ioc 0 1 := by
    constructor
    · exact Real.rpow_pos_of_pos hu.1 _
    · simpa only [Real.one_rpow] using Real.rpow_le_rpow hu.1.le hu.2 hp.le
  exact ((analyticAt_const (v := (m : ℝ)⁻¹)).mul
    (analyticAt_rpow_positive hu.1 ((m : ℝ)⁻¹ - 1))).smul
    ((hw _ hup).comp_of_eq (analyticAt_rpow_positive hu.1 (m : ℝ)⁻¹) rfl)

/-- Polynomial phases that differ by constants combine by multiplication of
the actual density, before endpoint expansions are compared. -/
theorem laplaceIntegral_add_parameter (w b : ℝ → ℂ) (lam c : ℂ) :
    laplaceIntegral w b (lam + c) =
      laplaceIntegral (fun t => w t * Complex.exp (c * b t)) b lam := by
  unfold laplaceIntegral
  congr 1
  funext t
  rw [add_mul, Complex.exp_add]
  ring

#print axioms powerKernel_eq_densityIntegral
#print axioms intervalIntegrable_powerDensity
#print axioms analyticOnNhd_powerDensity
#print axioms laplaceIntegral_add_parameter
end CRGPolynomialKernel
