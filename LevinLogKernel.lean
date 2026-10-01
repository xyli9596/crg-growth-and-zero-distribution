import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
A logarithmic radial kernel controlling oscillation of individual zero factors.
These are pointwise and integral estimates, not a complete Levin criterion.
-/
set_option autoImplicit false
open Set Metric Real Complex MeasureTheory intervalIntegral
namespace CRGLevinLogKernel

/-- Positive quantities bounded away from zero have logarithmic oscillation
controlled by their absolute difference through a logarithmic modulus. -/
theorem abs_log_sub_le {p q d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t)
    (hp : d ≤ p) (hq : d ≤ q) (hdiff : |p - q| ≤ t) :
    |Real.log p - Real.log q| ≤ Real.log (1 + t / d) := by
  have hp0 : 0 < p := hd.trans_le hp
  have hq0 : 0 < q := hd.trans_le hq
  have aux (p q : ℝ) (hp0 : 0 < p) (hq0 : 0 < q) (hq : d ≤ q)
      (hpq : p ≤ q + t) : Real.log p - Real.log q ≤ Real.log (1 + t / d) := by
    rw [← Real.log_div hp0.ne' hq0.ne']
    apply Real.log_le_log (div_pos hp0 hq0)
    calc
      p / q ≤ (q + t) / q := div_le_div_of_nonneg_right hpq hq0.le
      _ = 1 + t / q := by field_simp
      _ ≤ 1 + t / d := add_le_add_right (div_le_div_of_nonneg_left ht hd hq) 1
  have hdiff' := abs_le.mp hdiff
  exact abs_le.mpr ⟨by linarith [aux q p hq0 hp0 hp (by linarith)],
    aux p q hp0 hq0 hq (by linarith)⟩

/-- The logarithmic moduli of two zero factors are controlled by their separation
and a positive lower bound on their distances from the zero. -/
theorem zero_factor_log_difference {x y a : ℂ} {d : ℝ} (hd : 0 < d)
    (hx : d ≤ ‖x - a‖) (hy : d ≤ ‖y - a‖) :
    |Real.log ‖x - a‖ - Real.log ‖y - a‖| ≤ Real.log (1 + ‖x - y‖ / d) := by
  apply abs_log_sub_le hd (norm_nonneg _) hx hy
  have h := abs_norm_sub_norm_le (x - a) (y - a)
  simpa only [sub_sub_sub_cancel_right] using h

/-- The same bound on a circle, with a denominator depending only on the radius.
The excluded radii are explicitly those that meet the zero. -/
theorem circular_zero_factor_log_difference {v w a : ℂ} {r : ℝ}
    (hr : 0 < r) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hgap : r ≠ ‖a‖) :
    |Real.log ‖(r : ℂ) * v - a‖ - Real.log ‖(r : ℂ) * w - a‖| ≤
      Real.log (1 + r * ‖v - w‖ / |r - ‖a‖|) := by
  have hd : 0 < |r - ‖a‖| := abs_pos.mpr (sub_ne_zero.mpr hgap)
  have hv' : ‖(r : ℂ) * v‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hv]
  have hw' : ‖(r : ℂ) * w‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hw]
  have hx := abs_norm_sub_norm_le ((r : ℂ) * v) a
  have hy := abs_norm_sub_norm_le ((r : ℂ) * w) a
  rw [hv'] at hx
  rw [hw'] at hy
  have h := zero_factor_log_difference hd hx hy
  have heq : ‖(r : ℂ) * v - (r : ℂ) * w‖ = r * ‖v - w‖ := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  simpa only [heq] using h

/-- The radial majorant. Its arbitrary finite value at the singular point is
irrelevant for Lebesgue integration; pointwise factor bounds exclude that point. -/
noncomputable def radialKernel (h x : ℝ) : ℝ := Real.log (1 + h / |x|)

lemma radialKernel_nonneg {h x : ℝ} (hh : 0 ≤ h) : 0 ≤ radialKernel h x := by
  apply Real.log_nonneg
  have h := div_nonneg hh (abs_nonneg x)
  linarith

lemma radialKernel_eq_log_sub {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    radialKernel h x = Real.log (x + h) - Real.log x := by
  rw [radialKernel, abs_of_pos hx]
  have heq : 1 + h / x = (x + h) / x := by field_simp
  rw [heq, Real.log_div (by positivity : x + h ≠ 0) hx.ne']

/-- The logarithmic radial singularity is genuinely Lebesgue integrable. -/
theorem radialKernel_intervalIntegrable {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L) :
    IntervalIntegrable (radialKernel h) volume 0 L := by
  have hshift : IntervalIntegrable (fun x : ℝ => Real.log (x + h)) volume 0 L :=
    (IntervalIntegrable.comp_add_right_iff (c := h)).mpr intervalIntegrable_log'
  apply (hshift.sub intervalIntegrable_log').congr_uIoo
  intro x hx
  rw [uIoo_of_le hL] at hx
  exact (radialKernel_eq_log_sub hh hx.1).symm

/-- Exact integral of the radial logarithmic majorant. -/
theorem integral_radialKernel {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L) :
    (∫ x in 0..L, radialKernel h x) =
      (L + h) * Real.log (L + h) - L * Real.log L - h * Real.log h := by
  have hshift : IntervalIntegrable (fun x : ℝ => Real.log (x + h)) volume 0 L :=
    (IntervalIntegrable.comp_add_right_iff (c := h)).mpr intervalIntegrable_log'
  rw [intervalIntegral.integral_congr_Ioo_of_le hL
    (fun x hx => radialKernel_eq_log_sub hh hx.1)]
  rw [intervalIntegral.integral_sub hshift intervalIntegrable_log',
    intervalIntegral.integral_comp_add_right Real.log h]
  simp only [integral_log, zero_add, zero_mul, sub_zero, add_zero]
  ring

/-- The averaged radial kernel is `O(δ log(1/δ))` as the angular separation δ
shrinks. This estimate is what is needed before Markov's inequality. -/
theorem integral_radialKernel_unit_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ x in 0..1, radialKernel δ x) ≤ δ * (2 - Real.log δ) := by
  rw [integral_radialKernel hδ (by norm_num)]
  have hl : Real.log (1 + δ) ≤ δ := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + δ)
    linarith
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 1 + δ)
  simp only [Real.log_one, mul_zero, sub_zero]
  nlinarith

/-- Evenness extends the radial-kernel integrability to every finite interval. -/
theorem radialKernel_intervalIntegrable_all {h a b : ℝ} (hh : 0 < h) :
    IntervalIntegrable (radialKernel h) volume a b := by
  apply intervalIntegrable_of_even (fun x => by simp [radialKernel])
  intro x hx
  exact radialKernel_intervalIntegrable hh hx.le

/-- Integral on a symmetric interval, including the integrable central singularity. -/
theorem integral_radialKernel_symmetric {h L : ℝ} (hh : 0 < h) :
    (∫ x in -L..L, radialKernel h x) = 2 * (∫ x in 0..L, radialKernel h x) := by
  have hn : (∫ x in -L..0, radialKernel h x) = ∫ x in 0..L, radialKernel h x := by
    simpa [radialKernel] using (integral_comp_neg (radialKernel h) (a := -L) (b := 0))
  rw [← integral_add_adjacent_intervals (radialKernel_intervalIntegrable_all hh)
    (radialKernel_intervalIntegrable_all hh), hn]
  ring

/-- Scaling the spatial interval scales the radial-kernel integral linearly. -/
theorem integral_radialKernel_scale {δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) :
    (∫ x in 0..L, radialKernel (δ * L) x) =
      L * (∫ x in 0..1, radialKernel δ x) := by
  rw [integral_radialKernel (mul_pos hδ hL) hL.le,
    integral_radialKernel hδ (by norm_num)]
  have hsum : L + δ * L = L * (1 + δ) := by ring
  rw [hsum, Real.log_mul hL.ne' (by positivity : 1 + δ ≠ 0),
    Real.log_mul hδ.ne' hL.ne']
  simp only [Real.log_one, mul_zero, sub_zero]
  ring

/-- A uniform bound for every translated interval lying within distance L of the
singular radius. It is independent of the position of that radius. -/
theorem integral_radialKernel_shift_bound {δ L a b s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 < L)
    (hab : a ≤ b) (ha : -L ≤ a - s) (hb : b - s ≤ L) :
    (∫ x in a..b, radialKernel (δ * L) (x - s)) ≤
      2 * L * (δ * (2 - Real.log δ)) := by
  rw [integral_comp_sub_right]
  have hm := integral_mono_interval ha (sub_le_sub_right hab s) hb
    (Filter.Eventually.of_forall (fun x => radialKernel_nonneg (mul_pos hδ hL).le))
    (radialKernel_intervalIntegrable_all (mul_pos hδ hL))
  rw [integral_radialKernel_symmetric (mul_pos hδ hL),
    integral_radialKernel_scale hδ hL] at hm
  calc
    _ ≤ _ := hm
    _ = 2 * L * (∫ x in 0..1, radialKernel δ x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_radialKernel_unit_bound hδ hδ1)
      (by positivity)

/-- The angular scale `δ` yields a uniform radial L¹ bound on a dyadic annulus,
for any zero of modulus at most `8R`. -/
theorem integral_radialKernel_dyadic_bound {δ R s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 < R) (hs0 : 0 ≤ s) (hs : s ≤ 8 * R) :
    (∫ x in R..(2 * R), radialKernel (2 * δ * R) (x - s)) ≤
      4 * R * δ * (2 - Real.log (δ / 4)) := by
  have h := integral_radialKernel_shift_bound (δ := δ / 4) (L := 8 * R)
    (a := R) (b := 2 * R) (s := s)
    (by positivity) (by linarith) (by positivity)
    (by linarith) (by linarith) (by linarith)
  have heq : δ / 4 * (8 * R) = 2 * δ * R := by ring
  rw [heq] at h
  convert h using 1
  ring

/-- The angular bound has a radial majorant independent of the two directions,
which allows one bad set to control all sufficiently close direction pairs. -/
theorem circular_zero_factor_uniform_bound {v w a : ℂ} {r R δ : ℝ}
    (hr : 0 < r) (hrR : r ≤ 2 * R) (hδ : 0 ≤ δ)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : ‖v - w‖ ≤ δ) (hgap : r ≠ ‖a‖) :
    |Real.log ‖(r : ℂ) * v - a‖ - Real.log ‖(r : ℂ) * w - a‖| ≤
      radialKernel (2 * δ * R) (r - ‖a‖) := by
  apply (circular_zero_factor_log_difference hr hv hw hgap).trans
  apply Real.log_le_log (by positivity : 0 < 1 + r * ‖v - w‖ / |r - ‖a‖|)
  have hmul : r * ‖v - w‖ ≤ 2 * δ * R := by
    have h₁ := mul_le_mul_of_nonneg_left hvw hr.le
    have h₂ := mul_le_mul_of_nonneg_right hrR hδ
    nlinarith
  exact add_le_add_right (div_le_div_of_nonneg_right hmul (abs_nonneg _)) 1

/-- The explicit bound on the average tends to zero with the angular scale. -/
theorem radialKernel_modulus_tendsto_zero :
    Filter.Tendsto (fun δ : ℝ => δ * (2 - Real.log δ)) (nhds 0) (nhds 0) := by
  have hc : Continuous (fun δ : ℝ => 2 * δ - δ * Real.log δ) :=
    (continuous_const.mul continuous_id).sub Real.continuous_mul_log
  have heq : (fun δ : ℝ => δ * (2 - Real.log δ)) =
      (fun δ : ℝ => 2 * δ - δ * Real.log δ) := by funext δ; ring
  rw [heq]
  simpa using hc.tendsto 0

#print axioms abs_log_sub_le
#print axioms zero_factor_log_difference
#print axioms circular_zero_factor_log_difference
#print axioms radialKernel_nonneg
#print axioms radialKernel_eq_log_sub
#print axioms radialKernel_intervalIntegrable
#print axioms integral_radialKernel
#print axioms integral_radialKernel_unit_bound
#print axioms radialKernel_intervalIntegrable_all
#print axioms integral_radialKernel_symmetric
#print axioms integral_radialKernel_scale
#print axioms integral_radialKernel_shift_bound
#print axioms integral_radialKernel_dyadic_bound
#print axioms circular_zero_factor_uniform_bound
#print axioms radialKernel_modulus_tendsto_zero
end CRGLevinLogKernel
