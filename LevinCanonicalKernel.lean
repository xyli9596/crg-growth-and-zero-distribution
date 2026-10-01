import LevinLogKernel
import Mathlib.Analysis.Complex.CanonicalDecomposition

/-! Quantitative angular control of the actual finite Blaschke canonical factor. -/
set_option autoImplicit false
open Real Complex Set Metric
open ComplexConjugate
namespace CRGLevinCanonicalKernel

/-- The numerator of a canonical factor stays uniformly away from zero on the
inner half disk, even when the original zero approaches the outer boundary. -/
theorem canonical_numerator_lower {R : ℝ} {a z : ℂ} (hR : 0 < R)
    (ha : ‖a‖ ≤ R) (hz : ‖z‖ ≤ R / 2) :
    R ^ 2 / 2 ≤ ‖(R : ℂ) ^ 2 - conj a * z‖ := by
  have hp : ‖conj a * z‖ ≤ R * (R / 2) := by
    rw [norm_mul, norm_conj]
    exact mul_le_mul ha hz (norm_nonneg _) hR.le
  have h := norm_sub_norm_le ((R : ℂ) ^ 2) (conj a * z)
  have hnorm : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  rw [hnorm] at h
  nlinarith

/-- The logarithmic modulus of the smooth numerator has a linear oscillation
bound independent of the position of the original zero. -/
theorem canonical_numerator_log_difference {R : ℝ} {a z w : ℂ} (hR : 0 < R)
    (ha : ‖a‖ ≤ R) (hz : ‖z‖ ≤ R / 2) (hw : ‖w‖ ≤ R / 2) :
    |Real.log ‖(R : ℂ) ^ 2 - conj a * z‖ -
      Real.log ‖(R : ℂ) ^ 2 - conj a * w‖| ≤ (2 / R) * ‖z - w‖ := by
  have hd : 0 < R ^ 2 / 2 := by positivity
  have hdiff : |‖(R : ℂ) ^ 2 - conj a * z‖ - ‖(R : ℂ) ^ 2 - conj a * w‖| ≤
      R * ‖z - w‖ := by
    have h := abs_norm_sub_norm_le ((R : ℂ) ^ 2 - conj a * z)
      ((R : ℂ) ^ 2 - conj a * w)
    have heq : ((R : ℂ) ^ 2 - conj a * z) - ((R : ℂ) ^ 2 - conj a * w) =
        conj a * (w - z) := by ring
    rw [heq, norm_mul, norm_conj, norm_sub_rev w z] at h
    exact h.trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  have h := CRGLevinLogKernel.abs_log_sub_le hd (mul_nonneg hR.le (norm_nonneg _))
    (canonical_numerator_lower hR ha hz) (canonical_numerator_lower hR ha hw) hdiff
  have hl := Real.log_le_sub_one_of_pos
    (by positivity : 0 < 1 + R * ‖z - w‖ / (R ^ 2 / 2))
  calc
    _ ≤ _ := h
    _ ≤ R * ‖z - w‖ / (R ^ 2 / 2) := by linarith
    _ = _ := by field_simp

/-- The true canonical factor inherits a smooth numerator term plus the singular
zero-factor radial term. All zero-avoidance requirements are explicit. -/
theorem canonicalFactor_log_difference {R d : ℝ} {a z w : ℂ} (hR : 0 < R)
    (ha : ‖a‖ ≤ R) (hz : ‖z‖ ≤ R / 2) (hw : ‖w‖ ≤ R / 2)
    (hd : 0 < d) (hza : d ≤ ‖z - a‖) (hwa : d ≤ ‖w - a‖) :
    |Real.log ‖canonicalFactor R a z‖ - Real.log ‖canonicalFactor R a w‖| ≤
      (2 / R) * ‖z - w‖ + Real.log (1 + ‖z - w‖ / d) := by
  have aux (x : ℂ) (hx : ‖x‖ ≤ R / 2) (hxa : d ≤ ‖x - a‖) :
      Real.log ‖canonicalFactor R a x‖ =
        Real.log ‖(R : ℂ) ^ 2 - conj a * x‖ - Real.log R - Real.log ‖x - a‖ := by
    have hn : 0 < ‖(R : ℂ) ^ 2 - conj a * x‖ :=
      lt_of_lt_of_le (by positivity : 0 < R ^ 2 / 2) (canonical_numerator_lower hR ha hx)
    have hnx : 0 < ‖x - a‖ := hd.trans_le hxa
    rw [canonicalFactor_apply, norm_div, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR,
      Real.log_div hn.ne' (mul_pos hR hnx).ne', Real.log_mul hR.ne' hnx.ne']
    ring
  rw [aux z hz hza, aux w hw hwa]
  have heq : Real.log ‖(R : ℂ) ^ 2 - conj a * z‖ - Real.log R - Real.log ‖z - a‖ -
      (Real.log ‖(R : ℂ) ^ 2 - conj a * w‖ - Real.log R - Real.log ‖w - a‖) =
      (Real.log ‖(R : ℂ) ^ 2 - conj a * z‖ - Real.log ‖(R : ℂ) ^ 2 - conj a * w‖) -
      (Real.log ‖z - a‖ - Real.log ‖w - a‖) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add (canonical_numerator_log_difference hR ha hz hw)
    (CRGLevinLogKernel.zero_factor_log_difference hd hza hwa))

/-- On a dyadic annulus, every sufficiently close pair of angular directions is
controlled by the same radial function for the actual canonical factor. -/
theorem canonicalFactor_circle_uniform_bound {S R r δ : ℝ} {a v w : ℂ}
    (hS : 0 < S) (hr : 0 < r) (hrS : r ≤ S / 2) (hrR : r ≤ 2 * R)
    (ha : ‖a‖ ≤ S) (hδ : 0 ≤ δ) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : ‖v - w‖ ≤ δ) (hgap : r ≠ ‖a‖) :
    |Real.log ‖canonicalFactor S a ((r : ℂ) * v)‖ -
      Real.log ‖canonicalFactor S a ((r : ℂ) * w)‖| ≤
      δ + CRGLevinLogKernel.radialKernel (2 * δ * R) (r - ‖a‖) := by
  have hv' : ‖(r : ℂ) * v‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hv]
  have hw' : ‖(r : ℂ) * w‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hw]
  have hd : 0 < |r - ‖a‖| := abs_pos.mpr (sub_ne_zero.mpr hgap)
  have hza : |r - ‖a‖| ≤ ‖(r : ℂ) * v - a‖ := by
    simpa only [hv'] using abs_norm_sub_norm_le ((r : ℂ) * v) a
  have hwa : |r - ‖a‖| ≤ ‖(r : ℂ) * w - a‖ := by
    simpa only [hw'] using abs_norm_sub_norm_le ((r : ℂ) * w) a
  have h := canonicalFactor_log_difference hS ha (by simpa only [hv'] using hrS)
    (by simpa only [hw'] using hrS) hd hza hwa
  have heq : ‖(r : ℂ) * v - (r : ℂ) * w‖ = r * ‖v - w‖ := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [heq] at h
  have hsmooth : (2 / S) * (r * ‖v - w‖) ≤ δ := by
    have hratio : 2 * r / S ≤ 1 := (div_le_one hS).mpr (by linarith)
    have hmul := mul_le_mul hratio hvw (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    calc
      _ = (2 * r / S) * ‖v - w‖ := by ring
      _ ≤ 1 * δ := hmul
      _ = δ := one_mul δ
  have hsingular : Real.log (1 + r * ‖v - w‖ / |r - ‖a‖|) ≤
      CRGLevinLogKernel.radialKernel (2 * δ * R) (r - ‖a‖) := by
    apply Real.log_le_log (by positivity)
    have hmul : r * ‖v - w‖ ≤ 2 * δ * R := by
      have h₁ := mul_le_mul_of_nonneg_left hvw hr.le
      have h₂ := mul_le_mul_of_nonneg_right hrR hδ
      nlinarith
    exact add_le_add_right (div_le_div_of_nonneg_right hmul (abs_nonneg _)) 1
  exact h.trans (add_le_add hsmooth hsingular)

#print axioms canonical_numerator_lower
#print axioms canonical_numerator_log_difference
#print axioms canonicalFactor_log_difference
#print axioms canonicalFactor_circle_uniform_bound
end CRGLevinCanonicalKernel
