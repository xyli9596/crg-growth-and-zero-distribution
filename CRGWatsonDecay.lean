import CRGWatsonTaylor

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace CRGWatson
open CRGPolynomialKernel

/-- Actual remainder estimate in the left half-plane, with its full Gamma
scaling. This is uniform in the complex parameter. -/
theorem laplace_power_remainder_bound {R : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {m : ℕ} (hm : 0 < m) (N : ℕ)
    (hR : ∀ t ∈ Icc 0 1, ‖R t‖ ≤ C * t ^ N)
    {lam : ℂ} (hlam : lam.re < 0) :
    ‖laplaceIntegral R (fun t => (t : ℂ) ^ m) lam‖ ≤
      C * ((-lam.re) ^ (-((N : ℝ) + 1) / (m : ℝ)) * (1 / (m : ℝ)) *
        Real.Gamma (((N : ℝ) + 1) / (m : ℝ))) := by
  have hA : 0 < -lam.re := neg_pos.mpr hlam
  have hmajorant : IntervalIntegrable
      (fun t : ℝ => C * (t ^ N * Real.exp (-(-lam.re) * t ^ m))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hnorm : ‖laplaceIntegral R (fun t => (t : ℂ) ^ m) lam‖ ≤
      ∫ t : ℝ in (0 : ℝ)..1, C * (t ^ N * Real.exp (-(-lam.re) * t ^ m)) := by
    unfold laplaceIntegral
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one _ hmajorant
    filter_upwards with t
    intro ht
    rw [norm_mul, Complex.norm_exp, ← Complex.ofReal_pow]
    have hexp : (lam * ((t ^ m : ℝ) : ℂ)).re = lam.re * t ^ m := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hexp]
    have h := mul_le_mul_of_nonneg_right (hR t (Ioc_subset_Icc_self ht))
      (Real.exp_nonneg (lam.re * t ^ m))
    simpa only [neg_neg, mul_assoc] using h
  calc
    _ ≤ _ := hnorm
    _ = C * ∫ t : ℝ in (0 : ℝ)..1, t ^ N * Real.exp (-(-lam.re) * t ^ m) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussian_moment_bound hA hm N) hC

/-- The preceding bound applies to all Taylor orders for analytic weights. -/
theorem analytic_decay_remainder_bound {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (hwa : AnalyticAt ℝ w 0)
    {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℂ, lam.re < 0 →
      ‖laplaceIntegral (fun t => w t - taylorPolynomial w N t)
        (fun t => (t : ℂ) ^ m) lam‖ ≤
        C * ((-lam.re) ^ (-((N : ℝ) + 1) / (m : ℝ)) * (1 / (m : ℝ)) *
          Real.Gamma (((N : ℝ) + 1) / (m : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := analytic_taylor_remainder_bound hw hwa N
  exact ⟨C, hC, fun lam hlam => laplace_power_remainder_bound hC hm N hbound hlam⟩

/-- Subtracting the Taylor polynomial under the integral is the actual error
in the coefficient function. -/
theorem integral_taylor_remainder {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (m N : ℕ) (lam : ℂ) :
    laplaceIntegral (fun t => w t - taylorPolynomial w N t)
      (fun t => (t : ℂ) ^ m) lam =
      laplaceIntegral w (fun t => (t : ℂ) ^ m) lam -
        laplaceIntegral (taylorPolynomial w N) (fun t => (t : ℂ) ^ m) lam := by
  unfold laplaceIntegral
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub]
  · exact laplaceIntegral_integrable hw (by fun_prop) lam
  · exact laplaceIntegral_integrable (continuous_taylorPolynomial w N).continuousOn
      (by fun_prop) lam

/-- On any fixed closed cone in the left half-plane, every Taylor order
has the claimed uniform fractional-power remainder estimate. -/
theorem analytic_decay_cone_remainder_bound {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (hwa : AnalyticAt ℝ w 0)
    {m : ℕ} (hm : 0 < m) (N : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ lam : ℂ, lam ≠ 0 → lam.re ≤ -c * ‖lam‖ →
      ‖laplaceIntegral (fun t => w t - taylorPolynomial w N t)
        (fun t => (t : ℂ) ^ m) lam‖ ≤
        B * ‖lam‖ ^ (-((N : ℝ) + 1) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let e : ℝ := -((N : ℝ) + 1) / (m : ℝ)
  have he : e ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N]) hmR.le
  have hGamma : 0 ≤ Real.Gamma (((N : ℝ) + 1) / (m : ℝ)) :=
    Real.Gamma_nonneg_of_nonneg (by positivity)
  obtain ⟨C, hC, hbound⟩ := analytic_decay_remainder_bound hw hwa hm N
  refine ⟨C * (c ^ e * (1 / (m : ℝ)) *
    Real.Gamma (((N : ℝ) + 1) / (m : ℝ))), by positivity, ?_⟩
  intro lam hne hcone
  have hnorm : 0 < ‖lam‖ := norm_pos_iff.mpr hne
  have hprod : 0 < c * ‖lam‖ := mul_pos hc hnorm
  have hA : c * ‖lam‖ ≤ -lam.re := by nlinarith [hcone]
  have hlam : lam.re < 0 := by linarith
  have hrpow : (-lam.re) ^ e ≤ (c * ‖lam‖) ^ e :=
    Real.rpow_le_rpow_of_nonpos hprod hA he
  calc
    _ ≤ C * ((-lam.re) ^ e * (1 / (m : ℝ)) *
          Real.Gamma (((N : ℝ) + 1) / (m : ℝ))) := hbound lam hlam
    _ ≤ C * ((c * ‖lam‖) ^ e * (1 / (m : ℝ)) *
          Real.Gamma (((N : ℝ) + 1) / (m : ℝ))) := by
      gcongr
    _ = _ := by rw [Real.mul_rpow hc.le (norm_nonneg lam)]; ring

#print axioms laplace_power_remainder_bound
#print axioms analytic_decay_remainder_bound
#print axioms integral_taylor_remainder
#print axioms analytic_decay_cone_remainder_bound
end CRGWatson
