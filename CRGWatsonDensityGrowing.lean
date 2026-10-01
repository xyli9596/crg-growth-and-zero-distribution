import CRGWatsonGrowing
import CRGPolynomialKernelDensity
import CRGWatsonExpansion

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators Interval
namespace CRGWatson
open CRGLinearKernelIntegration CRGLinearKernelExpansion CRGPolynomialKernel

def endpointSeries (v : ℝ → ℂ) (x : ℝ) (lam : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j / lam ^ (j + 1) * iteratedDeriv j v x

theorem normalized_endpointSum (v : ℝ → ℂ) (δ : ℝ) (lam : ℂ) (N : ℕ) :
    Complex.exp (-lam) * endpointSum v δ 1 lam N =
      endpointSeries v 1 lam N -
        Complex.exp (-lam * (1 - (δ : ℂ))) * endpointSeries v δ lam N := by
  have he1 : Complex.exp (-lam) * Complex.exp (lam * (1 : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  have heδ : Complex.exp (-lam) * Complex.exp (lam * (δ : ℂ)) =
      Complex.exp (-lam * (1 - (δ : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold endpointSum endpointSeries endpoint
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hupper := congrArg (fun z : ℂ => (-1 : ℂ) ^ j / lam ^ (j + 1) *
    iteratedDeriv j v 1 * z) he1
  have hlower := congrArg (fun z : ℂ => (-1 : ℂ) ^ j / lam ^ (j + 1) *
    iteratedDeriv j v δ * z) heδ
  simp only [Complex.ofReal_one] at *
  linear_combination hupper - hlower

theorem norm_endpointSeries_le (v : ℝ → ℂ) (x : ℝ) (lam : ℂ) (N : ℕ) :
    ‖endpointSeries v x lam N‖ ≤
      ∑ j ∈ Finset.range N, ‖iteratedDeriv j v x‖ / ‖lam‖ ^ (j + 1) := by
  unfold endpointSeries
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro j _
  simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
  ring

/-- The growing endpoint expansion with both exponentially small contributions
made explicit. It applies to an integrable density which may be singular at zero. -/
theorem growing_density_expansion_bound {v : ℝ → ℂ} {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hvi : IntervalIntegrable v volume 0 1)
    (hva : AnalyticOnNhd ℝ v [[δ, 1]]) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℂ, ∀ c : ℝ,
      lam ≠ 0 → 0 < c → c * ‖lam‖ ≤ lam.re →
      ‖Complex.exp (-lam) * kernel v 0 1 lam - endpointSeries v 1 lam N‖ ≤
        ((∫ t : ℝ in (0 : ℝ)..δ, ‖v t‖) +
          ∑ j ∈ Finset.range N, ‖iteratedDeriv j v δ‖ / ‖lam‖ ^ (j + 1)) *
          Real.exp (-lam.re * (1 - δ)) +
        (2 * C / c) / ‖lam‖ ^ (N + 1) := by
  obtain ⟨C, hC, hendpoint⟩ := endpoint_expansion_bound hδ1.le hva N
  refine ⟨C, hC, fun lam c hlam hc hcone => ?_⟩
  have hlamnorm : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  have hRe : 0 < lam.re := lt_of_lt_of_le (mul_pos hc hlamnorm) hcone
  have hv0 : IntervalIntegrable v volume 0 δ := hvi.mono_set (by
    rw [uIcc_of_le zero_le_one, uIcc_of_le hδ0.le]
    exact Icc_subset_Icc le_rfl hδ1.le)
  have hInt : IntervalIntegrable (fun t : ℝ => v t * Complex.exp (lam * (t : ℂ))) volume 0 1 :=
    hvi.mul_continuousOn (by fun_prop)
  have hsplit : kernel v 0 1 lam = kernel v 0 δ lam + kernel v δ 1 lam := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (hInt.mono_set (by
        rw [uIcc_of_le zero_le_one, uIcc_of_le hδ0.le]
        exact Icc_subset_Icc le_rfl hδ1.le))
      (hInt.mono_set (by
        rw [uIcc_of_le zero_le_one, uIcc_of_le hδ1.le]
        exact Icc_subset_Icc hδ0.le le_rfl))
  have hFlat : Real.exp (-lam.re * (1 - δ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hRe.le) (sub_nonneg.mpr hδ1.le)
  have hnormLeak : ‖Complex.exp (-lam * (1 - (δ : ℂ)))‖ =
      Real.exp (-lam.re * (1 - δ)) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.sub_re,
      Complex.one_re, Complex.ofReal_re, Complex.sub_im, Complex.one_im, Complex.ofReal_im]
    ring
  have hRem : ‖Complex.exp (-lam) * (kernel v δ 1 lam - endpointSum v δ 1 lam N)‖ ≤
      (2 * C / c) / ‖lam‖ ^ (N + 1) := by
    rw [norm_mul, Complex.norm_exp, Complex.neg_re]
    have hh := mul_le_mul_of_nonneg_left
      (hendpoint lam c hlam hc (by simpa only [abs_of_pos hRe] using hcone))
      (Real.exp_nonneg (-lam.re))
    have hprod1 : Real.exp (-lam.re) * Real.exp lam.re = 1 := by
      rw [← Real.exp_add]; simp
    have hprodδ : Real.exp (-lam.re) * Real.exp (lam.re * δ) =
        Real.exp (-lam.re * (1 - δ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hrhs : Real.exp (-lam.re) *
        (C / c * (‖Complex.exp (lam * (1 : ℂ))‖ + ‖Complex.exp (lam * (δ : ℂ))‖) /
          ‖lam‖ ^ (N + 1)) =
        (C / c * (1 + Real.exp (-lam.re * (1 - δ)))) / ‖lam‖ ^ (N + 1) := by
      simp only [Complex.norm_exp, mul_one]
      have hreδ : (lam * (δ : ℂ)).re = lam.re * δ := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [hreδ]
      linear_combination (C / c / ‖lam‖ ^ (N + 1)) * hprod1 +
        (C / c / ‖lam‖ ^ (N + 1)) * hprodδ
    refine hh.trans (hrhs.le.trans ?_)
    have hCpos : 0 ≤ C / c := (div_pos hC hc).le
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ (C / c) * 2 := mul_le_mul_of_nonneg_left (by linarith [hFlat]) hCpos
      _ = _ := by ring
  have hExact : Complex.exp (-lam) * kernel v 0 1 lam - endpointSeries v 1 lam N =
      Complex.exp (-lam) * kernel v 0 δ lam +
      Complex.exp (-lam) * (kernel v δ 1 lam - endpointSum v δ 1 lam N) -
      Complex.exp (-lam * (1 - (δ : ℂ))) * endpointSeries v δ lam N := by
    rw [hsplit]
    have he := normalized_endpointSum v δ lam N
    linear_combination he
  rw [hExact]
  calc
    _ ≤ ‖Complex.exp (-lam) * kernel v 0 δ lam‖ +
        ‖Complex.exp (-lam) * (kernel v δ 1 lam - endpointSum v δ 1 lam N)‖ +
        ‖Complex.exp (-lam * (1 - (δ : ℂ))) * endpointSeries v δ lam N‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      have hLower := normalized_initial_density_bound hδ0.le hv0 lam hRe.le
      have hLeak := mul_le_mul_of_nonneg_left (norm_endpointSeries_le v δ lam N)
        (Real.exp_nonneg (-lam.re * (1 - δ)))
      have hLeakNorm : ‖Complex.exp (-lam * (1 - (δ : ℂ))) * endpointSeries v δ lam N‖ ≤
          Real.exp (-lam.re * (1 - δ)) *
            (∑ j ∈ Finset.range N, ‖iteratedDeriv j v δ‖ / ‖lam‖ ^ (j + 1)) := by
        rw [norm_mul, hnormLeak]
        exact hLeak
      nlinarith [hLower, hRem, hLeakNorm]

/-- The growing endpoint expansion of an integrable analytic density is
uniform to every inverse-power order on each closed cone. -/
theorem growing_density_uniform_expansion {v : ℝ → ℂ} {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hvi : IntervalIntegrable v volume 0 1)
    (hva : AnalyticOnNhd ℝ v [[δ, 1]]) (N : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ R : ℝ, 1 ≤ R ∧ ∀ lam : ℂ,
      R ≤ ‖lam‖ → c * ‖lam‖ ≤ lam.re →
      ‖Complex.exp (-lam) * kernel v 0 1 lam - endpointSeries v 1 lam N‖ ≤
        B / ‖lam‖ ^ (N + 1) := by
  obtain ⟨C, hC, hbound⟩ := growing_density_expansion_bound hδ0 hδ1 hvi hva N
  let D : ℝ := (∫ t : ℝ in (0 : ℝ)..δ, ‖v t‖) +
    ∑ j ∈ Finset.range N, ‖iteratedDeriv j v δ‖
  have hInt : 0 ≤ ∫ t : ℝ in (0 : ℝ)..δ, ‖v t‖ :=
    intervalIntegral.integral_nonneg_of_forall hδ0.le (fun t => norm_nonneg (v t))
  have hD : 0 ≤ D := add_nonneg hInt (Finset.sum_nonneg (fun j _ => norm_nonneg _))
  have ha : 0 < c * (1 - δ) := mul_pos hc (sub_pos.mpr hδ1)
  obtain ⟨M, hM, R, hR, hflat⟩ := exponential_flat_bound ha (-((N + 1 : ℕ) : ℝ))
  refine ⟨D * M + 2 * C / c, by positivity, R, hR, ?_⟩
  intro lam hRlam hcone
  have hnorm1 : 1 ≤ ‖lam‖ := hR.trans hRlam
  have hnorm : 0 < ‖lam‖ := zero_lt_one.trans_le hnorm1
  have hlam : lam ≠ 0 := norm_pos_iff.mp hnorm
  have hsum : (∫ t : ℝ in (0 : ℝ)..δ, ‖v t‖) +
      (∑ j ∈ Finset.range N, ‖iteratedDeriv j v δ‖ / ‖lam‖ ^ (j + 1)) ≤ D := by
    dsimp [D]
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro j _
    exact div_le_self (norm_nonneg _) (one_le_pow₀ hnorm1)
  have hExp : Real.exp (-lam.re * (1 - δ)) ≤
      Real.exp (-(c * (1 - δ)) * ‖lam‖) := Real.exp_le_exp.mpr (by nlinarith)
  have hFlat : Real.exp (-(c * (1 - δ)) * ‖lam‖) ≤ M / ‖lam‖ ^ (N + 1) := by
    have h := hflat ‖lam‖ hRlam
    simpa only [Real.rpow_neg hnorm.le, Real.rpow_natCast,
      div_eq_mul_inv] using h
  calc
    _ ≤ _ := hbound lam c hlam hc hcone
    _ ≤ D * Real.exp (-lam.re * (1 - δ)) + (2 * C / c) / ‖lam‖ ^ (N + 1) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hsum (Real.exp_nonneg _)) le_rfl
    _ ≤ D * Real.exp (-(c * (1 - δ)) * ‖lam‖) + (2 * C / c) / ‖lam‖ ^ (N + 1) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hExp hD) le_rfl
    _ ≤ D * (M / ‖lam‖ ^ (N + 1)) + (2 * C / c) / ‖lam‖ ^ (N + 1) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hFlat hD) le_rfl
    _ = _ := by ring

/-- The full growing Watson expansion for the paper's `t^m` kernel, with
analytic source weights and the density coefficients computed by substitution. -/
theorem analytic_growing_uniform_expansion {w : ℝ → ℂ}
    (hw : AnalyticOnNhd ℝ w (Icc 0 1)) {m : ℕ} (hm : 0 < m) (N : ℕ)
    {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ R : ℝ, 1 ≤ R ∧ ∀ lam : ℂ,
      R ≤ ‖lam‖ → c * ‖lam‖ ≤ lam.re →
      ‖Complex.exp (-lam) * laplaceIntegral w (fun t => (t : ℂ) ^ m) lam -
        endpointSeries (powerDensity w m) 1 lam N‖ ≤ B / ‖lam‖ ^ (N + 1) := by
  have hvi := intervalIntegrable_powerDensity hw.continuousOn hm
  have hva := analyticOnNhd_powerDensity (hw.mono Ioc_subset_Icc_self) hm
  have hupper : AnalyticOnNhd ℝ (powerDensity w m) [[(1 / 2 : ℝ), 1]] := by
    apply hva.mono
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    intro u hu
    exact ⟨by linarith [hu.1], hu.2⟩
  obtain ⟨B, hB, R, hR, hbound⟩ := growing_density_uniform_expansion
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hvi hupper N hc
  refine ⟨B, hB, R, hR, fun lam hnorm hcone => ?_⟩
  rw [powerKernel_eq_densityIntegral w hm lam]
  exact hbound lam hnorm hcone

#print axioms growing_density_expansion_bound
#print axioms growing_density_uniform_expansion
#print axioms analytic_growing_uniform_expansion
end CRGWatson
