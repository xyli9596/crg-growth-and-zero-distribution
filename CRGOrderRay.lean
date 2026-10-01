import CRGPhragmenPolynomialRay
import CRGRay
import LevinC0

noncomputable section
open Set Filter Complex
open scoped Topology
namespace CRGOrderRay

abbrev logValue (f : ℂ → ℂ) (θ r : ℝ) : ℝ :=
  Real.log ‖f (CRGPhragmenRay.point θ r)‖

/-- The information retained from a nondegenerate finite phase expansion.
For zero degree the logarithmic error, rather than a fictitious constant
limit, is retained explicitly. -/
structure RayData (f : ℂ → ℂ) (θ d a : ℝ) : Prop where
  nonzero : ∀ᶠ r : ℝ in atTop, f (CRGPhragmenRay.point θ r) ≠ 0
  degree_nonneg : 0 ≤ d
  zero : d = 0 → ∃ C : ℝ, ∀ᶠ r : ℝ in atTop, |logValue f θ r| ≤ C * Real.log r
  positive : 0 < d → a ≠ 0 ∧
    Tendsto (fun r : ℝ => logValue f θ r / r ^ d) atTop (𝓝 a)

theorem norm_le_exp_of_log_le {z : ℂ} {u : ℝ} (hz : z ≠ 0)
    (h : Real.log ‖z‖ ≤ u) : ‖z‖ ≤ Real.exp u := by
  rw [← Real.exp_log (norm_pos_iff.mpr hz)]
  exact Real.exp_le_exp.mpr h

theorem zero_degree_polynomial {f : ℂ → ℂ} {θ d a : ℝ}
    (h : RayData f θ d a) (hd : d = 0) :
    ∃ A : ℝ, 0 < A ∧ ∃ k R : ℝ, ∀ r : ℝ, R ≤ r →
      ‖f (CRGPhragmenRay.point θ r)‖ ≤ A * r ^ k := by
  obtain ⟨C, hC⟩ := h.zero hd
  have he : ∀ᶠ r : ℝ in atTop,
      ‖f (CRGPhragmenRay.point θ r)‖ ≤ r ^ C := by
    filter_upwards [hC, h.nonzero, eventually_gt_atTop (0 : ℝ)] with r hr hn hr0
    have hh := norm_le_exp_of_log_le hn ((le_abs_self _).trans hr)
    simpa only [Real.rpow_def_of_pos hr0, mul_comm C (Real.log r)] using hh
  obtain ⟨R, hR⟩ := eventually_atTop.1 he
  exact ⟨1, zero_lt_one, C, R, fun r hr => by simpa using hR r hr⟩

theorem negative_leading_bounded {f : ℂ → ℂ} {θ d a : ℝ}
    (h : RayData f θ d a) (hd : 0 < d) (ha : a < 0) :
    ∀ᶠ r : ℝ in atTop, ‖f (CRGPhragmenRay.point θ r)‖ ≤ 1 := by
  have hl := (h.positive hd).2.eventually (gt_mem_nhds ha)
  filter_upwards [hl, h.nonzero, eventually_gt_atTop (0 : ℝ)] with r hr hn hr0
  have hp := Real.rpow_pos_of_pos hr0 d
  have hu : logValue f θ r ≤ 0 := by
    have hh := (div_lt_iff₀ hp).mp hr
    simpa using hh.le
  simpa using norm_le_exp_of_log_le hn hu

theorem positive_leading_upper {f : ℂ → ℂ} {θ d a σ : ℝ}
    (h : RayData f θ d a) (hd : 0 < d) (ha : 0 < a) (hdσ : d ≤ σ) :
    ∃ C R : ℝ, ∀ r : ℝ, R ≤ r →
      ‖f (CRGPhragmenRay.point θ r)‖ ≤ Real.exp (C * r ^ σ) := by
  have hl := (h.positive hd).2.eventually (gt_mem_nhds (lt_add_one a))
  have he : ∀ᶠ r : ℝ in atTop,
      ‖f (CRGPhragmenRay.point θ r)‖ ≤ Real.exp ((a + 1) * r ^ σ) := by
    filter_upwards [hl, h.nonzero, eventually_ge_atTop (1 : ℝ)] with r hr hn hr1
    have hp := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hr1) d
    apply norm_le_exp_of_log_le hn
    apply ((div_lt_iff₀ hp).mp hr).le.trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr1 hdσ) (by linarith)
  obtain ⟨R, hR⟩ := eventually_atTop.1 he
  exact ⟨a + 1, R, hR⟩

theorem positive_leading_lower {f : ℂ → ℂ} {θ d a : ℝ}
    (h : RayData f θ d a) (hd : 0 < d) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∃ z : ℂ, max R 1 ≤ ‖z‖ ∧
      Real.exp (c * ‖z‖ ^ d) ≤ ‖f z‖ := by
  have hl := (h.positive hd).2.eventually (lt_mem_nhds (show a / 2 < a by linarith))
  refine ⟨a / 2, by positivity, fun R => ?_⟩
  obtain ⟨r, hr, hn, hrR⟩ := (hl.and (h.nonzero.and (eventually_ge_atTop (max R 1)))).exists
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hrR)
  have hnorm : ‖CRGPhragmenRay.point θ r‖ = r := by
    simp [CRGPhragmenRay.point, Complex.norm_exp, Real.norm_of_nonneg hr0.le]
  refine ⟨CRGPhragmenRay.point θ r, by simpa only [hnorm] using hrR, ?_⟩
  rw [hnorm, ← Real.exp_log (norm_pos_iff.mpr hn)]
  apply Real.exp_le_exp.mpr
  exact ((lt_div_iff₀ (Real.rpow_pos_of_pos hr0 d)).mp hr).le

theorem zero_normalized_limit {f : ℂ → ℂ} {θ d a ρ : ℝ}
    (h : RayData f θ d a) (hd : d = 0) (hρ : 0 < ρ) :
    Tendsto (fun r : ℝ => logValue f θ r / r ^ ρ) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := h.zero hd
  have hlog := (isLittleO_log_rpow_atTop hρ).tendsto_div_nhds_zero
  have hub : ∀ᶠ r : ℝ in atTop,
      |logValue f θ r / r ^ ρ| ≤ C * (Real.log r / r ^ ρ) := by
    filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hr0 ρ), ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hr (Real.rpow_pos_of_pos hr0 ρ).le
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hub (by simpa using hlog.const_mul C)

/-- Normalize at a larger degree. This is the actual finite radial limit
needed by Levin, with zero-degree rays treated separately. -/
theorem normalized_limit {f : ℂ → ℂ} {θ d a ρ : ℝ}
    (h : RayData f θ d a) (hρ : 0 < ρ) (hdρ : d ≤ ρ) :
    ∃ L : ℝ, Tendsto (fun r : ℝ => logValue f θ r / r ^ ρ) atTop (𝓝 L) := by
  by_cases hd0 : d = 0
  · exact ⟨0, zero_normalized_limit h hd0 hρ⟩
  have hd : 0 < d := lt_of_le_of_ne h.degree_nonneg (Ne.symm hd0)
  by_cases heq : d = ρ
  · subst d
    exact ⟨a, (h.positive hd).2⟩
  have hlt : d < ρ := lt_of_le_of_ne hdρ heq
  have ht := (h.positive hd).2.mul (tendsto_rpow_neg_atTop (sub_pos.mpr hlt))
  refine ⟨0, ?_⟩
  have ht' := ht
  simp only [mul_zero] at ht'
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [Real.rpow_neg hr.le, Real.rpow_sub hr, div_eq_mul_inv]
  field_simp

theorem zero_degree_upper {f : ℂ → ℂ} {θ d a σ : ℝ}
    (h : RayData f θ d a) (hd : d = 0) (hσ : 0 < σ) :
    ∃ C R : ℝ, ∀ r : ℝ, R ≤ r →
      ‖f (CRGPhragmenRay.point θ r)‖ ≤ Real.exp (C * r ^ σ) := by
  have hl := (zero_normalized_limit h hd hσ).eventually (gt_mem_nhds zero_lt_one)
  have he : ∀ᶠ r : ℝ in atTop,
      ‖f (CRGPhragmenRay.point θ r)‖ ≤ Real.exp (1 * r ^ σ) := by
    filter_upwards [hl, h.nonzero, eventually_gt_atTop (0 : ℝ)] with r hr hn hr0
    exact norm_le_exp_of_log_le hn ((div_lt_iff₀ (Real.rpow_pos_of_pos hr0 σ)).mp hr).le
  obtain ⟨R, hR⟩ := eventually_atTop.1 he
  exact ⟨1, R, hR⟩

#print axioms norm_le_exp_of_log_le
#print axioms zero_degree_polynomial
#print axioms negative_leading_bounded
#print axioms positive_leading_upper
#print axioms positive_leading_lower
#print axioms zero_normalized_limit
#print axioms normalized_limit
#print axioms zero_degree_upper
end CRGOrderRay
