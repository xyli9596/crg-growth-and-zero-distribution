import CRGProgress
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Decay and genuine integrability of an actual analytic remainder whose initial
Taylor coefficients vanish.  The power-series hypothesis belongs to the actual
residual after finite truncation.  No convergence of the full formal gauge or
formal transformed series is assumed or inferred.
-/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace WasowAnalyticRemainder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem partialSum_eq_zero {p : FormalMultilinearSeries ℂ ℂ E} {N : ℕ}
    (hp : ∀ k < N, p.coeff k = 0) (z : ℂ) : p.partialSum N z = 0 := by
  unfold FormalMultilinearSeries.partialSum
  apply Finset.sum_eq_zero
  intro k hk
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, hp k (Finset.mem_range.mp hk), smul_zero]

theorem isBigO_of_initial_coefficients_zero {f : ℂ → E}
    {p : FormalMultilinearSeries ℂ ℂ E} {N : ℕ}
    (hf : HasFPowerSeriesAt f p 0) (hp : ∀ k < N, p.coeff k = 0) :
    f =O[𝓝 0] (fun z : ℂ => ‖z‖ ^ N) := by
  simpa only [zero_add, partialSum_eq_zero hp, sub_zero] using hf.isBigO_sub_partialSum_pow N

theorem inverse_real_tendsto_zero :
    Tendsto (fun r : ℝ => (r : ℂ)⁻¹) atTop (𝓝 0) := by
  simpa only [Complex.ofReal_inv, Complex.ofReal_zero] using tendsto_inv_atTop_zero.ofReal

/-- One common genuine tail supports both continuity and a pointwise bound. -/
theorem exists_inverse_tail_bound {f : ℂ → E}
    {p : FormalMultilinearSeries ℂ ℂ E} {N : ℕ}
    (hf : HasFPowerSeriesAt f p 0) (hp : ∀ k < N, p.coeff k = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (fun r : ℝ => f ((r : ℂ)⁻¹)) (Ici R) ∧
      ∀ r : ℝ, R ≤ r → ‖f ((r : ℂ)⁻¹)‖ ≤ C / r ^ N := by
  have hb := (isBigO_of_initial_coefficients_zero hf hp).comp_tendsto inverse_real_tendsto_zero
  obtain ⟨C, hC, hbC⟩ := hb.exists_pos
  have hc := inverse_real_tendsto_zero.eventually hf.analyticAt.eventually_continuousAt
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hbC.bound.and hc)
  refine ⟨C, hC, max 1 R, le_max_left _ _, ?_, ?_⟩
  · intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) ((le_max_left 1 R).trans hr)
    have hg : ContinuousAt (fun t : ℝ => (t : ℂ)⁻¹) r :=
      Complex.continuous_ofReal.continuousAt.inv₀ (by exact_mod_cast hr0.ne')
    have hh : ContinuousAt (fun t : ℝ => f ((t : ℂ)⁻¹)) r :=
      ContinuousAt.comp (f := fun t : ℝ => (t : ℂ)⁻¹) (x := r)
        (hR r ((le_max_right 1 R).trans hr)).2 hg
    exact hh.continuousWithinAt
  · intro r hr
    have hr0 : 0 ≤ r := le_trans (by norm_num) ((le_max_left 1 R).trans hr)
    have hh := (hR r ((le_max_right 1 R).trans hr)).1
    simpa only [Function.comp_apply, norm_pow, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0, inv_pow, div_eq_mul_inv] using hh

/-- Vanishing to order at least two implies genuine Bochner integrability on
a sufficiently late half-line, obtained by domination by an integrable power. -/
theorem exists_integrable_inverse_tail {f : ℂ → E}
    {p : FormalMultilinearSeries ℂ ℂ E} {N : ℕ}
    (hf : HasFPowerSeriesAt f p 0) (hp : ∀ k < N, p.coeff k = 0) (hN : 2 ≤ N) :
    ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (fun r : ℝ => f ((r : ℂ)⁻¹)) (Ici R) ∧
      IntegrableOn (fun r : ℝ => f ((r : ℂ)⁻¹)) (Ici R) := by
  obtain ⟨C, _, R, hR, hc, hb⟩ := exists_inverse_tail_bound hf hp
  refine ⟨R, hR, hc, Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi ?_⟩
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hmajor : IntegrableOn (fun r : ℝ => C * r ^ (-(N : ℝ))) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(N : ℝ) < -1)
      (lt_of_lt_of_le zero_lt_one hR)).const_mul C
  apply hmajor.mono' ((hc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  simpa only [Real.rpow_neg (le_of_lt (lt_of_lt_of_le zero_lt_one (hR.trans hr.le))),
    Real.rpow_natCast, div_eq_mul_inv] using hb r hr.le

/-- The late tail is truly integrable and has arbitrarily small integral norm. -/
theorem exists_small_integrable_inverse_tail {f : ℂ → E}
    {p : FormalMultilinearSeries ℂ ℂ E} {N : ℕ}
    (hf : HasFPowerSeriesAt f p 0) (hp : ∀ k < N, p.coeff k = 0) (hN : 2 ≤ N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (fun r : ℝ => f ((r : ℂ)⁻¹)) (Ici R) ∧
      IntegrableOn (fun r : ℝ => f ((r : ℂ)⁻¹)) (Ici R) ∧
      (∫ r in Ici R, ‖f ((r : ℂ)⁻¹)‖) < ε := by
  obtain ⟨a, ha, hc, hi⟩ := exists_integrable_inverse_tail hf hp hN
  obtain ⟨R, hR, hsmall⟩ := CRGProgress.exists_small_tail
    (fun r : ℝ => f ((r : ℂ)⁻¹)) a ε (hi.mono_set Ioi_subset_Ici_self) hε
  refine ⟨R, ha.trans hR, hc.mono (Ici_subset_Ici.mpr hR),
    hi.mono_set (Ici_subset_Ici.mpr hR), ?_⟩
  rwa [integral_Ici_eq_integral_Ioi]

end WasowAnalyticRemainder

#print axioms WasowAnalyticRemainder.partialSum_eq_zero
#print axioms WasowAnalyticRemainder.isBigO_of_initial_coefficients_zero
#print axioms WasowAnalyticRemainder.inverse_real_tendsto_zero
#print axioms WasowAnalyticRemainder.exists_inverse_tail_bound
#print axioms WasowAnalyticRemainder.exists_integrable_inverse_tail
#print axioms WasowAnalyticRemainder.exists_small_integrable_inverse_tail
