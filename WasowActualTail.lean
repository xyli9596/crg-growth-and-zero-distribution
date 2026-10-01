import WasowActualTruncation

/-! Genuine inverse-variable `L¹` tails for the actual finite gauge defect.
The bounds follow from the proved analytic truncation estimate. No separate
Taylor expansion or assumed integrability of the residual is required.
These are estimates for the raw defect; rank weights and inverse-gauge factors
must be tracked before identifying a fully transformed system remainder. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology Matrix.Norms.Operator
open Filter Asymptotics Set MeasureTheory
namespace WasowActualTail
open WasowMatrixPolynomial WasowActualTruncation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- The matrix operator norm is continuous for the actual product topology.
-- Making this instance explicit resolves the topology/norm instance diamond
-- when `IntegrableOn` is elaborated for matrix-valued functions.
local instance : ContinuousENorm (Matrix ι ι ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by
    simp_rw [Matrix.linfty_opNNNorm_def]
    fun_prop

/-- Actual finite residuals are continuous wherever the coefficient function
is continuous; the differentiated gauge is itself a finite polynomial. -/
theorem actualDefect_continuousAt {a : ℂ → Matrix ι ι ℂ} {z : ℂ}
    (ha : ContinuousAt a z) (P B : PowerSeries (Matrix ι ι ℂ)) (q N : ℕ) :
    ContinuousAt (actualDefect a P B q N) z := by
  have hd : deriv (eval (PowerSeries.trunc N P)) =
      eval (PowerSeries.trunc N P).derivative := by
    funext w
    exact (hasDerivAt_eval _ w).deriv
  unfold actualDefect
  rw [hd]
  exact ((ha.mul (continuous_eval _).continuousAt).sub
    ((continuous_eval _).continuousAt.mul (continuous_eval _).continuousAt)).add
      ((continuousAt_id.pow _).smul (continuous_eval _).continuousAt)

section Tail
variable {E : Type*} [NormedAddCommGroup E]

/-- A local `O(|z|^N)` estimate and actual continuity near zero yield a common
real inverse-variable tail with continuity and pointwise polynomial decay. -/
theorem exists_inverse_tail_bound_of_isBigO {f : ℂ → E} {N : ℕ}
    (hf : ∀ᶠ z in 𝓝 (0 : ℂ), ContinuousAt f z)
    (hO : f =O[𝓝 (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ N)) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (fun r : ℝ => f ((r : ℂ)⁻¹)) (Ici R) ∧
      ∀ r : ℝ, R ≤ r → ‖f ((r : ℂ)⁻¹)‖ ≤ C / r ^ N := by
  have ht := WasowAnalyticRemainder.inverse_real_tendsto_zero
  obtain ⟨C, hC, hb⟩ := (hO.comp_tendsto ht).exists_pos
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hb.bound.and (ht.eventually hf))
  refine ⟨C, hC, max 1 R, le_max_left _ _, ?_, ?_⟩
  · intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) ((le_max_left 1 R).trans hr)
    have hg : ContinuousAt (fun t : ℝ => (t : ℂ)⁻¹) r :=
      Complex.continuous_ofReal.continuousAt.inv₀ (by exact_mod_cast hrpos.ne')
    have hh : ContinuousAt (fun t : ℝ => f ((t : ℂ)⁻¹)) r :=
      ContinuousAt.comp (f := fun t : ℝ => (t : ℂ)⁻¹) (x := r)
        (hR r ((le_max_right 1 R).trans hr)).2 hg
    exact hh.continuousWithinAt
  · intro r hr
    have hrnonneg : 0 ≤ r := le_trans (by norm_num) ((le_max_left 1 R).trans hr)
    have hh := (hR r ((le_max_right 1 R).trans hr)).1
    simpa only [Function.comp_apply, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hrnonneg, inv_pow, div_eq_mul_inv] using hh

/-- The inverse-variable remainder has a genuine arbitrarily small `L¹` tail;
its integrability is proved by domination, rather than assumed. -/
theorem exists_small_inverse_tail_of_isBigO {f : ℂ → E} {N : ℕ}
    (hf : ∀ᶠ z in 𝓝 (0 : ℂ), ContinuousAt f z)
    (hO : f =O[𝓝 (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ N))
    (hN : 2 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (fun r : ℝ => f ((r : ℂ)⁻¹)) (Ici R) ∧
      IntegrableOn (fun r : ℝ => f ((r : ℂ)⁻¹)) (Ici R) ∧
      (∫ r in Ici R, ‖f ((r : ℂ)⁻¹)‖) < ε := by
  obtain ⟨C, _, a, ha, hc, hb⟩ := exists_inverse_tail_bound_of_isBigO hf hO
  have hi : IntegrableOn (fun r : ℝ => f ((r : ℂ)⁻¹)) (Ici a) := by
    refine Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi ?_
    have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hmajor : IntegrableOn (fun r : ℝ => C * r ^ (-(N : ℝ))) (Ioi a) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : -(N : ℝ) < -1)
        (lt_of_lt_of_le zero_lt_one ha)).const_mul C
    apply hmajor.mono' ((hc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [Real.rpow_neg (le_of_lt (lt_of_lt_of_le zero_lt_one (ha.trans hr.le))),
      Real.rpow_natCast, div_eq_mul_inv] using hb r hr.le
  obtain ⟨R, hR, hsmall⟩ := CRGProgress.exists_small_tail
    (fun r : ℝ => f ((r : ℂ)⁻¹)) a ε (hi.mono_set Ioi_subset_Ici_self) hε
  refine ⟨R, ha.trans hR, hc.mono (Ici_subset_Ici.mpr hR),
    hi.mono_set (Ici_subset_Ici.mpr hR), ?_⟩
  rwa [integral_Ici_eq_integral_Ioi]

end Tail

/-- The actual residual of the finite formal gauge, with no residual-series
hypothesis, has a continuous and arbitrarily small integrable ray tail. This
is the raw gauge defect; inverse gauge factors and rank weights must still be
accounted for before identifying a transformed differential-equation error. -/
theorem actualDefect_small_inverse_tail
    {a : ℂ → Matrix ι ι ℂ} {p : FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ)}
    (ha : HasFPowerSeriesAt a p 0) (A P B : PowerSeries (Matrix ι ι ℂ))
    (hc : ∀ n, p.coeff n = PowerSeries.coeff n A) (q N : ℕ)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P))
    (hN : 2 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (fun r : ℝ => actualDefect a P B q N ((r : ℂ)⁻¹)) (Ici R) ∧
      IntegrableOn (fun r : ℝ => actualDefect a P B q N ((r : ℂ)⁻¹)) (Ici R) ∧
      (∫ r in Ici R, ‖actualDefect a P B q N ((r : ℂ)⁻¹)‖) < ε := by
  apply exists_small_inverse_tail_of_isBigO
    (ha.analyticAt.eventually_continuousAt.mono (fun z hz => actualDefect_continuousAt hz P B q N))
    (actualDefect_isBigO ha A P B hc q N heq) hN hε

end WasowActualTail

#print axioms WasowActualTail.actualDefect_continuousAt
#print axioms WasowActualTail.exists_inverse_tail_bound_of_isBigO
#print axioms WasowActualTail.exists_small_inverse_tail_of_isBigO
#print axioms WasowActualTail.actualDefect_small_inverse_tail
