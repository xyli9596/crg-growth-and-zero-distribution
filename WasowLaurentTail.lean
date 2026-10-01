import WasowLaurentRemainder

/-! Punctured-neighborhood estimates for genuine inverse-normalized Laurent
residuals give continuous, integrable, arbitrarily small tails on every fixed
unit ray. All estimates are derived from the finite truncation theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Filter Set Asymptotics MeasureTheory
namespace WasowLaurentTail
open WasowLaurentRemainder WasowLaurentInverse
variable {m : ℕ}

local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by
    simp_rw [Matrix.linfty_opNNNorm_def]
    fun_prop

theorem rawDefect_continuousAt (a h N : ℕ) (hh : 0 < h)
    {c : ℂ → Matrix (Fin m) (Fin m) ℂ} {z : ℂ}
    (hc : ContinuousAt c z) (hz : z ≠ 0)
    (P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) :
    ContinuousAt (WasowLaurentActualResidual.rawDefect a h N c P B) z := by
  have ht := (hasDerivAt_zpow (-((a+h : ℕ) : ℤ)) z (Or.inl hz)).continuousAt
  have hc' := WasowLaurentActualResidual.clearedDefect_continuousAt a h N hc P B
  apply (ht.smul hc').congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hz] with w hw
  exact WasowLaurentActualResidual.rawDefect_eq a h N hh c P B hw

theorem eventually_remainder_continuousAt (a b h N : ℕ) (hh : 0 < h)
    {c : ℂ → Matrix (Fin m) (Fin m) ℂ} (hc : AnalyticAt ℂ c 0)
    (P Q B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hPQ : P * Q = PowerSeries.X ^ (a+b)) (hN : a+b < N) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), ContinuousAt (remainder a h N c P B) z := by
  filter_upwards [eventually_inverse_continuousAt P Q a b N hPQ hN,
    hc.eventually_continuousAt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hi hz hzne
  exact hi.mul (rawDefect_continuousAt a h N hh hz hzne P B)

/-- Every nonzero fixed ray tends to the punctured origin under inversion. -/
theorem ray_tendsto_punctured {u : ℂ} (hu : u ≠ 0) :
    Tendsto (fun r : ℝ => u * (r : ℂ)⁻¹) atTop (𝓝[≠] (0 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [mul_zero] using
      tendsto_const_nhds.mul WasowAnalyticRemainder.inverse_real_tendsto_zero
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact mul_ne_zero hu (inv_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'))

section Tail
variable {E : Type*} [NormedAddCommGroup E]

theorem exists_ray_tail_bound {f : ℂ → E} {N : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (hf : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ContinuousAt f z)
    (hO : f =O[𝓝[≠] (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ N)) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (fun r : ℝ => f (u * (r : ℂ)⁻¹)) (Ici R) ∧
      ∀ r : ℝ, R ≤ r → ‖f (u * (r : ℂ)⁻¹)‖ ≤ C / r ^ N := by
  have hune : u ≠ 0 := by intro he; simp [he] at hu
  have ht := ray_tendsto_punctured hune
  obtain ⟨C, hC, hb⟩ := (hO.comp_tendsto ht).exists_pos
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hb.bound.and (ht.eventually hf))
  refine ⟨C, hC, max 1 R, le_max_left _ _, ?_, ?_⟩
  · intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) ((le_max_left 1 R).trans hr)
    have hg : ContinuousAt (fun t : ℝ => u * (t : ℂ)⁻¹) r :=
      continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.inv₀
        (by exact_mod_cast hrpos.ne'))
    have hh : ContinuousAt (fun t : ℝ => f (u * (t : ℂ)⁻¹)) r :=
      ContinuousAt.comp (f := fun t : ℝ => u * (t : ℂ)⁻¹) (x := r)
        (hR r ((le_max_right 1 R).trans hr)).2 hg
    exact hh.continuousWithinAt
  · intro r hr
    have hrnonneg : 0 ≤ r := zero_le_one.trans ((le_max_left 1 R).trans hr)
    have hb' := (hR r ((le_max_right 1 R).trans hr)).1
    simpa only [Function.comp_apply, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), norm_mul, hu, one_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hrnonneg, inv_pow, div_eq_mul_inv] using hb'

theorem exists_small_ray_tail {f : ℂ → E} {N : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (hf : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ContinuousAt f z)
    (hO : f =O[𝓝[≠] (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ N))
    (hN : 2 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (fun r : ℝ => f (u * (r : ℂ)⁻¹)) (Ici R) ∧
      IntegrableOn (fun r : ℝ => f (u * (r : ℂ)⁻¹)) (Ici R) ∧
      (∫ r in Ici R, ‖f (u * (r : ℂ)⁻¹)‖) < ε := by
  obtain ⟨C, _, a, ha, hc, hb⟩ := exists_ray_tail_bound hu hf hO
  have hi : IntegrableOn (fun r : ℝ => f (u * (r : ℂ)⁻¹)) (Ici a) := by
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
    (fun r : ℝ => f (u * (r : ℂ)⁻¹)) a ε (hi.mono_set Ioi_subset_Ici_self) hε
  refine ⟨R, ha.trans hR, hc.mono (Ici_subset_Ici.mpr hR),
    hi.mono_set (Ici_subset_Ici.mpr hR), ?_⟩
  rwa [integral_Ici_eq_integral_Ioi]
end Tail

/-- Full inverse-normalized analytic error, including every Laurent pole loss,
has arbitrarily small tails along any unit direction. -/
theorem remainder_small_ray_tail (a b h k : ℕ) (hh : 0 < h) (hk : 2 ≤ k)
    {c : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hc : HasFPowerSeriesAt c s 0)
    (A P Q B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n A)
    (hPQ : P * Q = PowerSeries.X ^ (a+b))
    (heq : WasowClearedResidual.Equation a h A P B)
    {u : ℂ} (hu : ‖u‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (fun r : ℝ => remainder a h (a+b+h+k) c P B (u*(r:ℂ)⁻¹)) (Ici R) ∧
      IntegrableOn (fun r : ℝ => remainder a h (a+b+h+k) c P B (u*(r:ℂ)⁻¹)) (Ici R) ∧
      (∫ r in Ici R, ‖remainder a h (a+b+h+k) c P B (u*(r:ℂ)⁻¹)‖) < ε := by
  exact exists_small_ray_tail hu
    (eventually_remainder_continuousAt a b h _ hh hc.analyticAt P Q B hPQ (by omega))
    (remainder_isBigO a b h k hh hc A P Q B hcoeff hPQ heq) hk hε

#print axioms rawDefect_continuousAt
#print axioms eventually_remainder_continuousAt
#print axioms ray_tendsto_punctured
#print axioms exists_ray_tail_bound
#print axioms exists_small_ray_tail
#print axioms remainder_small_ray_tail
end WasowLaurentTail
