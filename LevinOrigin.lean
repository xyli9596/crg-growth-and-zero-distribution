import LevinGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Removing the finite-order zero at the origin

The entire quotient is constructed from the actual local analytic zero order.
All logarithmic identities are restricted to positive radii and nonzero values.
The monomial contributes a normalized term tending to zero for positive order.
-/

noncomputable section
open Set Filter Metric
open scoped Topology
open LevinGrowth

namespace LevinOrigin

/-- A nonzero entire function has a global monomial factorization with a
zero-free value at the origin. The factor itself may have zeros elsewhere. -/
theorem exists_entire_factor_at_origin {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∃ z : ℂ, f z ≠ 0) :
    ∃ m : ℕ, ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 0 ≠ 0 ∧
      ∀ z : ℂ, f z = z ^ m * F z := by
  have ha : AnalyticOnNhd ℂ f univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hlocal : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0 := by
    intro hz
    have hall := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ (0 : ℂ)) hz
    obtain ⟨z, hnz⟩ := hn
    exact hnz (hall (mem_univ z))
  obtain ⟨m, g, hg, hg0, hfg⟩ :=
    (ha 0 (mem_univ _)).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hlocal
  let F : ℂ → ℂ := fun z => if z = 0 then g 0 else f z / z ^ m
  have hFg : g =ᶠ[𝓝 (0 : ℂ)] F := by
    filter_upwards [hfg] with z hz
    by_cases hz0 : z = 0
    · simp [F, hz0]
    · simp only [sub_zero, smul_eq_mul] at hz
      simp [F, hz0, hz, mul_div_cancel_left₀ _ (pow_ne_zero _ hz0)]
  have hFa : AnalyticOnNhd ℂ F univ := by
    intro z _
    by_cases hz0 : z = 0
    · subst z
      exact hg.congr hFg
    · apply ((ha z (mem_univ _)).div (analyticAt_id.pow m) (pow_ne_zero _ hz0)).congr
      filter_upwards [eventually_ne_nhds hz0] with w hw
      simp [F, hw]
  refine ⟨m, F, Complex.analyticOnNhd_univ_iff_differentiable.mp hFa, ?_, ?_⟩
  · simpa [F] using hg0
  · intro z
    by_cases hz0 : z = 0
    · subst z
      have hz := (show f =ᶠ[𝓝 (0 : ℂ)] (fun z => (z - 0) ^ m • g z) from hfg).eq_of_nhds
      simpa [F, smul_eq_mul] using hz
    · simp [F, hz0, mul_div_cancel₀ _ (pow_ne_zero m hz0)]

/-- The exact normalized contribution of the removed monomial. -/
def monomialError (m : ℕ) (ρ r : ℝ) : ℝ := (m : ℝ) * Real.log r / r ^ ρ

theorem monomialError_tendsto_zero (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (monomialError m ρ) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop hρ).tendsto_div_nhds_zero
  change Tendsto (fun r => (m : ℝ) * Real.log r / r ^ ρ) atTop (𝓝 0)
  simpa only [mul_div_assoc, mul_zero] using h.const_mul (m : ℝ)

/-- At positive radii, removing a monomial preserves nonvanishing exactly. -/
theorem ray_nonzero_iff {f F : ℂ → ℂ} {m : ℕ}
    (hfactor : ∀ z : ℂ, f z = z ^ m * F z) {r : ℝ} (hr : 0 < r) (ζ : Direction) :
    f (rayPoint r ζ) ≠ 0 ↔ F (rayPoint r ζ) ≠ 0 := by
  have hz : rayPoint r ζ ≠ 0 := norm_pos_iff.mp (by simpa [norm_rayPoint hr.le ζ] using hr)
  rw [hfactor, mul_ne_zero_iff]
  exact and_iff_right (pow_ne_zero m hz)

/-- The logarithmic identity uses an actual nonzero quotient value; it never
substitutes Lean's totalized logarithm at a zero. -/
theorem normalizedLog_factorization {f F : ℂ → ℂ} {m : ℕ}
    (hfactor : ∀ z : ℂ, f z = z ^ m * F z) {r ρ : ℝ} (hr : 0 < r) (ζ : Direction)
    (hnz : F (rayPoint r ζ) ≠ 0) :
    normalizedLog f ρ r ζ = normalizedLog F ρ r ζ + monomialError m ρ r := by
  unfold normalizedLog monomialError
  rw [hfactor, norm_mul, norm_pow, norm_rayPoint hr.le ζ,
    Real.log_mul (pow_pos hr m).ne' (norm_ne_zero_iff.mpr hnz), Real.log_pow]
  ring

/-- Dividing out a fixed monomial preserves finite nonzero type at positive
order. The positive lower type loses only a factor of two in its witness. -/
theorem finitePositiveType_remove_monomial {f F : ℂ → ℂ} {m : ℕ} {ρ : ℝ}
    (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hfactor : ∀ z : ℂ, f z = z ^ m * F z) : FinitePositiveType F ρ := by
  have hnorm (z : ℂ) : ‖f z‖ = ‖z‖ ^ m * ‖F z‖ := by rw [hfactor, norm_mul, norm_pow]
  constructor
  · obtain ⟨C, hC, R, hR, hb⟩ := htype.1
    refine ⟨C, hC, max R 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
    intro z hz
    have hz1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
    have hp : 1 ≤ ‖z‖ ^ m := one_le_pow₀ hz1
    apply le_trans _ (hb z ((le_max_left _ _).trans hz))
    rw [hnorm]
    exact le_mul_of_one_le_left (norm_nonneg _) hp
  · obtain ⟨c, hc, hlower⟩ := htype.2
    have hc2 : 0 < c / 2 := by positivity
    obtain ⟨A, hA⟩ := eventually_atTop.mp
      ((tendsto_order.mp (monomialError_tendsto_zero m hρ)).2 (c / 2) hc2)
    refine ⟨c / 2, hc2, ?_⟩
    intro R
    obtain ⟨z, hz, hlarge⟩ := hlower (max R A)
    have hzR : max R 1 ≤ ‖z‖ := max_le (le_trans (le_max_left R A) ((le_max_left _ _).trans hz))
      ((le_max_right _ _).trans hz)
    have hzA : A ≤ ‖z‖ := (le_max_right R A).trans ((le_max_left _ _).trans hz)
    have hz1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
    have hz0 : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz1
    have hpow : 0 < ‖z‖ ^ ρ := Real.rpow_pos_of_pos hz0 _
    have hpoly : ‖z‖ ^ m ≤ Real.exp ((c / 2) * ‖z‖ ^ ρ) := by
      have he := hA ‖z‖ hzA
      change (m : ℝ) * Real.log ‖z‖ / ‖z‖ ^ ρ < c / 2 at he
      have he' := (div_lt_iff₀ hpow).mp he
      rw [← Real.exp_log (pow_pos hz0 m), Real.log_pow]
      exact Real.exp_le_exp.mpr he'.le
    refine ⟨z, hzR, ?_⟩
    have hmul : Real.exp ((c / 2) * ‖z‖ ^ ρ) * Real.exp ((c / 2) * ‖z‖ ^ ρ) ≤
        Real.exp ((c / 2) * ‖z‖ ^ ρ) * ‖F z‖ := by
      calc
        _ = Real.exp (c * ‖z‖ ^ ρ) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ ‖f z‖ := hlarge
        _ = ‖z‖ ^ m * ‖F z‖ := hnorm z
        _ ≤ _ := mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
    nlinarith [Real.exp_pos ((c / 2) * ‖z‖ ^ ρ)]

/-- Raywise regularity passes to the quotient at the same exponent and limit. -/
theorem rayRegular_remove_monomial {f F : ℂ → ℂ} {m : ℕ} {ρ a : ℝ} {ζ : Direction}
    (hρ : 0 < ρ) (hfactor : ∀ z : ℂ, f z = z ^ m * F z)
    (hreg : RayRegular f ρ ζ a) : RayRegular F ρ ζ a := by
  obtain ⟨E, hEm, hEz, hlim⟩ := hreg
  refine ⟨E, hEm, hEz, ?_⟩
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨R, hR, hRf⟩ := hlim (ε / 2) hε2
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp (monomialError_tendsto_zero m hρ)) (ε / 2) hε2)
  refine ⟨max R A, hR.trans_le (le_max_left _ _), ?_⟩
  intro r hr hrE
  have hrR : R ≤ r := (le_max_left _ _).trans hr
  have hrA : A ≤ r := (le_max_right _ _).trans hr
  have hr0 : 0 < r := hR.trans_le hrR
  have hgood := hRf r hrR hrE
  have hnz := (ray_nonzero_iff hfactor hr0 ζ).mp hgood.1
  have heq := normalizedLog_factorization (ρ := ρ) hfactor hr0 ζ hnz
  have herr : |monomialError m ρ r| < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero] using hA r hrA
  refine ⟨hnz, ?_⟩
  have hdiff : normalizedLog F ρ r ζ - a =
      (normalizedLog f ρ r ζ - a) - monomialError m ρ r := by linarith
  rw [hdiff]
  exact (abs_sub _ _).trans_lt (by linarith [hgood.2])

/-- Multiplication by the removed monomial restores radial regularity without
changing the limiting angular function or the exceptional set. -/
theorem radialRegular_restore_monomial {f F : ℂ → ℂ} {m : ℕ} {ρ : ℝ}
    {h : Direction → ℝ} (hρ : 0 < ρ)
    (hfactor : ∀ z : ℂ, f z = z ^ m * F z)
    (hreg : RadialRegular F ρ h) : RadialRegular f ρ h := by
  obtain ⟨hh, E, hEm, hEz, hlim⟩ := hreg
  refine ⟨hh, E, hEm, hEz, ?_⟩
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨R, hR, hRF⟩ := hlim (ε / 2) hε2
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp (monomialError_tendsto_zero m hρ)) (ε / 2) hε2)
  refine ⟨max R A, hR.trans_le (le_max_left _ _), ?_⟩
  intro r hr hrE ζ
  have hrR : R ≤ r := (le_max_left _ _).trans hr
  have hrA : A ≤ r := (le_max_right _ _).trans hr
  have hr0 : 0 < r := hR.trans_le hrR
  have hgood := hRF r hrR hrE ζ
  have hnz := (ray_nonzero_iff hfactor hr0 ζ).mpr hgood.1
  have heq := normalizedLog_factorization (ρ := ρ) hfactor hr0 ζ hgood.1
  have herr : |monomialError m ρ r| < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero] using hA r hrA
  refine ⟨hnz, ?_⟩
  have hdiff : normalizedLog f ρ r ζ - h ζ =
      (normalizedLog F ρ r ζ - h ζ) + monomialError m ρ r := by linarith
  rw [hdiff]
  exact (abs_add_le _ _).trans_lt (by linarith [hgood.2])

/-- Complete origin reduction for the general positive-order radial criterion.
The quotient has the same finite positive type, inherits every good ray, and
any radial conclusion for it transfers back to the original function. -/
theorem exists_origin_reduction {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ) :
    ∃ m : ℕ, ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 0 ≠ 0 ∧
      (∀ z : ℂ, f z = z ^ m * F z) ∧ FinitePositiveType F ρ ∧
      (∀ ζ a, RayRegular f ρ ζ a → RayRegular F ρ ζ a) ∧
      (∀ h, RadialRegular F ρ h → RadialRegular f ρ h) := by
  obtain ⟨m, F, hF, hF0, hfactor⟩ := exists_entire_factor_at_origin hf
    (finitePositiveType_nontrivial htype)
  exact ⟨m, F, hF, hF0, hfactor, finitePositiveType_remove_monomial hρ htype hfactor,
    fun _ _ => rayRegular_remove_monomial hρ hfactor,
    fun _ => radialRegular_restore_monomial hρ hfactor⟩

#print axioms rayRegular_remove_monomial
#print axioms radialRegular_restore_monomial
#print axioms exists_origin_reduction
#print axioms finitePositiveType_remove_monomial
#print axioms exists_entire_factor_at_origin
#print axioms monomialError_tendsto_zero
#print axioms ray_nonzero_iff
#print axioms normalizedLog_factorization

end LevinOrigin
