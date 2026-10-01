import LevinOrigin

/-!
# Origin reduction for indicator upper estimates

Removing a fixed monomial preserves the same radial regular limit. Conversely,
the monomial's vanishing normalized logarithm preserves unrestricted eventual
upper bounds. Zeros keep their extended-real value minus infinity throughout.
-/

noncomputable section
open Set Filter Metric
open scoped Topology
open LevinGrowth LevinOrigin

namespace LevinIndicatorOrigin

/-- Removing a monomial preserves radial regularity with the same angular
limit and the same measurable zero-density exceptional set. -/
theorem radialRegular_remove_monomial {f F : ℂ → ℂ} {m : ℕ} {ρ : ℝ}
    {h : Direction → ℝ} (hρ : 0 < ρ)
    (hfactor : ∀ z : ℂ, f z = z ^ m * F z)
    (hreg : RadialRegular f ρ h) : RadialRegular F ρ h := by
  obtain ⟨hh, E, hEm, hEz, hlim⟩ := hreg
  refine ⟨hh, E, hEm, hEz, ?_⟩
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨R, hR, hRf⟩ := hlim (ε / 2) hε2
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp (monomialError_tendsto_zero m hρ)) (ε / 2) hε2)
  refine ⟨max R A, hR.trans_le (le_max_left _ _), ?_⟩
  intro r hr hrE ζ
  have hrR : R ≤ r := (le_max_left _ _).trans hr
  have hrA : A ≤ r := (le_max_right _ _).trans hr
  have hr0 : 0 < r := hR.trans_le hrR
  have hgood := hRf r hrR hrE ζ
  have hnz := (ray_nonzero_iff hfactor hr0 ζ).mp hgood.1
  have heq := normalizedLog_factorization (ρ := ρ) hfactor hr0 ζ hnz
  have herr : |monomialError m ρ r| < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero] using hA r hrA
  refine ⟨hnz, ?_⟩
  have hdiff : normalizedLog F ρ r ζ - h ζ =
      (normalizedLog f ρ r ζ - h ζ) - monomialError m ρ r := by linarith
  rw [hdiff]
  exact (abs_sub _ _).trans_lt (by linarith [hgood.2])

/-- Unrestricted extended-real upper estimates pass from the quotient back to
the original function. At zeros the conclusion is the bottom-element bound;
elsewhere the exact real logarithmic identity and its vanishing error apply. -/
theorem eventual_upper_bounds_restore_monomial {f F : ℂ → ℂ} {m : ℕ} {ρ : ℝ}
    {h : Direction → ℝ} (hρ : 0 < ρ)
    (hfactor : ∀ z : ℂ, f z = z ^ m * F z)
    (hupper : ∀ ζ : Direction, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r : ℝ in atTop, extendedNormalizedLog F ρ r ζ ≤ ((h ζ + ε : ℝ) : EReal)) :
    ∀ ζ : Direction, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r : ℝ in atTop, extendedNormalizedLog f ρ r ζ ≤ ((h ζ + ε : ℝ) : EReal) := by
  intro ζ ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have herr : ∀ᶠ r : ℝ in atTop, monomialError m ρ r < ε / 2 :=
    (tendsto_order.mp (monomialError_tendsto_zero m hρ)).2 (ε / 2) hε2
  filter_upwards [hupper ζ (ε / 2) hε2, herr, eventually_gt_atTop (0 : ℝ)]
    with r hrupper hrerror hrpos
  by_cases hfnz : f (rayPoint r ζ) = 0
  · simp only [extendedNormalizedLog, if_pos hfnz, bot_le]
  · have hFnz := (ray_nonzero_iff hfactor hrpos ζ).mp hfnz
    have hreal : normalizedLog F ρ r ζ ≤ h ζ + ε / 2 := by
      simpa only [extendedNormalizedLog, if_neg hFnz, EReal.coe_le_coe_iff] using hrupper
    have heq := normalizedLog_factorization (ρ := ρ) hfactor hrpos ζ hFnz
    simp only [extendedNormalizedLog, if_neg hfnz, EReal.coe_le_coe_iff]
    linarith

#print axioms radialRegular_remove_monomial
#print axioms eventual_upper_bounds_restore_monomial

end LevinIndicatorOrigin
