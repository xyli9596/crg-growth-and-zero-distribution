import LevinGeneral
import LevinIndicatorLower
import LevinIndicatorOrigin
import LevinIndicatorUpper

/-! Assembly of radial regularity and the unrestricted indicator identity.
The stronger C₀-disk criterion is proved in LevinC0.lean. -/
noncomputable section
open Set Filter Topology
open LevinGrowth
namespace LevinCriterion

/-- Origin reduction also preserves upper estimates uniform in direction. -/
theorem uniform_upper_bounds_restore_monomial {f F : ℂ → ℂ} {m : ℕ} {ρ : ℝ}
    {h : Direction → ℝ} (hρ : 0 < ρ)
    (hfactor : ∀ z : ℂ, f z = z ^ m * F z)
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in atTop, ∀ ζ : Direction,
      extendedNormalizedLog F ρ r ζ ≤ ((h ζ + ε : ℝ) : EReal)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in atTop, ∀ ζ : Direction,
      extendedNormalizedLog f ρ r ζ ≤ ((h ζ + ε : ℝ) : EReal) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have herr : ∀ᶠ r : ℝ in atTop, LevinOrigin.monomialError m ρ r < ε / 2 :=
    (tendsto_order.mp (LevinOrigin.monomialError_tendsto_zero m hρ)).2 (ε / 2) hε2
  filter_upwards [hupper (ε / 2) hε2, herr, eventually_gt_atTop (0 : ℝ)]
    with r hrupper hrerror hrpos ζ
  by_cases hfnz : f (rayPoint r ζ) = 0
  · simp only [extendedNormalizedLog, if_pos hfnz, bot_le]
  · have hFnz := (LevinOrigin.ray_nonzero_iff hfactor hrpos ζ).mp hfnz
    have hreal : normalizedLog F ρ r ζ ≤ h ζ + ε / 2 := by
      simpa only [extendedNormalizedLog, if_neg hFnz, EReal.coe_le_coe_iff] using hrupper ζ
    have heq := LevinOrigin.normalizedLog_factorization (ρ := ρ) hfactor hrpos ζ hFnz
    simp only [extendedNormalizedLog, if_neg hfnz, EReal.coe_le_coe_iff]
    linarith

#print axioms uniform_upper_bounds_restore_monomial

/-- The full-radius upper estimate holds uniformly in direction, including
functions with a zero at the origin. -/
theorem uniform_upper_bounds_of_radialRegular {f : ℂ → ℂ} {ρ : ℝ}
    {h : Direction → ℝ} (hf : Differentiable ℂ f) (hρ : 0 < ρ)
    (htype : FinitePositiveType f ρ) (hreg : RadialRegular f ρ h) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in atTop, ∀ ζ : Direction,
      extendedNormalizedLog f ρ r ζ ≤ ((h ζ + ε : ℝ) : EReal) := by
  obtain ⟨m, F, hF, hF0, hfactor, _, _, _⟩ :=
    LevinOrigin.exists_origin_reduction hf hρ htype
  have hFreg := LevinIndicatorOrigin.radialRegular_remove_monomial hρ hfactor hreg
  exact uniform_upper_bounds_restore_monomial hρ hfactor
    (LevinIndicatorUpper.uniform_upper_bounds hF hF0 hFreg)

/-- The radial regular limit equals the unrestricted, extended-real indicator.
No upper-bound or indicator-identification premise remains. -/
theorem isIndicator_of_radialRegular {f : ℂ → ℂ} {ρ : ℝ}
    {h : Direction → ℝ} (hf : Differentiable ℂ f) (hρ : 0 < ρ)
    (htype : FinitePositiveType f ρ) (hreg : RadialRegular f ρ h) :
    IsIndicator f ρ h := by
  apply LevinIndicatorLower.isIndicator_of_radialRegular_and_eventual_upper_bounds hreg
  intro ζ ε hε
  filter_upwards [uniform_upper_bounds_of_radialRegular hf hρ htype hreg ε hε] with r hr
  exact hr ζ

/-- Dense-ray regularity gives one common radial exception and the genuine
indicator, for arbitrary finite-positive-type entire functions at positive order. -/
theorem radialRegular_and_indicator_of_dense_rays {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hgood : Dense {ζ : Direction | ∃ a : ℝ, RayRegular f ρ ζ a}) :
    ∃ h : Direction → ℝ, RadialRegular f ρ h ∧ IsIndicator f ρ h := by
  obtain ⟨h, hreg⟩ := LevinGeneral.radialRegular_of_dense_rays hf hρ htype hgood
  exact ⟨h, hreg, isIndicator_of_radialRegular hf hρ htype hreg⟩

/-- The completed radial-and-indicator milestone, distinct from the stronger
manuscript goal requiring a C₀ disk exception. -/
def ConstantOrderRadialIndicatorLevinGoal : Prop :=
  ∀ (f : ℂ → ℂ) (ρ : ℝ), Differentiable ℂ f → 0 < ρ →
    FinitePositiveType f ρ →
    Dense {ζ : Direction | ∃ a : ℝ, RayRegular f ρ ζ a} →
    ∃ h : Direction → ℝ, RadialRegular f ρ h ∧ IsIndicator f ρ h

theorem constantOrderRadialIndicatorLevin : ConstantOrderRadialIndicatorLevinGoal := by
  intro f ρ hf hρ htype hgood
  exact radialRegular_and_indicator_of_dense_rays hf hρ htype hgood

#print axioms uniform_upper_bounds_of_radialRegular
#print axioms isIndicator_of_radialRegular
#print axioms radialRegular_and_indicator_of_dense_rays
#print axioms constantOrderRadialIndicatorLevin
end LevinCriterion
