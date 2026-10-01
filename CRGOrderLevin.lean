import CRGOrderRay

/-! Bridge from the actual finite ray limits to the already proved full C₀
Levin criterion, including the unrestricted indicator conclusion. -/
noncomputable section
open Set Filter Complex
open scoped Topology
namespace CRGOrderLevin
open CRGOrderRay

def angleDirection (θ : ℝ) : LevinGrowth.Direction :=
  ⟨Complex.exp ((θ : ℂ) * Complex.I), by simp [Complex.norm_exp]⟩

theorem continuous_angleDirection : Continuous angleDirection := by
  apply Continuous.subtype_mk
  fun_prop

theorem surjective_angleDirection : Function.Surjective angleDirection := by
  intro ζ
  refine ⟨ζ.val.arg, Subtype.ext ?_⟩
  have hh := Complex.norm_mul_exp_arg_mul_I ζ.val
  simpa only [angleDirection, ζ.property, Complex.ofReal_one, one_mul] using hh

theorem rayRegular_of_limit {f : ℂ → ℂ} {θ ρ L : ℝ}
    (hn : ∀ᶠ r : ℝ in atTop, f (CRGPhragmenRay.point θ r) ≠ 0)
    (hl : Tendsto (fun r : ℝ => logValue f θ r / r ^ ρ) atTop (𝓝 L)) :
    LevinGrowth.RayRegular f ρ (angleDirection θ) L := by
  refine ⟨∅, MeasurableSet.empty, (LevinDensity.zeroRadialDensity_Iic 0).mono (empty_subset _), ?_⟩
  intro ε hε
  have he := hl.eventually (Metric.ball_mem_nhds L hε)
  obtain ⟨R, hR⟩ := eventually_atTop.1 (hn.and he)
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun r hr _ => ?_⟩
  obtain ⟨hnr, her⟩ := hR r ((le_max_left _ _).trans hr)
  refine ⟨hnr, ?_⟩
  simpa only [Metric.mem_ball, Real.dist_eq, LevinGrowth.normalizedLog,
    LevinGrowth.rayPoint, angleDirection, logValue, CRGPhragmenRay.point] using her

/-- Dense finite normalized limits imply the full disk and indicator CRG
conclusion through the proved Levin theorem. -/
theorem manuscriptCRG_of_rayData {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : LevinGrowth.FinitePositiveType f ρ)
    (degree leading : ℝ → ℝ) {D : Set ℝ} (hD : Dense D)
    (hdata : ∀ θ ∈ D, RayData f θ (degree θ) (leading θ))
    (hdegree : ∀ θ ∈ D, degree θ ≤ ρ) : LevinGrowth.ManuscriptCRG f ρ := by
  apply LevinC0.constantOrderLevin f ρ hf hρ htype
  apply surjective_angleDirection.denseRange.dense_of_mapsTo continuous_angleDirection hD
  intro θ hθ
  obtain ⟨L, hL⟩ := normalized_limit (hdata θ hθ) hρ (hdegree θ hθ)
  exact ⟨L, rayRegular_of_limit (hdata θ hθ).nonzero hL⟩

/-- Nondegenerate leading degree is bounded by any two-sided logarithmic order. -/
theorem degree_le_of_two_sided {f : ℂ → ℂ} {θ d a ρ : ℝ}
    (h : RayData f θ d a) (hρ : 0 ≤ ρ)
    (hbound : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ,
      ∀ᶠ r : ℝ in atTop, |logValue f θ r| ≤ C * r ^ (ρ + δ)) : d ≤ ρ := by
  by_cases hd0 : d = 0
  · simpa only [hd0] using hρ
  have hd : 0 < d := lt_of_le_of_ne h.degree_nonneg (Ne.symm hd0)
  apply CRGRay.phase_degree_le_order _ (h.positive hd).2 (h.positive hd).1
  intro s hs
  obtain ⟨C, hC⟩ := hbound (s - ρ) (sub_pos.mpr hs)
  exact ⟨C, by simpa only [show ρ + (s - ρ) = s by ring] using hC⟩

/-- The manuscript's two-sided logarithmic bound discharges the only degree
comparison needed by the Levin bridge. -/
theorem manuscriptCRG_of_two_sided {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : LevinGrowth.FinitePositiveType f ρ)
    (degree leading : ℝ → ℝ) {D : Set ℝ} (hD : Dense D)
    (hdata : ∀ θ ∈ D, RayData f θ (degree θ) (leading θ))
    (hbound : ∀ θ ∈ D, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ,
      ∀ᶠ r : ℝ in atTop, |logValue f θ r| ≤ C * r ^ (ρ + δ)) :
    LevinGrowth.ManuscriptCRG f ρ := by
  exact manuscriptCRG_of_rayData hf hρ htype degree leading hD hdata
    (fun θ hθ => degree_le_of_two_sided (hdata θ hθ) hρ.le (hbound θ hθ))

#print axioms continuous_angleDirection
#print axioms surjective_angleDirection
#print axioms rayRegular_of_limit
#print axioms manuscriptCRG_of_rayData
#print axioms degree_le_of_two_sided
#print axioms manuscriptCRG_of_two_sided
end CRGOrderLevin
