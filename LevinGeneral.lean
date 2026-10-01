import LevinRadial
import LevinAnnulus
import LevinExceptional
import LevinOrigin

/-!
The constant positive-order dense-ray criterion with a common radial exception.
All analytic and measure estimates are discharged here. Functions may have zeros,
including at the origin. The C₀-disk conclusion is proved separately in LevinC0.lean.
-/
noncomputable section
open Set Filter MeasureTheory Topology
open LevinGrowth LevinDensity LevinAssembly
namespace LevinGeneral

/-- Entire-function hypotheses imply the genuine small-density angular estimate.
The temporary center condition is removed by the final origin reduction. -/
theorem small_density_equicontinuity_of_ne_zero_at_origin {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ)
    (htype : FinitePositiveType f ρ) (hf0 : f 0 ≠ 0) :
    ∀ η : ℝ, 0 < η → ∃ E : Set ℝ, MeasurableSet E ∧
      LevinSmallDensity.EventuallyDensityLE E η ∧
      LevinCompact.AsymptoticUniformEquicontinuous (normalizedLog f ρ) (outsideFilter E) := by
  obtain ⟨C, _, hP⟩ := LevinAnnulus.exists_annular_majorant hf hρ htype hf0
  let cost : ℝ → ℝ := fun δ => C * LevinAnnulus.modulus δ
  have hc : Tendsto cost (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using
      (LevinAnnulus.modulus_tendsto_zero.const_mul C).mono_left nhdsWithin_le_nhds
  have hcontrol : LevinExceptional.AnnularMajorants (normalizedLog f ρ) (zeroRadii f) cost := by
    intro n δ hδ hδ1
    obtain ⟨P, hPm, hPi, hPpos, hPint, hangle⟩ :=
      hP ((2 : ℝ) ^ n) (one_le_pow₀ (by norm_num)) δ hδ hδ1
    refine ⟨P, hPm, hPi, hPpos, ?_, ?_⟩
    · simpa only [cost, mul_assoc, mul_comm C] using hPint
    · intro r hr hrZ v w hvw
      simpa only [Real.dist_eq] using hangle r hr hrZ v w hvw
  exact LevinExceptional.exists_small_density_equicontinuity
    (normalizedLog f ρ) (zeroRadii f) (zeroRadii_countable hf ⟨0, hf0⟩).measurableSet
    (zeroRadii_zero_density hf ⟨0, hf0⟩) cost hc hcontrol

/-- General zeros away from the origin are allowed; no equicontinuity hypothesis
remains in this theorem. -/
theorem radialRegular_of_dense_sequence_of_ne_zero_at_origin {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ)
    (htype : FinitePositiveType f ρ) (hf0 : f 0 ≠ 0)
    (d : ℕ → Direction) (hd : DenseRange d)
    (hgood : ∀ n, ∃ a : ℝ, RayRegular f ρ (d n) a) :
    ∃ h : Direction → ℝ, RadialRegular f ρ h := by
  exact LevinRadial.radialRegular_of_dense_sequence_and_small_density hf ⟨0, hf0⟩ d hd hgood
    (small_density_equicontinuity_of_ne_zero_at_origin hf hρ htype hf0)

/-- The radial dense-ray criterion for arbitrary entire functions of finite
positive type and positive constant order. This includes zeros at the origin. -/
theorem radialRegular_of_dense_rays {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hgood : Dense {ζ : Direction | ∃ a : ℝ, RayRegular f ρ ζ a}) :
    ∃ h : Direction → ℝ, RadialRegular f ρ h := by
  obtain ⟨m, F, hF, hF0, _, hFtype, hray, hrestore⟩ :=
    LevinOrigin.exists_origin_reduction hf hρ htype
  obtain ⟨d, hd, hmem⟩ := LevinZeroFree.exists_dense_sequence_in hgood
  have hgoodF : ∀ n, ∃ a : ℝ, RayRegular F ρ (d n) a := by
    intro n
    obtain ⟨a, ha⟩ := hmem n
    exact ⟨a, hray (d n) a ha⟩
  obtain ⟨h, hh⟩ := radialRegular_of_dense_sequence_of_ne_zero_at_origin
    hF hρ hFtype hF0 d hd hgoodF
  exact ⟨h, hrestore h hh⟩

/-- A named proposition for the completed radial milestone. It intentionally
does not replace the manuscript's stronger C₀-and-indicator goal. -/
def ConstantOrderRadialLevinGoal : Prop :=
  ∀ (f : ℂ → ℂ) (ρ : ℝ), Differentiable ℂ f → 0 < ρ →
    FinitePositiveType f ρ →
    Dense {ζ : Direction | ∃ a : ℝ, RayRegular f ρ ζ a} →
    ∃ h : Direction → ℝ, RadialRegular f ρ h

theorem constantOrderRadialLevin : ConstantOrderRadialLevinGoal := by
  intro f ρ hf hρ htype hgood
  exact radialRegular_of_dense_rays hf hρ htype hgood

#print axioms small_density_equicontinuity_of_ne_zero_at_origin
#print axioms radialRegular_of_dense_sequence_of_ne_zero_at_origin
#print axioms radialRegular_of_dense_rays
#print axioms constantOrderRadialLevin
end LevinGeneral
