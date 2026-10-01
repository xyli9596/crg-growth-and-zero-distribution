import LevinRadial
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The lower indicator inequality from radial regularity

The limsup here uses all large radii, and zeros retain the value minus infinity.
The upper-bound-to-indicator theorem explicitly assumes the missing global
upper estimate; it does not assert that this estimate follows from radial
regularity alone.
-/

noncomputable section
open Set Filter MeasureTheory Topology
open LevinGrowth LevinDensity LevinAssembly

namespace LevinIndicatorLower

/-- Raywise regularity gives the extended-real limit outside its exceptional
set; eventual nonvanishing justifies passage from the real logarithm. -/
theorem rayRegular_extended_tendsto {f : ℂ → ℂ} {ρ : ℝ} {ζ : Direction} {a : ℝ}
    (hf : RayRegular f ρ ζ a) :
    ∃ E : Set ℝ, MeasurableSet E ∧ ZeroRadialDensity E ∧
      Tendsto (fun r => extendedNormalizedLog f ρ r ζ)
        (outsideFilter E) (𝓝 (a : EReal)) := by
  obtain ⟨E, hEm, hEz, hlim⟩ := hf
  have hreal : Tendsto (fun r => normalizedLog f ρ r ζ) (outsideFilter E) (𝓝 a) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨R, _, hR⟩ := hlim ε hε
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop R] with r hr hrE
    simpa only [Real.dist_eq] using (hR r hr hrE).2
  have heq : (fun r => extendedNormalizedLog f ρ r ζ) =ᶠ[outsideFilter E]
      (fun r => (normalizedLog f ρ r ζ : EReal)) := by
    obtain ⟨R, _, hR⟩ := hlim 1 (by norm_num)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop R] with r hr hrE
    simp only [extendedNormalizedLog, if_neg (hR r hr hrE).1]
  exact ⟨E, hEm, hEz, (EReal.tendsto_coe.2 hreal).congr' heq.symm⟩

/-- The unrestricted limsup dominates every finite radial regular limit. -/
theorem rayRegular_le_limsup {f : ℂ → ℂ} {ρ : ℝ} {ζ : Direction} {a : ℝ}
    (hf : RayRegular f ρ ζ a) :
    (a : EReal) ≤ Filter.limsup (fun r => extendedNormalizedLog f ρ r ζ) atTop := by
  obtain ⟨E, _, hEz, hlim⟩ := rayRegular_extended_tendsto hf
  let : (outsideFilter E).NeBot := outsideFilter_neBot hEz
  rw [← hlim.limsup_eq]
  exact limsup_le_limsup_of_le inf_le_left

/-- Lower indicator inequality for every direction of a radially regular
function. No holomorphy premise is needed for this purely limiting step. -/
theorem radialRegular_le_limsup {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : RadialRegular f ρ h) (ζ : Direction) :
    (h ζ : EReal) ≤ Filter.limsup (fun r => extendedNormalizedLog f ρ r ζ) atTop :=
  rayRegular_le_limsup (radialRegular_rayRegular hf ζ)

/-- An unrestricted eventual upper bound at every positive tolerance controls
the extended-real limsup, including functions which can take minus infinity. -/
theorem limsup_le_of_eventual_upper_bounds (u : ℝ → EReal) (a : ℝ)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in atTop, u r ≤ ((a + ε : ℝ) : EReal)) :
    Filter.limsup u atTop ≤ (a : EReal) := by
  have hlim : Tendsto (fun ε : ℝ => ((a + ε : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (a : EReal)) := by
    apply EReal.tendsto_coe.2
    simpa only [add_zero] using tendsto_const_nhds.add
      (show Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) from nhdsWithin_le_nhds)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact limsup_le_of_le (h := hu ε hε)

/-- Radial regularity plus the separate full-radius upper estimate identifies
the radial limit with the manuscript's unrestricted indicator. -/
theorem isIndicator_of_radialRegular_and_eventual_upper_bounds
    {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : RadialRegular f ρ h)
    (hupper : ∀ ζ : Direction, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r : ℝ in atTop, extendedNormalizedLog f ρ r ζ ≤ ((h ζ + ε : ℝ) : EReal)) :
    IsIndicator f ρ h := by
  intro ζ
  exact le_antisymm (limsup_le_of_eventual_upper_bounds _ _ (hupper ζ))
    (radialRegular_le_limsup hf ζ)

end LevinIndicatorLower

#print axioms LevinIndicatorLower.rayRegular_extended_tendsto
#print axioms LevinIndicatorLower.rayRegular_le_limsup
#print axioms LevinIndicatorLower.radialRegular_le_limsup
#print axioms LevinIndicatorLower.limsup_le_of_eventual_upper_bounds
#print axioms LevinIndicatorLower.isIndicator_of_radialRegular_and_eventual_upper_bounds
