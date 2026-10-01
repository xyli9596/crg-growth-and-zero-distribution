import CRGPuiseuxRayReduction

/-! Coefficient-sector data for Proposition 5.1. A sector provides actual
coefficients, a nonvanishing local multiplier, and fixed possibly divergent
formal series. Full closed-subsector expansions imply the ray expansions
used here; no solution, gauge or phase is a field of the source data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set Asymptotics
open scoped Topology
namespace CRGPuiseuxSector
open CRGPuiseuxRayReduction CRGPuiseuxCoordinates CRGPuiseuxScalarReduction
open CRGPuiseuxCompanionNormalForm CRGPuiseuxCompanionExpansion
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientRayTail
open WasowGlobalRayData WasowLaurentRayEquation WasowRamifiedGauge
variable {n : ℕ}

structure Sector (a : Fin (n+1) → ℂ → ℂ) where
  denominator : ℕ
  positive : 0<denominator
  clearing : ℕ
  angles : Set ℝ
  multiplier : ℂ → ℂ
  series : Fin (n+1) → PowerSeries ℂ
  some_nonzero : ∃j,series j≠0
  multiplier_continuous : ∀θ∈angles,∀ᶠx in rayFilter (direction (θ/denominator)),
    ContinuousAt multiplier x
  multiplier_nonzero : ∀θ∈angles,∀ᶠx in rayFilter (direction (θ/denominator)),
    multiplier x≠0
  expansion : ∀θ∈angles,∀j,CompleteExpansion (rayFilter (direction (θ/denominator)))
    (clearedCoefficients a denominator clearing multiplier j) (series j)

def Sector.coefficients {a : Fin (n+1) → ℂ → ℂ} (S : Sector a) :=
  clearedCoefficients a S.denominator S.clearing S.multiplier

def Sector.highest {a : Fin (n+1) → ℂ → ℂ} (S : Sector a) : Highest S.series :=
  Classical.choice (exists_highest S.series S.some_nonzero)

/-- The normal-form construction is chosen before any direction or solution. -/
def Sector.formal {a : Fin (n+1) → ℂ → ℂ} (S : Sector a) :
    FormalData S.highest S.denominator := Classical.choice
  (WasowGlobalFormalSquare.exists_square_global_realization
    (normalizedSeries S.highest S.denominator)
    (S.denominator+(S.series S.highest.index).order.toNat-1))

theorem clearedCoefficients_continuousAt
    {a : Fin (n+1) → ℂ → ℂ} (ha : ∀j,Differentiable ℂ (a j))
    (p h : ℕ) {W : ℂ → ℂ} {x : ℂ} (hx : x≠0)
    (hW : ContinuousAt W x) (hne : W x≠0) (j : Fin (n+1)) :
    ContinuousAt (clearedCoefficients a p h W j) x := by
  have hp : ContinuousAt (originalPoint p) x :=
    continuousAt_id.zpow₀ (-(p:ℤ)) (Or.inl hx)
  exact ((continuousAt_id.pow h).mul ((ha j).continuous.continuousAt.comp hp)).div hW hne

theorem Sector.coefficients_continuous {a : Fin (n+1) → ℂ → ℂ}
    (S : Sector a) (ha : ∀j,Differentiable ℂ (a j)) (θ : ℝ) (hθ : θ∈S.angles) :
    ∀j,∀ᶠx in rayFilter (direction (θ/S.denominator)),ContinuousAt (S.coefficients j) x := by
  intro j
  have hne : ∀ᶠx : ℂ in 𝓝[≠] (0:ℂ),x≠0 := self_mem_nhdsWithin
  have hx : ∀ᶠx in rayFilter (direction (θ/S.denominator)),x≠0 :=
    hne.filter_mono (rayFilter_le_punctured (direction_ne_zero _))
  filter_upwards [hx,S.multiplier_continuous θ hθ,S.multiplier_nonzero θ hθ] with x hx hW hne
  exact clearedCoefficients_continuousAt ha _ _ hx hW hne j

theorem Sector.localOnRay_tendsto {a : Fin (n+1) → ℂ → ℂ}
    (S : Sector a) (θ : ℝ) :
    Tendsto (localOnRay S.highest S.denominator S.formal θ) atTop
      (rayFilter (direction (θ/S.denominator))) := by
  have hD : 0<CRGPuiseuxCompanionNormalForm.denominator S.highest S.denominator S.formal :=
    Nat.mul_pos S.formal.positive S.positive
  have ht : Tendsto (rootRadius (CRGPuiseuxCompanionNormalForm.denominator S.highest S.denominator S.formal)) atTop atTop :=
    tendsto_rpow_atTop (one_div_pos.mpr (by exact_mod_cast hD))
  change Tendsto (fun r : ℝ=>
    inverseRay (direction (θ/(CRGPuiseuxCompanionNormalForm.denominator S.highest S.denominator S.formal)))
      (rootRadius (CRGPuiseuxCompanionNormalForm.denominator S.highest S.denominator S.formal) r)^S.formal.denominator)
    atTop (rayFilter (direction (θ/S.denominator)))
  simpa only [CRGPuiseuxCompanionNormalForm.denominator,Nat.cast_mul,Function.comp_def] using
    (lifted_tendsto_local_ray S.formal.denominator S.denominator S.formal.positive
      S.positive θ).comp ht

/-- Each coefficient packet constructs its actual physical-ray gauge,
using the same fixed finite fractional polynomial family on every ray. -/
theorem Sector.physical_ray_gauge {a : Fin (n+1) → ℂ → ℂ}
    (S : Sector a) (ha : ∀j,Differentiable ℂ (a j)) (θ : ℝ) (hθ : θ∈S.angles) :
    Nonempty (CRGGeneralRayGauge.RayGaugeWitness
      (physicalCoefficient S.coefficients S.highest S.denominator S.formal θ)
      (fun i=>CRGNormalFormGoal.phaseOnRay (CRGPuiseuxCompanionNormalForm.denominator S.highest S.denominator S.formal)
        (S.formal.normal.phase i) θ ⟨0,Nat.mul_pos S.formal.positive S.positive⟩)) := by
  exact physical_ray_normal_form (rayFilter_le_punctured (direction_ne_zero _))
    (S.expansion θ hθ) S.highest S.denominator S.positive
    (S.coefficients_continuous ha θ hθ) S.formal θ
    (by simpa only [CRGPuiseuxCompanionNormalForm.denominator,Nat.cast_mul] using
      lifted_tendsto_local_ray S.formal.denominator S.denominator S.formal.positive S.positive θ)

#print axioms clearedCoefficients_continuousAt
#print axioms Sector.coefficients_continuous
#print axioms Sector.localOnRay_tendsto
#print axioms Sector.physical_ray_gauge
end CRGPuiseuxSector
