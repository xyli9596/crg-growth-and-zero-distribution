import CRGPuiseuxCompanionExpansion
import CRGGeneralRayRamification

/-! True ramification descent for the actual nonrational companion. The
fractional-power denominator combines the original coefficient Puiseux
ramification with the automatically chosen formal reduction ramification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Filter
namespace CRGPuiseuxCompanionNormalForm
open CRGPuiseuxScalarReduction CRGPuiseuxCompanionExpansion
open CRGNormalFormGoal WasowGlobalFormalSquare WasowLaurentGauge
open WasowGlobalFiniteRealization WasowLaurentRayEquation WasowRamifiedGauge
variable {n : ℕ} {A : Fin (n+1) → PowerSeries ℂ}

abbrev FormalData (H : Highest A) (p : ℕ) := SquareRealization
  (differentialCoefficient (p+(A H.index).order.toNat-1) (normalizedSeries H p))

def denominator (H : Highest A) (p : ℕ) (W : FormalData H p) := W.denominator*p

def localOnRay (H : Highest A) (p : ℕ) (W : FormalData H p) (θ r : ℝ) : ℂ :=
  (inverseRay (WasowGlobalRayData.direction (θ/denominator H p W))
    (rootRadius (denominator H p W) r))^W.denominator

/-- The actual companion coefficient on the original physical ray. -/
def physicalCoefficient (C : Fin (n+1) → ℂ → ℂ) (H : Highest A) (p : ℕ)
    (W : FormalData H p) (θ r : ℝ) : Matrix (Fin H.index.val) (Fin H.index.val) ℂ :=
  Complex.exp ((θ:ℂ)*Complex.I) • companion C H (localOnRay H p W θ r)

/-- Clearing the companion pole cancels exactly the same powers in the true
ramified differential coefficient, retaining the initial p Jacobian. -/
theorem ramifiedCoefficient_companion (C : Fin (n+1) → ℂ → ℂ) (H : Highest A)
    (P p : ℕ) (hp : 0<p) {z : ℂ} (hz : z≠0) :
    ramifiedCoefficient P (p+(A H.index).order.toNat-1) (normalizedSource C H p) z =
      (-(P*p:ℂ)*z^(-((P*p:ℤ)+1))) • companion C H (z^P) := by
  let b := (A H.index).order.toNat
  have hq : 1≤p+b := by omega
  unfold ramifiedCoefficient normalizedSource
  rw [clearedCompanion_eq,smul_smul,smul_smul]
  congr 1
  change (-(P:ℂ)*z^(-(WasowRamifiedCoefficient.pole P (p+b-1):ℤ)))*(p:ℂ)*(z^P)^b=_
  rw [←pow_mul,← zpow_natCast]
  calc
    _ = -(P*p:ℂ)*(z^(-(WasowRamifiedCoefficient.pole P (p+b-1):ℤ))*z^((P*b:ℕ):ℤ)) := by
      push_cast
      ring
    _ = _ := by
      rw [←zpow_add₀ hz]
      congr 2
      simp only [WasowRamifiedCoefficient.pole,Nat.cast_add,Nat.cast_mul,Nat.cast_one,
        Nat.sub_add_cancel hq]
      ring

/-- The exact reciprocal power-chain factor identifies the source of the
lifted normal form with the original actual physical companion. -/
theorem physicalCoefficient_pullback (C : Fin (n+1) → ℂ → ℂ) (H : Highest A)
    (p : ℕ) (hp : 0<p) (W : FormalData H p) (θ : ℝ) {r : ℝ} (hr : 0<r) :
    (rootRadiusDerivative (denominator H p W) r : ℂ) •
      CRGPuiseuxRayData.liftedCoefficient (normalizedSource C H p) W
        (θ/denominator H p W) (rootRadius (denominator H p W) r) =
      physicalCoefficient C H p W θ r := by
  let D := denominator H p W
  have hD : 0<D := Nat.mul_pos W.positive hp
  have hs : rootRadius D r≠0 := (rootRadius_pos D hr).ne'
  have hz := WasowGlobalRayData.inverseRay_ne_zero (θ/D) hs
  unfold CRGPuiseuxRayData.liftedCoefficient WasowLaurentRayEquation.coefficientOnRay
  rw [ramifiedCoefficient_companion C H W.denominator p hp hz]
  simp only [smul_smul]
  unfold physicalCoefficient localOnRay
  congr 1
  change (rootRadiusDerivative D r:ℂ)*(chainFactor (WasowGlobalRayData.direction (θ/D)) (rootRadius D r)*
    (-(W.denominator*p:ℂ)*(inverseRay (WasowGlobalRayData.direction (θ/D)) (rootRadius D r))^
      (-((W.denominator*p:ℤ)+1)))) = Complex.exp ((θ:ℂ)*Complex.I)
  have hexp : -((W.denominator*p:ℤ)+1)=-(D:ℤ)-1 := by dsimp [D,denominator];ring
  rw [hexp,←Nat.cast_mul]
  change (rootRadiusDerivative D r:ℂ)*(chainFactor (WasowGlobalRayData.direction (θ/D)) (rootRadius D r)*
    (-(D:ℂ)*inverseRay (WasowGlobalRayData.direction (θ/D)) (rootRadius D r)^(-(D:ℤ)-1))) = _
  rw [WasowGlobalRayData.source_chain_factor D hD (θ/D) hs,ray_chain_factor D hD θ hr]

/-- A genuine exact physical-ray gauge with the fixed combined Puiseux
phases is constructed solely from the complete coefficient expansions. -/
theorem physical_ray_normal_form
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0:ℂ))
    {C : Fin (n+1) → ℂ → ℂ}
    (hC : ∀j,CRGAsymptoticCoefficientQuotient.CompleteExpansion l (C j) (A j))
    (H : Highest A) (p : ℕ) (hp : 0<p)
    (hcont : ∀j,∀ᶠ z in l,ContinuousAt (C j) z) (W : FormalData H p) (θ : ℝ)
    (ht : Tendsto (fun s : ℝ =>
      (inverseRay (WasowGlobalRayData.direction (θ/denominator H p W)) s)^W.denominator) atTop l) :
    Nonempty (CRGGeneralRayGauge.RayGaugeWitness (physicalCoefficient C H p W θ)
      (fun i => phaseOnRay (denominator H p W) (W.normal.phase i) θ
        ⟨0,Nat.mul_pos W.positive hp⟩)) := by
  obtain ⟨K⟩ := CRGPuiseuxNormalForm.lifted_ray_normal_form
    (normalizedSource_completeExpansion hl hC H p)
    (normalizedSource_eventually_continuousAt hl hC H p hcont)
    (p+(A H.index).order.toNat-1) W (θ/denominator H p W) ht
  exact CRGGeneralRayRamification.descend_rayGauge (denominator H p W)
    (Nat.mul_pos W.positive hp) (physicalCoefficient C H p W θ)
    (CRGPuiseuxRayData.liftedCoefficient (normalizedSource C H p) W (θ/denominator H p W))
    W.normal.phase θ 0 (fun r hr => physicalCoefficient_pullback C H p hp W θ hr) K

/-- The fixed finite family is chosen without consulting the solution or
ray; only compatibility with the original coefficient sector restricts rays. -/
theorem exists_fixed_physical_phase_normal_form
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0:ℂ))
    {C : Fin (n+1) → ℂ → ℂ}
    (hC : ∀j,CRGAsymptoticCoefficientQuotient.CompleteExpansion l (C j) (A j))
    (H : Highest A) (p : ℕ) (hp : 0<p)
    (hcont : ∀j,∀ᶠ z in l,ContinuousAt (C j) z) :
    ∃ W : FormalData H p,
      (∀i,(W.normal.phase i).coeff 0=0) ∧
      ∀θ : ℝ,
        Tendsto (fun s : ℝ =>
          (inverseRay (WasowGlobalRayData.direction (θ/denominator H p W)) s)^W.denominator) atTop l →
        Nonempty (CRGGeneralRayGauge.RayGaugeWitness (physicalCoefficient C H p W θ)
          (fun i => phaseOnRay (denominator H p W) (W.normal.phase i) θ
            ⟨0,Nat.mul_pos W.positive hp⟩)) := by
  obtain ⟨W⟩ := exists_square_global_realization (normalizedSeries H p) (p+(A H.index).order.toNat-1)
  exact ⟨W,W.normal.phase_zero,fun θ ht => physical_ray_normal_form hl hC H p hp hcont W θ ht⟩

#print axioms ramifiedCoefficient_companion
#print axioms physicalCoefficient_pullback
#print axioms physical_ray_normal_form
#print axioms exists_fixed_physical_phase_normal_form
end CRGPuiseuxCompanionNormalForm
