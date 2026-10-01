import WasowGlobalRayData
import WasowGlobalConjugatedTail
import WasowLaurentGaugeControl
import WasowLaurentExactAssembly

/-! Final analytic assembly for the automatically constructed global Laurent
data. The regular-family input is supplied by the phase-preserving fundamental
matrix theorem; all other analytic hypotheses are generated here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Operator
namespace WasowGlobalExactAssembly
open CRGNormalFormGoal WasowLaurentGauge WasowLaurentTruncation
open WasowGlobalFormalSquare WasowGlobalFiniteRealization
open WasowFuchsianRealization WasowLaurentExactAssembly
variable {m : ℕ}

/-- Genuine global finite realization plus actual phase-preserving regular
fundamental matrices automatically yields the exact ramified ray witness. -/
theorem exact_of_regularFamily
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (F : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    {s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt (WasowRationalAtInfinity.coefficient A) s 0)
    (hcoeff : ∀n, s.coeff n = PowerSeries.coeff n F)
    (W : SquareRealization (differentialCoefficient (WasowRationalAtInfinity.order A) F))
    (φ : ℝ) (L : ℕ)
    (hregular : ∀ M : ℕ, 0<M → ∃ T S : ℝ → Matrix (Fin m) (Fin m) ℂ,
      ∃ g : RegularGauge (WasowGlobalRayData.regularOnRay W.normal.regular M φ) T S L,
        ∀ r>g.control.R,
          Commute (Matrix.diagonal (fun i => deriv (phaseOnRay 1 (W.normal.phase i) φ 0) r)) (T r)) :
    Nonempty (RayGaugeWitness (WasowRamification.rationalCoefficient W.denominator W.positive A)
      φ (fun i => phaseOnRay 1 (W.normal.phase i) φ 0)) := by
  let k := 2*L+2
  let M := WasowGlobalRayData.regularLength W k
  have hM : 0<M := by unfold M WasowGlobalRayData.regularLength; omega
  obtain ⟨T,S,g,hcomm⟩ := hregular M hM
  obtain ⟨C,hC,R,hR,hdata⟩ := WasowGlobalRayData.global_ray_control A F ha hcoeff W k φ
  have hb := clearingOrder_bounds W
  obtain ⟨z⟩ := WasowLaurentGaugeControl.exists_finiteGauge W.change.G W.change.H
    W.change.GH W.change.HG (clearingOrder W) k hb.1 (WasowGlobalRayData.direction_norm φ)
  have hz : FiniteGauge (WasowGlobalRayData.rayGauge W k φ)
      (fun r => (WasowGlobalRayData.rayGauge W k φ r)⁻¹)
      (deriv (WasowGlobalRayData.rayGauge W k φ)) (poleOrder W.change.G+poleOrder W.change.H) := z
  apply exists_exact_rayGauge_of_laurent_regular
    (WasowRamification.rationalCoefficient W.denominator W.positive A)
    φ (max R g.control.R) _ _ _ _ hz
    (WasowGlobalRayData.regularOnRay W.normal.regular M φ) T S L g
    (WasowGlobalRayData.rayRemainder (WasowRationalAtInfinity.coefficient A) W k φ)
    1 (by omega) W.normal.phase 0
  · intro r hr
    exact (hdata r ((le_max_left _ _).trans hr.le)).2.2.2.2.2.2
  · intro r hr
    exact hcomm r ((le_max_right _ _).trans_lt hr)
  · intro r hr
    exact (hdata r ((le_max_left _ _).trans hr.le)).1
  · exact WasowGlobalConjugatedTail.smallConjugatedTails ha F hcoeff
      (WasowRationalAtInfinity.order A) W T S L g.control (WasowGlobalRayData.direction_norm φ)

#print axioms exact_of_regularFamily
end WasowGlobalExactAssembly
