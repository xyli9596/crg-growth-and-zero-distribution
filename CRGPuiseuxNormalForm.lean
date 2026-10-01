import CRGPuiseuxRayData
import CRGGeneralRayGauge
import WasowCanonicalRegularGauge

/-! Exact lifted-ray normal forms for complete, possibly divergent sectorial
asymptotic coefficient expansions. Every formal choice and every analytic
regular factor is constructed from the fixed full matrix series. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Filter Set
namespace CRGPuiseuxNormalForm
open CRGNormalFormGoal WasowLaurentGauge WasowLaurentTruncation
open WasowGlobalFormalSquare WasowGlobalFiniteRealization
open WasowFuchsianRealization WasowLaurentExactAssembly
open CRGAsymptoticCoefficientCompleteExpansion WasowLaurentRayEquation
variable {m : ℕ}

/-- The genuine Laurent truncation and its integrable residual are corrected
by Volterra. No exact gauge or regular-family witness is an input. -/
theorem lifted_ray_normal_form
    {l : Filter ℂ} {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {A : PowerSeries (Matrix (Fin m) (Fin m) ℂ)}
    (ha : CompleteExpansion l a A) (hc : ∀ᶠ z in l,ContinuousAt a z) (q : ℕ)
    (W : SquareRealization (differentialCoefficient q A)) (φ : ℝ)
    (ht : Tendsto (fun r : ℝ => (inverseRay (WasowGlobalRayData.direction φ) r)^W.denominator) atTop l) :
    Nonempty (CRGGeneralRayGauge.RayGaugeWitness (CRGPuiseuxRayData.liftedCoefficient a W φ)
      (fun i => phaseOnRay 1 (W.normal.phase i) φ 0)) := by
  obtain ⟨L,hL⟩ := WasowCanonicalRegularGauge.exists_uniform_regular_family W.normal
  let k := 2*L+2
  let M := WasowGlobalRayData.regularLength W k
  have hM : 0<M := by unfold M WasowGlobalRayData.regularLength;omega
  obtain ⟨T,S,g,hcomm⟩ := hL φ M hM
  obtain ⟨C,hC,R,hR,hdata⟩ := CRGPuiseuxRayData.global_ray_control ha q W k φ ht
  have hb := clearingOrder_bounds W
  obtain ⟨z⟩ := WasowLaurentGaugeControl.exists_finiteGauge W.change.G W.change.H
    W.change.GH W.change.HG (clearingOrder W) k hb.1 (WasowGlobalRayData.direction_norm φ)
  have hz : FiniteGauge (WasowGlobalRayData.rayGauge W k φ)
      (fun r => (WasowGlobalRayData.rayGauge W k φ r)⁻¹)
      (deriv (WasowGlobalRayData.rayGauge W k φ)) (poleOrder W.change.G+poleOrder W.change.H) := z
  apply CRGGeneralRayGauge.exists_exact_rayGauge_of_laurent_regular
    (CRGPuiseuxRayData.liftedCoefficient a W φ) φ (max R g.control.R) _ _ _ _ hz
    (WasowGlobalRayData.regularOnRay W.normal.regular M φ) T S L g
    (WasowGlobalRayData.rayRemainder a W k φ) 1 (by omega) W.normal.phase 0
  · intro r hr
    exact (hdata r ((le_max_left _ _).trans hr.le)).2.2.2.2.2
  · intro r hr
    exact hcomm r ((le_max_right _ _).trans_lt hr)
  · exact CRGPuiseuxRayData.smallConjugatedTails ha hc q W φ ht T S L g.control

/-- One finite phase family and one ramification work on every compatible
lifted ray of the sector. They precede the ray and the chosen solution. -/
theorem exists_fixed_lifted_phase_normal_form
    {l : Filter ℂ} {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {A : PowerSeries (Matrix (Fin m) (Fin m) ℂ)}
    (ha : CompleteExpansion l a A) (hc : ∀ᶠ z in l,ContinuousAt a z) (q : ℕ) :
    ∃ W : SquareRealization (differentialCoefficient q A),
      (∀i,(W.normal.phase i).coeff 0=0) ∧
      ∀φ : ℝ,
        Tendsto (fun r : ℝ => (inverseRay (WasowGlobalRayData.direction φ) r)^W.denominator) atTop l →
        Nonempty (CRGGeneralRayGauge.RayGaugeWitness (CRGPuiseuxRayData.liftedCoefficient a W φ)
          (fun i => phaseOnRay 1 (W.normal.phase i) φ 0)) := by
  obtain ⟨W⟩ := exists_square_global_realization A q
  exact ⟨W,W.normal.phase_zero,fun φ ht => lifted_ray_normal_form ha hc q W φ ht⟩

#print axioms lifted_ray_normal_form
#print axioms exists_fixed_lifted_phase_normal_form
end CRGPuiseuxNormalForm
