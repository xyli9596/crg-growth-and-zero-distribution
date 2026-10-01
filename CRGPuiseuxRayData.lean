import CRGAsymptoticCoefficientRayTail
import WasowGlobalRayData
import WasowLaurentGaugeControl

/-! Actual lifted-ray data for a complete sectorial asymptotic coefficient.
The true ramified source replaces rational evaluation throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Filter Set Asymptotics
namespace CRGPuiseuxRayData
open CRGNormalFormGoal WasowLaurentGauge WasowGlobalFormalCanonical
open WasowGlobalFormalSquare WasowLaurentClearing WasowLaurentTruncation
open WasowGlobalFiniteRealization WasowLaurentFiniteRealization WasowLaurentRayEquation
open CRGAsymptoticCoefficientCompleteExpansion CRGAsymptoticCoefficientRayTail
variable {m : ℕ}

/-- The actual coefficient after all formal ramification, restricted to the
lifted inverse ray with the genuine real Jacobian. -/
def liftedCoefficient {A : PowerSeries (Matrix (Fin m) (Fin m) ℂ)} {q : ℕ}
    (a : ℂ → Matrix (Fin m) (Fin m) ℂ) (W : SquareRealization (differentialCoefficient q A))
    (φ : ℝ) : ℝ → Matrix (Fin m) (Fin m) ℂ :=
  WasowLaurentRayEquation.coefficientOnRay (ramifiedCoefficient W.denominator q a)
    (WasowGlobalRayData.direction φ)

def error {A : PowerSeries (Matrix (Fin m) (Fin m) ℂ)} {q : ℕ}
    (a : ℂ → Matrix (Fin m) (Fin m) ℂ) (W : SquareRealization (differentialCoefficient q A)) (k : ℕ) :=
  residual (clearingOrder W) (coefficient W.normal) W.change.G W.change.H
    (clearedCoefficient a W.denominator q (clearingOrder W)) k

/-- Complete expansions restricted to the actual source ray supply the
entire genuine finite transformed equation, without rational coefficients. -/
theorem global_ray_control
    {l : Filter ℂ} {a : ℂ → Matrix (Fin m) (Fin m) ℂ} {A : PowerSeries (Matrix (Fin m) (Fin m) ℂ)}
    (ha : CompleteExpansion l a A) (q : ℕ)
    (W : SquareRealization (differentialCoefficient q A)) (k : ℕ) (φ : ℝ)
    (ht : Tendsto (fun r : ℝ => (inverseRay (WasowGlobalRayData.direction φ) r)^W.denominator) atTop l) :
    ∃ C : ℝ, 0<C ∧ ∃ R : ℝ, 1≤R ∧ ∀ r : ℝ, R≤r →
      (WasowGlobalRayData.rayGauge W k φ r)⁻¹*WasowGlobalRayData.rayGauge W k φ r=1 ∧
      WasowGlobalRayData.rayGauge W k φ r*(WasowGlobalRayData.rayGauge W k φ r)⁻¹=1 ∧
      ‖WasowGlobalRayData.rayGauge W k φ r‖≤C*r^poleOrder W.change.G ∧
      ‖(WasowGlobalRayData.rayGauge W k φ r)⁻¹‖≤C*r^poleOrder W.change.H ∧
      DifferentiableAt ℝ (WasowGlobalRayData.rayGauge W k φ) r ∧
      liftedCoefficient a W φ r*WasowGlobalRayData.rayGauge W k φ r =
        deriv (WasowGlobalRayData.rayGauge W k φ) r + WasowGlobalRayData.rayGauge W k φ r*
          (Matrix.diagonal (fun i => deriv (phaseOnRay 1 (W.normal.phase i) φ 0) r) +
            WasowGlobalRayData.regularOnRay W.normal.regular (WasowGlobalRayData.regularLength W k) φ r +
            WasowGlobalRayData.rayRemainder a W k φ r) := by
  let u := WasowGlobalRayData.direction φ
  have hu : ‖u‖=1 := WasowGlobalRayData.direction_norm φ
  have hune : u≠0 := WasowGlobalRayData.direction_ne_zero φ
  have hfin := CRGPuiseuxFiniteRealization.finiteControl_of_square
    (rayFilter_le_punctured hune) ha q W (power_tendsto_rayFilter u W.denominator ht) k
  obtain ⟨C,hC,hbound⟩ := hfin.inverseBounds
  obtain ⟨R,hR⟩ := eventually_atTop.mp
    ((tendsto_map : Tendsto (inverseRay u) atTop (rayFilter u)).eventually hbound)
  refine ⟨C,hC,max 1 R,le_max_left _ _,?_⟩
  intro r hr
  have hrpos : 0<r := zero_lt_one.trans_le ((le_max_left 1 R).trans hr)
  have hb := hR r ((le_max_right 1 R).trans hr)
  refine ⟨hb.2.1,hb.2.2.1,?_,?_,
    (finiteGauge_onRay_hasDerivAt (clearingOrder W) W.change.G W.change.H k hune hrpos.ne').differentiableAt,?_⟩
  · simpa only [WasowGlobalRayData.rayGauge,onRay,inverseRay,norm_mul,hu,one_mul,norm_inv,
      Complex.norm_real,Real.norm_of_nonneg hrpos.le,inv_pow,div_inv_eq_mul] using hb.2.2.2.1
  · simpa only [WasowGlobalRayData.rayGauge,onRay,inverseRay,norm_mul,hu,one_mul,norm_inv,
      Complex.norm_real,Real.norm_of_nonneg hrpos.le,inv_pow,div_inv_eq_mul] using hb.2.2.2.2.1
  · have he := ray_equation
      (gauge (clearingOrder W) W.change.G W.change.H k)
      (ramifiedCoefficient W.denominator q a)
      (target (clearingOrder W) (coefficient W.normal) W.change.G W.change.H k)
      (error a W k) u hrpos.ne' hb.2.2.2.2.2.1 hb.2.2.2.2.2.2
    rw [WasowGlobalRayData.global_target_on_ray W k φ hrpos.ne'] at he
    exact he

/-- Holomorphic source functions provide the actual pointwise continuity
needed by the integrable ray residual; no regularity at the sector vertex
or convergence of its asymptotic series is needed. -/
theorem error_continuous_along_ray
    {l : Filter ℂ} {a : ℂ → Matrix (Fin m) (Fin m) ℂ} {A : PowerSeries (Matrix (Fin m) (Fin m) ℂ)}
    (hc : ∀ᶠ z in l,ContinuousAt a z) (q : ℕ)
    (W : SquareRealization (differentialCoefficient q A)) (k : ℕ) (φ : ℝ)
    (ht : Tendsto (fun r : ℝ => (inverseRay (WasowGlobalRayData.direction φ) r)^W.denominator) atTop l) :
    ∀ᶠ r : ℝ in atTop,ContinuousAt (error a W k) (inverseRay (WasowGlobalRayData.direction φ) r) := by
  let u := WasowGlobalRayData.direction φ
  have hune : u≠0 := WasowGlobalRayData.direction_ne_zero φ
  have hb := clearingOrder_bounds W
  have hi := WasowLaurentInverse.eventually_inverse_continuousAt (cleared W.change.G)
    (cleared W.change.H) (poleOrder W.change.G) (poleOrder W.change.H)
    (truncationOrder (clearingOrder W) W.change.G W.change.H k)
    (cleared_mul _ _ W.change.GH) (by unfold truncationOrder;omega)
  filter_upwards [ht.eventually hc, (WasowLaurentTail.ray_tendsto_punctured hune).eventually hi,
    eventually_gt_atTop (0:ℝ)] with r har hir hr
  have hz : inverseRay u r≠0 := mul_ne_zero hune (inv_ne_zero (by exact_mod_cast hr.ne'))
  have hclear : ContinuousAt (clearedCoefficient a W.denominator q (clearingOrder W)) (inverseRay u r) := by
    exact ((continuousAt_const.mul (continuousAt_id.pow _)).smul
      (ContinuousAt.comp (f := fun z : ℂ => z^W.denominator)
        (x := inverseRay u r) har (continuousAt_id.pow W.denominator)))
  exact hir.mul (WasowLaurentTail.rawDefect_continuousAt _ _ _ hb.1 hclear hz _ _)

/-- The finite residual is made arbitrarily small after the actual regular
fundamental matrices, with the derivative factor retained. -/
theorem smallConjugatedTails
    {l : Filter ℂ} {a : ℂ → Matrix (Fin m) (Fin m) ℂ} {A : PowerSeries (Matrix (Fin m) (Fin m) ℂ)}
    (ha : CompleteExpansion l a A) (hc : ∀ᶠ z in l,ContinuousAt a z) (q : ℕ)
    (W : SquareRealization (differentialCoefficient q A)) (φ : ℝ)
    (ht : Tendsto (fun r : ℝ => (inverseRay (WasowGlobalRayData.direction φ) r)^W.denominator) atTop l)
    (T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (L : ℕ) (ctrl : WasowPolynomialTail.Control T S L) :
    WasowLaurentExactAssembly.SmallConjugatedTails T S
      (WasowGlobalRayData.rayRemainder a W (2*L+2) φ) := by
  let u := WasowGlobalRayData.direction φ
  have hfin := CRGPuiseuxFiniteRealization.finiteControl_of_square
    (rayFilter_le_punctured (WasowGlobalRayData.direction_ne_zero φ)) ha q W
    (power_tendsto_rayFilter u W.denominator ht) (2*L+2)
  intro Rmin ε hε
  exact exists_small_conjugated_tail T S L ctrl (WasowGlobalRayData.direction_norm φ)
    (error_continuous_along_ray hc q W (2*L+2) φ ht) hfin.estimate Rmin hε

#print axioms global_ray_control
#print axioms error_continuous_along_ray
#print axioms smallConjugatedTails
end CRGPuiseuxRayData
