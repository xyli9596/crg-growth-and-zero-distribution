import WasowLaurentFiniteRealization
import Mathlib.Analysis.Complex.RealDeriv

/-! The genuine inverse-variable differential equation pulled back to a ray.
The factor `-u/r²` is derived from the actual derivative and multiplies the
original coefficient, the canonical target and the residual alike. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Filter Set
namespace WasowLaurentRayEquation
variable {m : ℕ}
abbrev Mat := Matrix (Fin m) (Fin m) ℂ

def inverseRay (u : ℂ) (r : ℝ) : ℂ := u*(r:ℂ)⁻¹

def chainFactor (u : ℂ) (r : ℝ) : ℂ := -u/(r:ℂ)^2

def onRay (G : ℂ → Mat (m := m)) (u : ℂ) (r : ℝ) : Mat (m := m) :=
  G (inverseRay u r)

def coefficientOnRay (C : ℂ → Mat (m := m)) (u : ℂ) (r : ℝ) : Mat (m := m) :=
  chainFactor u r • C (inverseRay u r)

/-- The exact real derivative of the inverse ray parameter. -/
theorem inverseRay_hasDerivAt (u : ℂ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (inverseRay u) (chainFactor u r) r := by
  have hh := ((hasDerivAt_inv (show (r:ℂ) ≠ 0 by exact_mod_cast hr)).const_mul u).comp_ofReal
  convert! hh using 1
  simp [chainFactor, div_eq_mul_inv]

/-- Restricting the actual complex derivative to the real ray retains the
complex scalar chain factor; no derivative value is supplied as a premise. -/
theorem onRay_hasDerivAt {G : ℂ → Mat (m := m)} (u : ℂ) {r : ℝ} (hr : r ≠ 0)
    (hG : DifferentiableAt ℂ G (inverseRay u r)) :
    HasDerivAt (onRay G u) (chainFactor u r • deriv G (inverseRay u r)) r := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hg := hasDerivAt_pi.mp (hasDerivAt_pi.mp hG.hasDerivAt i) j
  have hh := (hg.comp (r:ℂ)
    ((hasDerivAt_inv (show (r:ℂ) ≠ 0 by exact_mod_cast hr)).const_mul u)).comp_ofReal
  convert! hh using 1
  simp only [chainFactor, Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Exact pullback of the entire transformed equation. Both the target and
the residual receive the same actual derivative factor. -/
theorem ray_equation (G C B E : ℂ → Mat (m := m)) (u : ℂ) {r : ℝ} (hr : r ≠ 0)
    (hG : DifferentiableAt ℂ G (inverseRay u r))
    (heq : C (inverseRay u r)*G (inverseRay u r) = deriv G (inverseRay u r) +
      G (inverseRay u r)*(B (inverseRay u r)+E (inverseRay u r))) :
    coefficientOnRay C u r * onRay G u r = deriv (onRay G u) r +
      onRay G u r * (coefficientOnRay B u r+coefficientOnRay E u r) := by
  rw [(onRay_hasDerivAt u hr hG).deriv]
  have hh := congrArg (fun M : Mat (m := m) => chainFactor u r • M) heq
  simpa only [coefficientOnRay, onRay, Matrix.smul_mul, Matrix.mul_smul,
    smul_add, Matrix.mul_add] using hh

/-- The finite Laurent gauge automatically has the actual derivative on any
nonzero inverse ray point. -/
theorem finiteGauge_onRay_hasDerivAt (h : ℕ)
    (G H : WasowLaurentFiniteRealization.LMat (m := m)) (k : ℕ)
    {u : ℂ} (hu : u ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (onRay (WasowLaurentFiniteRealization.gauge h G H k) u)
      (chainFactor u r • deriv (WasowLaurentFiniteRealization.gauge h G H k)
        (inverseRay u r)) r := by
  apply onRay_hasDerivAt u hr
  apply WasowLaurentFiniteRealization.gauge_differentiableAt
  exact mul_ne_zero hu (inv_ne_zero (by exact_mod_cast hr))

/-- Automatic finite-gauge specialization with every chain factor explicit. -/
theorem finiteGauge_ray_equation (h : ℕ)
    (B G H : WasowLaurentFiniteRealization.LMat (m := m))
    (c : ℂ → Mat (m := m)) (k : ℕ) {u : ℂ} (hu : u ≠ 0) {r : ℝ} (hr : r ≠ 0)
    (hinv : WasowLaurentFiniteRealization.gauge h G H k (inverseRay u r) *
      (WasowLaurentFiniteRealization.gauge h G H k (inverseRay u r))⁻¹=1) :
    coefficientOnRay (WasowLaurentFiniteRealization.actualCoefficient h c) u r *
      onRay (WasowLaurentFiniteRealization.gauge h G H k) u r =
    deriv (onRay (WasowLaurentFiniteRealization.gauge h G H k) u) r +
      onRay (WasowLaurentFiniteRealization.gauge h G H k) u r *
        (coefficientOnRay (WasowLaurentFiniteRealization.target h B G H k) u r +
          coefficientOnRay (WasowLaurentFiniteRealization.residual h B G H c k) u r) := by
  apply ray_equation _ _ _ _ u hr
  · apply WasowLaurentFiniteRealization.gauge_differentiableAt
    exact mul_ne_zero hu (inv_ne_zero (by exact_mod_cast hr))
  · exact WasowLaurentFiniteRealization.transformed_equation h B G H c k _ hinv

/-- On a unit ray the derivative factor has precisely quadratic decay. -/
theorem chainFactor_norm {u : ℂ} (hu : ‖u‖=1) {r : ℝ} (hr : 0<r) :
    ‖chainFactor u r‖ = 1/r^2 := by
  simp [chainFactor, norm_pow, hu, Complex.norm_real, Real.norm_of_nonneg hr.le]

/-- The finite-realization theorem automatically supplies a common ray tail,
true inverses, fixed pole growth bounds, and the correctly pulled-back ODE. -/
theorem finite_realization_on_ray
    (A B G H : WasowLaurentFiniteRealization.LMat (m := m))
    (h : ℕ) (hh : 0<h)
    (hA : WasowLaurentTruncation.poleOrder A ≤ h)
    (hB : WasowLaurentTruncation.poleOrder B ≤ h)
    (hGH : G*H=1) (hHG : H*G=1) (heq : WasowLaurentGauge.GaugeEquation A G B)
    {c : ℂ → Mat (m := m)} {s : FormalMultilinearSeries ℂ ℂ (Mat (m := m))}
    (hc : HasFPowerSeriesAt c s 0)
    (hcoeff : ∀n, s.coeff n = PowerSeries.coeff n (WasowLaurentClearing.clearAt h A))
    (k : ℕ) {u : ℂ} (hu : ‖u‖=1) :
    ∃ C : ℝ, 0<C ∧ ∃ R : ℝ, 1≤R ∧ ∀ r : ℝ, R≤r →
      let T := onRay (WasowLaurentFiniteRealization.gauge h G H k) u
      (T r)⁻¹*T r=1 ∧ T r*(T r)⁻¹=1 ∧
      ‖T r‖ ≤ C*r^WasowLaurentTruncation.poleOrder G ∧
      ‖(T r)⁻¹‖ ≤ C*r^WasowLaurentTruncation.poleOrder H ∧
      DifferentiableAt ℝ T r ∧
      coefficientOnRay (WasowLaurentFiniteRealization.actualCoefficient h c) u r * T r =
        deriv T r + T r *
          (coefficientOnRay (WasowLaurentFiniteRealization.target h B G H k) u r +
            coefficientOnRay (WasowLaurentFiniteRealization.residual h B G H c k) u r) := by
  obtain ⟨_,C,hC,hbound⟩ := WasowLaurentFiniteRealization.finite_realization
    A B G H h hh hA hB hGH hHG heq hc hcoeff k
  have hune : u≠0 := by intro he; simp [he] at hu
  have ht := WasowLaurentTail.ray_tendsto_punctured hune
  obtain ⟨R,hR⟩ := eventually_atTop.mp (ht.eventually hbound)
  refine ⟨C,hC,max 1 R,le_max_left _ _,?_⟩
  intro r hr
  have hrpos : 0<r := lt_of_lt_of_le zero_lt_one ((le_max_left 1 R).trans hr)
  have hb := hR r ((le_max_right 1 R).trans hr)
  dsimp only
  refine ⟨hb.2.1,hb.2.2.1,?_,?_,
    (finiteGauge_onRay_hasDerivAt h G H k hune hrpos.ne').differentiableAt,
    finiteGauge_ray_equation h B G H c k hune hrpos.ne' hb.2.2.1⟩
  · simpa only [onRay, inverseRay, norm_mul, hu, one_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hrpos.le, inv_pow, div_inv_eq_mul] using hb.2.2.2.1
  · simpa only [onRay, inverseRay, norm_mul, hu, one_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hrpos.le, inv_pow, div_inv_eq_mul] using hb.2.2.2.2.1

#print axioms chainFactor_norm
#print axioms finite_realization_on_ray

#print axioms inverseRay_hasDerivAt
#print axioms onRay_hasDerivAt
#print axioms ray_equation
#print axioms finiteGauge_onRay_hasDerivAt
#print axioms finiteGauge_ray_equation
end WasowLaurentRayEquation
