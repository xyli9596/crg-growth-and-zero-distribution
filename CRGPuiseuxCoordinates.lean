import CRGPuiseuxCompanionNormalForm

/-! Actual local inverse Puiseux coordinates and compatibility of successive
ramifications on a fixed argument interval. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology
open Filter
namespace CRGPuiseuxCoordinates
open CRGNormalFormGoal WasowRamifiedGauge WasowLaurentRayEquation
open CRGPuiseuxCompanionNormalForm
variable {n : ℕ} {A : Fin (n+1) → PowerSeries ℂ}

def originalPoint (p : ℕ) (x : ℂ) : ℂ := x^(-(p:ℤ))

theorem ray_pow (p : ℕ) (hp : 0<p) (θ s : ℝ) :
    (ray (θ/p) s)^p=ray θ (s^p) := by
  simp only [ray,mul_pow,←Complex.ofReal_pow,direction_pow p hp θ]

theorem originalPoint_inverseRay (p : ℕ) (hp : 0<p) (θ s : ℝ) :
    originalPoint p (inverseRay (WasowGlobalRayData.direction (θ/p)) s)=ray θ (s^p) := by
  unfold originalPoint
  rw [zpow_neg,zpow_natCast,←inv_pow,WasowGlobalRayData.inverseRay_inv,ray_pow p hp]

theorem originalPoint_localOnRay (H : CRGPuiseuxScalarReduction.Highest A)
    (p : ℕ) (hp : 0<p) (W : FormalData H p) (θ : ℝ) {r : ℝ} (hr : 0≤r) :
    originalPoint p (localOnRay H p W θ r)=ray θ r := by
  unfold originalPoint localOnRay
  rw [zpow_neg,zpow_natCast,←pow_mul,←inv_pow,WasowGlobalRayData.inverseRay_inv]
  exact ray_root_pow (denominator H p W) (Nat.mul_pos W.positive hp) θ hr

theorem direction_pow_general (P : ℕ) (φ : ℝ) :
    WasowGlobalRayData.direction φ^P=WasowGlobalRayData.direction (φ*P) := by
  unfold WasowGlobalRayData.direction
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The local ray obtained after the full formal reduction is precisely the
original coefficient local ray, with its radius raised to the additional
integer power. No unrelated branch is introduced. -/
theorem inverseRay_power (P p : ℕ) (hP : 0<P) (hp : 0<p) (θ s : ℝ) :
    (inverseRay (WasowGlobalRayData.direction (θ/(P*p))) s)^P=
      inverseRay (WasowGlobalRayData.direction (θ/p)) (s^P) := by
  have hangle : (θ/(P*p:ℝ))*P=θ/p := by
    have hpR : (p:ℝ)≠0 := by exact_mod_cast hp.ne'
    have hPR : (P:ℝ)≠0 := by exact_mod_cast hP.ne'
    field_simp
  simp only [inverseRay,mul_pow,inv_pow,←Complex.ofReal_pow,
    direction_pow_general,hangle]

/-- Every original local ray automatically meets the compatibility condition
of the general normal-form theorem at every further positive ramification. -/
theorem lifted_tendsto_local_ray (P p : ℕ) (hP : 0<P) (hp : 0<p) (θ : ℝ) :
    Tendsto (fun s : ℝ => (inverseRay (WasowGlobalRayData.direction (θ/(P*p))) s)^P) atTop
      (CRGAsymptoticCoefficientRayTail.rayFilter (WasowGlobalRayData.direction (θ/p))) := by
  have hs : Tendsto (fun s : ℝ => s^P) atTop atTop := tendsto_pow_atTop hP.ne'
  have ht := (tendsto_map : Tendsto (inverseRay (WasowGlobalRayData.direction (θ/p))) atTop
    (CRGAsymptoticCoefficientRayTail.rayFilter (WasowGlobalRayData.direction (θ/p)))).comp hs
  change Tendsto (fun s : ℝ => inverseRay (WasowGlobalRayData.direction (θ/p)) (s^P)) atTop
    (CRGAsymptoticCoefficientRayTail.rayFilter (WasowGlobalRayData.direction (θ/p))) at ht
  simpa only [inverseRay_power P p hP hp θ] using ht

#print axioms ray_pow
#print axioms originalPoint_inverseRay
#print axioms originalPoint_localOnRay
#print axioms direction_pow_general
#print axioms inverseRay_power
#print axioms lifted_tendsto_local_ray
end CRGPuiseuxCoordinates
