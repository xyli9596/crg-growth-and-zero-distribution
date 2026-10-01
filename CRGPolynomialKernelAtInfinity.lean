import CRGPolynomialKernelCoefficients
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace CRGPolynomialKernel

/-- The reciprocal polynomial phase in a common inverse-power coordinate. -/
def inversePhase (Q : Polynomial ℂ) (p : ℕ) (x : ℂ) : ℂ :=
  x ^ (p * Q.natDegree) / Q.reverse.eval (x ^ p)

/-- The reversed polynomial is nonzero at the origin precisely because of
its genuine leading coefficient. -/
theorem reverse_eval_zero_ne_zero {Q : Polynomial ℂ} (hQ : Q ≠ 0) :
    Q.reverse.eval (0 : ℂ) ≠ 0 := by
  simpa only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse] using
    Polynomial.leadingCoeff_ne_zero.mpr hQ

/-- An identity of the actual polynomial values under ramification. -/
theorem inversePhase_eq {Q : Polynomial ℂ} (p : ℕ) {x : ℂ} (hx : x ≠ 0) :
    inversePhase Q p x = (Q.eval (x ^ (-(p : ℤ))))⁻¹ := by
  letI : Invertible ((x ^ p)⁻¹) := invertibleOfNonzero (inv_ne_zero (pow_ne_zero p hx))
  have he := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) ((x ^ p)⁻¹) Q
  simp only [Polynomial.eval₂_id, invOf_eq_inv, inv_inv] at he
  unfold inversePhase
  rw [zpow_neg, zpow_natCast, ← he, mul_inv_rev, inv_pow, inv_inv, div_eq_mul_inv, pow_mul]

/-- The inverse phase is an analytic germ and vanishes at the origin. -/
theorem analyticAt_inversePhase {Q : Polynomial ℂ} (hQ : Q ≠ 0)
    {p : ℕ} (hp : 0 < p) : AnalyticAt ℂ (inversePhase Q p) 0 := by
  have hrev : AnalyticAt ℂ (fun x : ℂ => Q.reverse.eval (x ^ p)) 0 :=
    ((AnalyticOnNhd.eval_polynomial Q.reverse) _ (mem_univ _)).comp (analyticAt_id.pow p)
  exact (analyticAt_id.pow (p * Q.natDegree)).mul
    (hrev.inv (by simpa only [zero_pow hp.ne'] using reverse_eval_zero_ne_zero hQ))

theorem inversePhase_zero {Q : Polynomial ℂ} (hdegree : 0 < Q.natDegree)
    {p : ℕ} (hp : 0 < p) : inversePhase Q p 0 = 0 := by
  simp only [inversePhase, zero_pow (Nat.mul_pos hp hdegree).ne', zero_div]

/-- The first nonzero degree of the reciprocal phase is the ramified polynomial
degree; composing an endpoint series with it preserves a nonzero leading term. -/
theorem inversePhase_analyticOrder {Q : Polynomial ℂ} (hQ : Q ≠ 0)
    {p : ℕ} (hp : 0 < p) :
    analyticOrderAt (inversePhase Q p) (0 : ℂ) = p * Q.natDegree := by
  have ha := analyticAt_inversePhase hQ hp
  apply ha.analyticOrderAt_eq_natCast.mpr
  refine ⟨fun x : ℂ => (Q.reverse.eval (x ^ p))⁻¹, ?_, ?_, ?_⟩
  · have hrev : AnalyticAt ℂ (fun x : ℂ => Q.reverse.eval (x ^ p)) 0 :=
      ((AnalyticOnNhd.eval_polynomial Q.reverse) _ (mem_univ _)).comp (analyticAt_id.pow p)
    exact hrev.inv (by simpa only [zero_pow hp.ne'] using reverse_eval_zero_ne_zero hQ)
  · apply inv_ne_zero
    simpa only [zero_pow hp.ne'] using reverse_eval_zero_ne_zero hQ
  · filter_upwards with x
    simp only [inversePhase, sub_zero, smul_eq_mul, div_eq_mul_inv]

/-- The analytic unit needed for fractional endpoint powers is formed around
1, so it is analytic for every nonzero leading complex coefficient. -/
def phaseUnit (Q : Polynomial ℂ) (p : ℕ) (x : ℂ) : ℂ :=
  Q.reverse.eval (x ^ p) / Q.leadingCoeff

theorem phaseUnit_zero {Q : Polynomial ℂ} (hQ : Q ≠ 0) {p : ℕ} (hp : 0 < p) :
    phaseUnit Q p 0 = 1 := by
  simp only [phaseUnit, zero_pow hp.ne', ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse,
    div_self (Polynomial.leadingCoeff_ne_zero.mpr hQ)]

theorem analyticAt_fractionalPhaseUnit {Q : Polynomial ℂ} (hQ : Q ≠ 0)
    {p : ℕ} (hp : 0 < p) (r : ℂ) :
    AnalyticAt ℂ (fun x : ℂ => (phaseUnit Q p x) ^ r) 0 := by
  have hrev : AnalyticAt ℂ (fun x : ℂ => Q.reverse.eval (x ^ p)) 0 :=
    ((AnalyticOnNhd.eval_polynomial Q.reverse) _ (mem_univ _)).comp (analyticAt_id.pow p)
  have hu : AnalyticAt ℂ (phaseUnit Q p) 0 := hrev.mul analyticAt_const
  exact hu.cpow analyticAt_const (by rw [phaseUnit_zero hQ hp]; exact Complex.one_mem_slitPlane)

#print axioms inversePhase_eq
#print axioms inversePhase_analyticOrder
#print axioms analyticAt_fractionalPhaseUnit
end CRGPolynomialKernel
