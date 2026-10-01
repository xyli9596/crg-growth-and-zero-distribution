import CRGWatsonDensityGrowing
import CRGAsymptoticCoefficientScalarAlgebra

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial
open scoped Topology BigOperators
namespace CRGWatson

/-- Endpoint integral expansions have a forced zero constant coefficient. -/
def integralSeries (c : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else c (n-1))

theorem integralSeries_constantCoeff (c : ℕ → ℂ) :
    PowerSeries.constantCoeff (integralSeries c) = 0 := by
  simp [integralSeries, PowerSeries.constantCoeff_mk]

theorem eval_trunc_integralSeries (c : ℕ → ℂ) (N : ℕ) (x : ℂ) :
    (PowerSeries.trunc (N+1) (integralSeries c)).eval x =
      ∑ j ∈ Finset.range N, c j * x^(j+1) := by
  change Polynomial.eval₂ (RingHom.id ℂ) x (PowerSeries.trunc (N+1) (integralSeries c)) = _
  rw [PowerSeries.eval₂_trunc_eq_sum_range,Finset.sum_range_succ']
  simp [integralSeries,PowerSeries.coeff_mk,RingHom.id_apply]

/-- The growing density endpoint's genuine formal integration-by-parts series. -/
def growingFormalSeries (v : ℝ → ℂ) : PowerSeries ℂ :=
  integralSeries (fun j => (-1 : ℂ)^j * iteratedDeriv j v 1)

/-- The decaying endpoint's genuine Gamma-moment series. -/
def decayingFormalSeries (w : ℝ → ℂ) (m : ℕ) : PowerSeries ℂ :=
  integralSeries (fun j => taylorCoefficient w j *
    (((1/(m:ℝ))*Real.Gamma (((j:ℝ)+1)/(m:ℝ))) : ℝ))

theorem endpointSeries_eq_trunc (v : ℝ → ℂ) (N : ℕ) (lam : ℂ) :
    endpointSeries v 1 lam N =
      (PowerSeries.trunc (N+1) (growingFormalSeries v)).eval lam⁻¹ := by
  rw [growingFormalSeries,eval_trunc_integralSeries]
  unfold endpointSeries
  apply Finset.sum_congr rfl
  intro j _
  rw [inv_pow,div_eq_mul_inv]
  ring

theorem decayingSum_eq_trunc (w : ℝ → ℂ) {m : ℕ} (_hm : 0 < m)
    (N : ℕ) (s : ℂ) :
    decayingSum w m N s = (PowerSeries.trunc (N+1) (decayingFormalSeries w m)).eval
      (s ^ (-(m : ℂ)⁻¹)) := by
  rw [decayingFormalSeries,eval_trunc_integralSeries]
  unfold decayingSum gammaMomentTerm
  apply Finset.sum_congr rfl
  intro j _
  have he : -((((j:ℝ)+1)/(m:ℝ)):ℂ) = (-(m:ℂ)⁻¹) * (j+1) := by
    simp only [Complex.ofReal_natCast]
    ring
  rw [he, ←Nat.cast_one (R := ℂ), ←Nat.cast_add,Complex.cpow_mul_nat]
  ring

#print axioms eval_trunc_integralSeries
#print axioms decayingSum_eq_trunc
end CRGWatson
