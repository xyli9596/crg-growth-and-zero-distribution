import WasowMatrixPolynomial
import WasowTruncation
import WasowMatrixBounds
import WasowAnalyticRemainder

/-! Actual finite polynomial gauges, their derivatives, and true inverse bounds
on inverse-variable tails. No convergence of the infinite formal series is used. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology Matrix.Norms.Operator
namespace WasowTruncatedGauge
open WasowMatrixPolynomial

variable {m : ℕ}

theorem eval_zero (P : Polynomial (Matrix (Fin m) (Fin m) ℂ)) :
    eval P 0 = P.coeff 0 := by
  simp [eval, evaluation, Polynomial.eval₂RingHom'_apply]

def gauge (P : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (N : ℕ) :
    ℂ → Matrix (Fin m) (Fin m) ℂ := eval (PowerSeries.trunc N P)

theorem gauge_zero (P : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    {N : ℕ} (hN : 0 < N) : gauge P N 0 = PowerSeries.constantCoeff P := by
  rw [gauge, eval_zero, PowerSeries.coeff_trunc, if_pos hN,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem gauge_hasDerivAt (P : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (N : ℕ) (z : ℂ) :
    HasDerivAt (gauge P N) (eval (PowerSeries.trunc N P).derivative z) z :=
  hasDerivAt_eval _ _

theorem gauge_inverse_variable_tendsto (P : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hP : PowerSeries.constantCoeff P = 1) {N : ℕ} (hN : 0 < N) :
    Tendsto (fun r : ℝ => gauge P N ((r : ℂ)⁻¹)) atTop (𝓝 1) := by
  have hh := (continuous_eval (PowerSeries.trunc N P)).continuousAt.tendsto.comp
    WasowAnalyticRemainder.inverse_real_tendsto_zero
  change Tendsto (fun r : ℝ => gauge P N ((r : ℂ)⁻¹)) atTop (𝓝 (gauge P N 0)) at hh
  rwa [gauge_zero P hN, hP] at hh

/-- One actual late tail has a nonsingular finite polynomial gauge, its true
two-sided matrix inverse, and uniform bounds on both induced operators. -/
theorem exists_inverse_tail_bounds (P : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hP : PowerSeries.constantCoeff P = 1) {N : ℕ} (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧ ∀ r ≥ R,
      (gauge P N ((r : ℂ)⁻¹)).det ≠ 0 ∧
      (gauge P N ((r : ℂ)⁻¹))⁻¹ * gauge P N ((r : ℂ)⁻¹) = 1 ∧
      gauge P N ((r : ℂ)⁻¹) * (gauge P N ((r : ℂ)⁻¹))⁻¹ = 1 ∧
      (∀ x : Fin m → ℂ, ‖(gauge P N ((r : ℂ)⁻¹)).mulVec x‖ ≤ C * ‖x‖) ∧
      (∀ x : Fin m → ℂ, ‖((gauge P N ((r : ℂ)⁻¹))⁻¹).mulVec x‖ ≤ C * ‖x‖) := by
  have hlim := gauge_inverse_variable_tendsto P hP hN
  obtain ⟨C,hC,hbound⟩ := WasowMatrixBounds.eventually_uniform_mulVec_bounds hlim
  obtain ⟨R,hR⟩ := eventually_atTop.mp
    ((WasowMatrixBounds.eventually_det_ne_zero hlim).and hbound)
  exact ⟨C,hC,max 1 R,le_max_left _ _,fun r hr => hR r ((le_max_right 1 R).trans hr)⟩

#print axioms eval_zero
#print axioms gauge_zero
#print axioms gauge_hasDerivAt
#print axioms gauge_inverse_variable_tendsto
#print axioms exists_inverse_tail_bounds
end WasowTruncatedGauge
