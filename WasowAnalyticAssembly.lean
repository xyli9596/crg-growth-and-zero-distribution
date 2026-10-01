import WasowRegularTruncation
import WasowRamifiedGauge

/-! Assembly of actual finite-truncation realization, the commuting regular
factor, and ramification descent. The hypotheses are explicit formal canonical
data of the ramified coefficient function. Constructing these data for every
rational system is still a separate formal-reduction problem. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.Operator
namespace WasowAnalyticAssembly
open CRGNormalFormGoal WasowGaugeAssembly WasowRegularSingular

/-- A canonical formal reduction of the actual ramified coefficient yields
the original system's exact ray gauge. No gauge, inverse estimate, integrable
remainder, phase ordering, or branch choice is assumed in this implication. -/
theorem exists_original_rayGauge_of_ramified_formal_truncation
    {m : ℕ} [NeZero m]
    (A₀ : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (p : ℕ) (hp : 0 < p) (F : Fin m → Polynomial ℂ) (θ Rmin : ℝ)
    (G : Matrix (Fin m) (Fin m) ℂ) (L : ℕ) (hL : ‖matrixOperator G‖ ≤ L)
    {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt a s 0)
    (A P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hc : ∀ n, s.coeff n = PowerSeries.coeff n A)
    (q N : ℕ) (hq : 0 < q) (hN : q + 2 * L + 1 ≤ N)
    (hP : PowerSeries.constantCoeff P = 1)
    (heq : A * P - P * B =
      -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P))
    (hcoef : ∀ r > Rmin,
      coefficientOnRay (WasowRamification.rationalCoefficient p hp A₀) (θ / p) r =
        rayCoefficient a q r)
    (hcanon : ∀ r > Rmin, truncatedCoefficient B q N r =
      Matrix.diagonal (fun i => deriv (phaseOnRay 1 (F i) (θ / p) 0) r) +
        ((r : ℂ)⁻¹) • G)
    (hcomm : ∀ r > Rmin, Commute
      (Matrix.diagonal (fun i => deriv (phaseOnRay 1 (F i) (θ / p) 0) r)) G) :
    ∃ ℓ : Fin p, Nonempty (RayGaugeWitness A₀ θ
      (fun i => phaseOnRay p (F i) θ ℓ)) := by
  obtain ⟨Rp, hRp⟩ := Filter.eventually_atTop.mp
    (WasowRamifiedGauge.eventually_original_pole_free
      (WasowRamification.rationalCoefficient p hp A₀) (θ / p))
  let R := max Rmin Rp
  have hmin {r : ℝ} (hr : R < r) : Rmin < r := (le_max_left _ _).trans_lt hr
  obtain ⟨H⟩ := WasowRegularTruncation.exists_exact_rayGauge_of_regular_formal_truncation
    (WasowRamification.rationalCoefficient p hp A₀) (θ / p) R G L hL ha
    A P B hc q N hq hN hP heq 1 (by decide) F 0
    (fun r hr => hcoef r (hmin hr))
    (fun r hr => hcanon r (hmin hr))
    (fun r hr => hcomm r (hmin hr))
    (fun r hr => hRp r ((le_max_right _ _).trans hr.le))
  exact WasowRamifiedGauge.exists_descended_branch p hp A₀ F θ H

#print axioms exists_original_rayGauge_of_ramified_formal_truncation
end WasowAnalyticAssembly
