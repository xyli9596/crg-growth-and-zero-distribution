import WasowGaugeAssembly
import WasowPhaseRealization

/-! Actual analytic realization of a formally reduced analytic coefficient.
The complete formal gauge is used only through a finite polynomial truncation.
The inverse gauge, the weighted remainder, the small integrable tail, and the
integration directions are constructed, rather than included as hypotheses.
The remaining structural assumptions identify the original rational ray
coefficient and its finite diagonal part with the proposed Puiseux phases. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix.Norms.Operator
attribute [local instance] Measure.Subtype.measureSpace
namespace WasowTruncationRealization
open CRGNormalFormGoal WasowGaugeAssembly WasowPhaseRealization

/-- A formal gauge equation with an actual analytic coefficient and a finite
Puiseux diagonal part gives a genuine exact ray gauge. In particular, neither
convergence of the formal gauge nor an assumed remainder estimate is needed.
The output has the exact differential identity and polynomial bounds on the
actual gauge and its actual inverse from the original goal. -/
theorem exists_exact_rayGauge_of_formal_truncation {m : ℕ}
    (A₀ : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ Rmin : ℝ)
    {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt a s 0)
    (A P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hc : ∀ n, s.coeff n = PowerSeries.coeff n A)
    (q N : ℕ) (hq : 0 < q) (hN : q + 1 ≤ N)
    (hP : PowerSeries.constantCoeff P = 1)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P))
    (p : ℕ) (hp : 0 < p) (G : Fin m → Polynomial ℂ) (ℓ : Fin p)
    (hcoef : ∀ r > Rmin, coefficientOnRay A₀ θ r = rayCoefficient a q r)
    (hdiag : ∀ r > Rmin, truncatedCoefficient B q N r =
      Matrix.diagonal (fun i => deriv (phaseOnRay p (G i) θ ℓ) r))
    (hpole : ∀ r > Rmin, ∀ i j, (RatFunc.denom (A₀ i j)).eval (ray θ r) ≠ 0) :
    Nonempty (RayGaugeWitness A₀ θ (fun i => phaseOnRay p (G i) θ ℓ)) := by
  obtain ⟨R₀, hmin, _, hrealize⟩ :=
    exists_exact_rayGauge_of_puiseux_phases A₀ p hp G θ ℓ Rmin
  obtain ⟨R, _, hR, ⟨H⟩, hcont, hL1, hsmall⟩ :=
    exists_approximateRayGauge_of_formal_truncation A₀ θ R₀ ha A P B hc q N hq hN hP heq
      (fun i => deriv (phaseOnRay p (G i) θ ℓ))
      (fun r hr => hcoef r (hmin.trans_lt hr))
      (fun r hr => hdiag r (hmin.trans_lt hr))
      (fun r hr => hpole r (hmin.trans_lt hr)) (by norm_num : (0 : ℝ) < 1)
  exact hrealize R hR (tailOperator a P B q N R) H hcont hL1 hsmall

end WasowTruncationRealization
#print axioms WasowTruncationRealization.exists_exact_rayGauge_of_formal_truncation
