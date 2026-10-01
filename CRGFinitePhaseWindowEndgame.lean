import CRGIndicatorPeriodicRays

/-! The finite Puiseux-phase endpoint with exactly one revolution of actual
angular coverage. Periodicity is proved for the underlying rays. -/
noncomputable section
open Set Filter MeasureTheory Polynomial
open scoped Topology
namespace CRGFinitePhaseWindowEndgame
open CRGNormalFormGoal

/-- Finite phase comparisons only for almost every angle in (0,2π] already
imply positive rational order, finite positive type, and manuscript CRG. -/
theorem complete_of_finite_phases_window {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z)
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (P : ι → Polynomial ℂ)
    (hP0 : ∀ i, (P i).coeff 0 = 0)
    (hphase : ∀ᵐ θ : ℝ ∂volume.restrict (Ioc 0 (2 * Real.pi)), ∃ i : ι,
      (∀ᶠ r : ℝ in atTop, f (ray θ r) ≠ 0) ∧
      ∃ C : ℝ, ∀ᶠ r : ℝ in atTop,
        |Real.log ‖f (ray θ r)‖ - (phaseOnRay (p i) (P i) θ ⟨0, hp i⟩ r).re| ≤ C * Real.log r) :
    ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ : ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ : ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ : ℝ) := by
  exact CRGIndicatorPeriodicRays.complete_of_Ioc_finite_phases
    hf hfinite htrans p hp P hP0 hphase

#print axioms complete_of_finite_phases_window
end CRGFinitePhaseWindowEndgame
