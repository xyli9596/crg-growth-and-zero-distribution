import CRGOrderPhaseData
import CRGOrderPhaseCriterion

/-! Concrete finite-polynomial-phase version of the order/type conclusion.
The phases here are the actual `phaseOnRay` functions used by Wasow. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace CRGOrderPolynomialPhases
open CRGOrderRay CRGNormalFormGoal

theorem positive_rational_order_of_phases {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z)
    (p : ℕ) (hp : 0 < p) (P : ι → Polynomial ℂ) (hP0 : ∀ i, (P i).coeff 0 = 0)
    (chosen : ℝ → ι) (branch : ℝ → Fin p) {D : Set ℝ} (hD : Dense D)
    (hn : ∀ θ ∈ D, ∀ᶠ r : ℝ in atTop, f (CRGPhragmenRay.point θ r) ≠ 0)
    (herror : ∀ θ ∈ D, ∃ C : ℝ, ∀ᶠ r : ℝ in atTop,
      |logValue f θ r - (phaseOnRay p (P (chosen θ)) θ (branch θ) r).re| ≤ C * Real.log r)
    (hlead : ∀ θ ∈ D, P (chosen θ) ≠ 0 → ((P (chosen θ)).leadingCoeff *
      (Complex.exp (((θ + 2 * Real.pi * (branch θ : ℝ)) / (p : ℝ) : ℝ) * Complex.I)) ^
        (P (chosen θ)).natDegree).re ≠ 0) :
    ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ : ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ : ℝ) := by
  let degree : ι → ℚ := fun i => (P i).natDegree / (p : ℚ)
  let leading : ℝ → ℝ := fun θ => ((P (chosen θ)).leadingCoeff *
    (Complex.exp (((θ + 2 * Real.pi * (branch θ : ℝ)) / (p : ℝ) : ℝ) * Complex.I)) ^
      (P (chosen θ)).natDegree).re
  apply CRGOrderPhaseCriterion.positive_rational_order hf hfinite htrans degree chosen leading hD
  intro θ hθ
  simpa only [degree, leading, Rat.cast_div, Rat.cast_natCast] using
    CRGOrderPhaseData.rayData_of_polynomial_phase p hp (P (chosen θ)) (hP0 _) θ (branch θ)
      (hn θ hθ) (herror θ hθ) (hlead θ hθ)

#print axioms positive_rational_order_of_phases
end CRGOrderPolynomialPhases
