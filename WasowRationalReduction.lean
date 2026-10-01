import WasowRationalAtInfinity
import WasowRecursivePhases

/-! An arbitrary rational matrix supplies its genuine analytic Taylor series,
then the complete finite formal reduction and its fixed phase family. This
constructs the formal input before selecting a ray. It does not identify the
formal operation tree with a single analytically realized Laurent gauge. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.Operator
namespace WasowRationalReduction
open CRGNormalFormGoal WasowRationalAtInfinity

/-- Number the actual tree's phase values by the original finite coordinates. -/
def phaseValue {m : ℕ} {A : PowerSeries (Matrix (Fin m) (Fin m) ℂ)} {rank : ℕ}
    (R : WasowRecursiveTree.Reduction A rank) (θ r : ℝ) (j : Fin m) : ℂ :=
  WasowRecursivePhases.phaseValue R θ r (Fin.cast (Fintype.card_fin m).symm j)

/-- All formal reduction data and all Puiseux phase polynomials are genuinely
constructed from the rational input; the angle is universally quantified last.
The remaining analytic task is realization of the composed formal tree. -/
theorem exists_rational_reduction_fixed_phases {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) :
    ∃ (s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ))
      (F : PowerSeries (Matrix (Fin m) (Fin m) ℂ)),
      HasFPowerSeriesAt (coefficient A) s 0 ∧
      (∀ n, s.coeff n = PowerSeries.coeff n F) ∧
      ∃ R : WasowRecursiveTree.Reduction F (order A),
        ∃ (p : ℕ) (hp : 0 < p) (G : Fin m → Polynomial ℂ),
          (∀ j, (G j).coeff 0 = 0) ∧ ∀ θ r, 0 ≤ r → ∀ j,
            phaseValue R θ r j = phaseOnRay p (G j) θ ⟨0,hp⟩ r := by
  obtain ⟨s, F, hs, hc⟩ := exists_formal_expansion A
  obtain ⟨R, p, hp, G, hG, he⟩ := WasowRecursivePhases.exists_reduction_fixed_phases F (order A)
  refine ⟨s, F, hs, hc, R, p, hp, fun j => G (Fin.cast (Fintype.card_fin m).symm j),
    fun j => hG _, ?_⟩
  intro θ r hr j
  exact he θ r hr _

#print axioms exists_rational_reduction_fixed_phases
end WasowRationalReduction
