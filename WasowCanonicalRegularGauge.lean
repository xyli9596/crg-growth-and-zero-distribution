import WasowPhaseRegularGauge
import WasowGlobalRayData

/-! Every actual canonical regular truncation has a fundamental matrix which
preserves all fixed phase fibers. The growth exponent is chosen before the
angle and truncation degree; no commutation premise remains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix.Norms.Operator
namespace WasowCanonicalRegularGauge
open CRGNormalFormGoal WasowGlobalFormalCanonical WasowGlobalRayData
open WasowFuchsianRealization WasowPhaseRegularGauge
variable {m : ℕ}

/-- One exponent controls the actual phase-preserving regular fundamental
matrices on every ray and at every finite truncation order. -/
theorem exists_uniform_regular_family (N : NormalData (Fin m)) :
    ∃ L : ℕ, ∀ φ : ℝ, ∀ M : ℕ, 0<M →
      ∃ T S : ℝ → Matrix (Fin m) (Fin m) ℂ,
        ∃ g : RegularGauge (regularOnRay N.regular M φ) T S L,
          ∀ r>g.control.R,
            Commute (Matrix.diagonal (fun i => deriv (phaseOnRay 1 (N.phase i) φ 0) r)) (T r) := by
  obtain ⟨L,hL⟩ := exists_nat_ge (‖PowerSeries.constantCoeff N.regular‖+1)
  refine ⟨L,?_⟩
  intro φ M hM
  rw [regularOnRay_eq_rotated]
  have hsep : ∀ n i j, N.phase i ≠ N.phase j →
      PowerSeries.coeff n (rotatedSeries N.regular (direction φ)) i j = 0 := by
    intro n i j hij
    rw [coeff_rotatedSeries]
    simp only [Matrix.smul_apply, N.separated n i j hij, smul_zero]
  have hL' : ‖PowerSeries.constantCoeff (rotatedSeries N.regular (direction φ))‖+1 ≤ L := by
    simpa only [constantCoeff_rotatedSeries, norm_neg] using hL
  obtain ⟨T,S,g,hcomm⟩ := exists_regularGauge_preserving_fibers N.phase
    (rotatedSeries N.regular (direction φ)) hsep L hL' hM
  refine ⟨T,S,g,?_⟩
  intro r hr
  apply (hcomm r hr (fun i => deriv (phaseOnRay 1 (N.phase i) φ 0) r) ?_).1
  intro i j hij
  rw [hij]

#print axioms exists_uniform_regular_family
end WasowCanonicalRegularGauge
