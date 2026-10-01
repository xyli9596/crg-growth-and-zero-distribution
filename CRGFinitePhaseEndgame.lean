import CRGOrderAE
import CRGOrderPhaseData

/-! Full analytic endpoint of the paper's finite-phase argument. Each member
of the fixed finite phase family may have its own positive ramification.
Only the actual almost-everywhere scalar phase comparison is assumed:
leading-term nondegeneracy and two-sided logarithmic estimates are proved. -/
noncomputable section
open Set Filter MeasureTheory Polynomial
open scoped Topology
namespace CRGFinitePhaseEndgame
open CRGNormalFormGoal CRGOrderRay

/-- Real leading coefficient on the zero branch of a ramified polynomial. -/
def leading (p : ℕ) (P : Polynomial ℂ) (θ : ℝ) : ℝ :=
  (P.leadingCoeff * Complex.exp (((θ / (p : ℝ) : ℝ) : ℂ) * Complex.I) ^ P.natDegree).re

theorem leading_eq_monomial (p : ℕ) (P : Polynomial ℂ) (θ : ℝ) :
    leading p P θ = CRGPhaseDirections.leadingReal P.leadingCoeff
      ((P.natDegree : ℝ) / (p : ℝ)) θ := by
  unfold leading CRGPhaseDirections.leadingReal
  rw [← Complex.exp_nat_mul]
  congr 3
  push_cast
  ring

theorem natDegree_pos_of_normalized {P : Polynomial ℂ}
    (hP0 : P.coeff 0 = 0) (hP : P ≠ 0) : 0 < P.natDegree := by
  by_contra hn
  have hN : P.natDegree = 0 := Nat.eq_zero_of_not_pos hn
  apply hP
  rw [Polynomial.eq_C_of_natDegree_eq_zero hN, hP0, Polynomial.C_0]

/-- The bad leading directions are null for each nonzero normalized phase. -/
theorem ae_leading_ne_zero (p : ℕ) (hp : 0 < p) (P : Polynomial ℂ)
    (hP0 : P.coeff 0 = 0) (hP : P ≠ 0) :
    ∀ᵐ θ : ℝ, leading p P θ ≠ 0 := by
  have hdeg : 0 < (P.natDegree : ℝ) / (p : ℝ) := by
    apply div_pos
    · exact_mod_cast natDegree_pos_of_normalized hP0 hP
    · exact_mod_cast hp
  simpa only [leading_eq_monomial] using
    CRGPhaseDirections.leadingReal_ae_ne_zero
      (Polynomial.leadingCoeff_ne_zero.mpr hP) hdeg.ne'

/-- All members of a finite fixed phase family are nondegenerate outside one
null angular set. Their ramification denominators need not coincide. -/
theorem ae_all_leading_ne_zero {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (P : ι → Polynomial ℂ)
    (hP0 : ∀ i, (P i).coeff 0 = 0) :
    ∀ᵐ θ : ℝ, ∀ i : ι, P i ≠ 0 → leading (p i) (P i) θ ≠ 0 := by
  rw [ae_all_iff]
  intro i
  by_cases hP : P i = 0
  · exact Eventually.of_forall fun _ hne => (hne hP).elim
  · exact (ae_leading_ne_zero (p i) (hp i) (P i) (hP0 i) hP).mono fun _ h _ => h

/-- Convert the actual selected phase comparison to a.e. ray data, automatically
intersecting with the proved null complement of the leading bad directions. -/
theorem ae_rayData_of_phase_comparison {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (P : ι → Polynomial ℂ)
    (hP0 : ∀ i, (P i).coeff 0 = 0)
    (hphase : ∀ᵐ θ : ℝ, ∃ i : ι,
      (∀ᶠ r : ℝ in atTop, f (ray θ r) ≠ 0) ∧
      ∃ C : ℝ, ∀ᶠ r : ℝ in atTop,
        |Real.log ‖f (ray θ r)‖ - (phaseOnRay (p i) (P i) θ ⟨0, hp i⟩ r).re| ≤ C * Real.log r) :
    ∀ᵐ θ : ℝ, ∃ i : ι,
      RayData f θ (((P i).natDegree : ℚ) / (p i : ℚ) : ℚ)
        (leading (p i) (P i) θ) := by
  filter_upwards [hphase, ae_all_leading_ne_zero p hp P hP0] with θ hθ hlead
  obtain ⟨i, hn, herror⟩ := hθ
  refine ⟨i, ?_⟩
  have hh := CRGOrderPhaseData.rayData_of_polynomial_phase (p i) (hp i) (P i) (hP0 i)
    θ ⟨0, hp i⟩ hn herror (by
      intro hPi
      simpa only [leading, Fin.val_mk, Nat.cast_zero, mul_zero, add_zero] using hlead i hPi)
  simpa only [leading, Rat.cast_div, Rat.cast_natCast,
    Fin.val_mk, Nat.cast_zero, mul_zero, add_zero] using hh

/-- Complete finite-phase endpoint: a nonpolynomial entire function of finite
order with actual a.e. comparison to a fixed finite family of ramified
polynomials has positive rational order, finite positive type, and manuscript
C₀ completely regular growth with the unrestricted indicator. -/
theorem complete_of_finite_phases {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z)
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (P : ι → Polynomial ℂ)
    (hP0 : ∀ i, (P i).coeff 0 = 0)
    (hphase : ∀ᵐ θ : ℝ, ∃ i : ι,
      (∀ᶠ r : ℝ in atTop, f (ray θ r) ≠ 0) ∧
      ∃ C : ℝ, ∀ᶠ r : ℝ in atTop,
        |Real.log ‖f (ray θ r)‖ - (phaseOnRay (p i) (P i) θ ⟨0, hp i⟩ r).re| ≤ C * Real.log r) :
    ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ : ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ : ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ : ℝ) := by
  exact CRGOrderAE.complete_of_ae_rayData hf hfinite htrans
    (fun i => ((P i).natDegree : ℚ) / (p i : ℚ))
    (fun i θ => leading (p i) (P i) θ)
    (ae_rayData_of_phase_comparison p hp P hP0 hphase)

#print axioms leading_eq_monomial
#print axioms natDegree_pos_of_normalized
#print axioms ae_leading_ne_zero
#print axioms ae_all_leading_ne_zero
#print axioms ae_rayData_of_phase_comparison
#print axioms complete_of_finite_phases
end CRGFinitePhaseEndgame
