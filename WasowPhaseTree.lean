import WasowPhaseFamilyRamification

/-! An actual finite syntax for the phase algebra of reduction. Leaves have zero
exponential phase; scalar extraction, power ramification, and finite splitting
compute their denominator and polynomials recursively, before any ray angle.
This file proves the computed polynomials represent the recursive phase
functions. It does not assert that an arbitrary system has such a reduction tree.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowPhaseTree
open CRGNormalFormGoal WasowPhaseFamily WasowPhaseFamilyRamification

inductive Tree : Type
  | regular (m : ℕ)
  | scalar (Q : Polynomial ℂ) (hQ : Q.coeff 0 = 0) (child : Tree)
  | ramify (p : ℕ) (hp : 0 < p) (child : Tree)
  | split (s : ℕ) (child : Fin s → Tree)

def dimension : Tree → ℕ
  | .regular m => m
  | .scalar _ _ t => dimension t
  | .ramify _ _ t => dimension t
  | .split _ t => ∑ i, dimension (t i)

def denominator : Tree → ℕ
  | .regular _ => 1
  | .scalar _ _ t => denominator t
  | .ramify p _ t => p * denominator t
  | .split _ t => commonDenominator (fun i => denominator (t i))

theorem denominator_pos (t : Tree) : 0 < denominator t := by
  induction t with
  | regular m => exact Nat.zero_lt_one
  | scalar Q hQ t ih => exact ih
  | ramify p hp t ih => exact Nat.mul_pos hp ih
  | split s t ih => exact commonDenominator_pos _ ih

def family : (t : Tree) → Fin (dimension t) → Polynomial ℂ
  | .regular _, _ => 0
  | .scalar Q _ t, j => family t j + refinePhase (denominator t) Q
  | .ramify _ _ t, j => family t j
  | .split _ t, j =>
      commonFamily (fun i => denominator (t i)) (fun i => family (t i))
        ((finSigmaFinEquiv (n := fun i => dimension (t i))).symm j)

def phaseValue : (t : Tree) → ℝ → ℝ → Fin (dimension t) → ℂ
  | .regular _, _, _, _ => 0
  | .scalar Q _ t, θ, r, j => phaseValue t θ r j + phaseOnRay 1 Q θ 0 r
  | .ramify p _ t, θ, r, j => phaseValue t (θ / p) (WasowRamifiedGauge.rootRadius p r) j
  | .split _ t, θ, r, j =>
      let a := (finSigmaFinEquiv (n := fun i => dimension (t i))).symm j
      phaseValue (t a.1) θ r a.2

theorem family_coeff_zero (t : Tree) (j : Fin (dimension t)) : (family t j).coeff 0 = 0 := by
  induction t with
  | regular m => simp [family]
  | scalar Q hQ t ih =>
      change (family t j + refinePhase (denominator t) Q).coeff 0 = 0
      rw [Polynomial.coeff_add, ih j, refinePhase_coeff_zero _ (denominator_pos t), hQ, add_zero]
  | ramify p hp t ih => exact ih j
  | split s t ih =>
      exact commonFamily_coeff_zero _ (fun i => denominator_pos (t i)) _ ih _

/-- The computed finite family has precisely the actual recursive ray values.
All polynomial and denominator choices precede the universal angle quantifier. -/
theorem phaseValue_eq (t : Tree) (θ : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (j : Fin (dimension t)) :
    phaseValue t θ r j = phaseOnRay (denominator t) (family t j) θ ⟨0,denominator_pos t⟩ r := by
  induction t generalizing θ r with
  | regular m => simp [phaseValue, family, phaseOnRay]
  | scalar Q hQ t ih =>
      have hQphase : phaseOnRay (denominator t) (refinePhase (denominator t) Q) θ ⟨0,denominator_pos t⟩ r =
          phaseOnRay 1 Q θ 0 r := by
        simpa [phaseOnRay, rootOnRay] using
          phaseOnRay_refine 1 (denominator t) Nat.zero_lt_one (denominator_pos t) Q θ hr
      simp only [phaseValue, family, denominator, phaseOnRay, Polynomial.eval_add]
      rw [ih θ hr j]
      exact congrArg (fun z => phaseOnRay (denominator t) (family t j) θ ⟨0,denominator_pos t⟩ r + z)
        hQphase.symm
  | ramify p hp t ih =>
      change phaseValue t (θ / p) (WasowRamifiedGauge.rootRadius p r) j =
        phaseOnRay (p * denominator t) (family t j) θ ⟨0,Nat.mul_pos hp (denominator_pos t)⟩ r
      rw [ih (θ / p) (show 0 ≤ WasowRamifiedGauge.rootRadius p r from Real.rpow_nonneg hr _) j]
      exact phaseOnRay_comp p (denominator t) hp (denominator_pos t) (family t j) θ hr
  | split s t ih =>
      let a := (finSigmaFinEquiv (n := fun i => dimension (t i))).symm j
      change phaseValue (t a.1) θ r a.2 = _
      rw [ih a.1 θ hr a.2]
      exact (phaseOnRay_commonFamily (fun i => denominator (t i))
        (fun i => denominator_pos (t i)) (fun i => family (t i)) a θ hr).symm

/-- A finite tree yields a single fixed denominator and normalized family,
with an actual functional equality for every positive radius and every angle. -/
theorem exists_fixed_family (t : Tree) :
    ∃ (p : ℕ) (hp : 0 < p) (F : Fin (dimension t) → Polynomial ℂ),
      (∀ j, (F j).coeff 0 = 0) ∧ ∀ θ r, 0 ≤ r → ∀ j,
        phaseValue t θ r j = phaseOnRay p (F j) θ ⟨0,hp⟩ r := by
  exact ⟨denominator t, denominator_pos t, family t, family_coeff_zero t,
    fun θ r hr j => phaseValue_eq t θ hr j⟩

end WasowPhaseTree
#print axioms WasowPhaseTree.denominator_pos
#print axioms WasowPhaseTree.family_coeff_zero
#print axioms WasowPhaseTree.phaseValue_eq
#print axioms WasowPhaseTree.exists_fixed_family
