import WasowPhaseFamily

/-! Restore a scalar polynomial coefficient by adding its actual polynomial
primitive to every phase. The existing gauge matrices and their polynomial
bounds are retained. Rational evaluation is only used on a proved common
nonpole tail. All phase polynomials are selected before the angle. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace WasowScalarPhase
open CRGNormalFormGoal WasowPhaseFamily

/-- Add the derivative of a fixed scalar polynomial to the actual rational
system. This is the inverse of removing that scalar polynomial part. -/
def addScalar {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (Q : Polynomial ℂ) : Matrix (Fin m) (Fin m) (RatFunc ℂ) :=
  A + Matrix.diagonal (fun _ => algebraMap (Polynomial ℂ) (RatFunc ℂ) Q.derivative)

def addPhase (p : ℕ) (Q F : Polynomial ℂ) : Polynomial ℂ :=
  F + refinePhase p Q

theorem addPhase_coeff_zero (p : ℕ) (hp : 0 < p) (Q F : Polynomial ℂ)
    (hQ : Q.coeff 0 = 0) (hF : F.coeff 0 = 0) : (addPhase p Q F).coeff 0 = 0 := by
  rw [addPhase, Polynomial.coeff_add, refinePhase_coeff_zero p hp, hQ, hF, add_zero]

theorem phaseOnRay_addPhase (p : ℕ) (hp : 0 < p) (Q F : Polynomial ℂ)
    (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    phaseOnRay p (addPhase p Q F) θ ⟨0,hp⟩ r =
      phaseOnRay p F θ ⟨0,hp⟩ r + phaseOnRay 1 Q θ 0 r := by
  have hh : phaseOnRay p (refinePhase p Q) θ ⟨0,hp⟩ r = phaseOnRay 1 Q θ 0 r := by
    simpa [phaseOnRay, rootOnRay] using
      phaseOnRay_refine 1 p Nat.zero_lt_one hp Q θ hr
  change (F + refinePhase p Q).eval _ = _
  rw [Polynomial.eval_add]
  exact congrArg (fun z => phaseOnRay p F θ ⟨0,hp⟩ r + z) hh

theorem polynomial_phase_hasDerivAt (Q : Polynomial ℂ) (θ r : ℝ) :
    HasDerivAt (phaseOnRay 1 Q θ 0)
      (Complex.exp ((θ : ℂ) * Complex.I) * Q.derivative.eval (ray θ r)) r := by
  have hcomplex := (Q.hasDerivAt (ray θ r)).comp (r : ℂ)
    ((hasDerivAt_id (r : ℂ)).mul_const (Complex.exp ((θ : ℂ) * Complex.I)))
  have hreal := hcomplex.comp_ofReal
  change HasDerivAt (fun t => Q.eval (rootOnRay 1 θ 0 t)) _ r
  simp_rw [WasowPolynomialPhase.rootOnRay_one]
  simpa only [Function.comp_apply, id_eq, one_mul, mul_one, ray, mul_comm] using hreal

theorem deriv_addPhase (p : ℕ) (hp : 0 < p) (Q F : Polynomial ℂ)
    (θ : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (phaseOnRay p (addPhase p Q F) θ ⟨0,hp⟩) r =
      deriv (phaseOnRay p F θ ⟨0,hp⟩) r +
        Complex.exp ((θ : ℂ) * Complex.I) * Q.derivative.eval (ray θ r) := by
  have hF := (WasowPhaseOrdering.phase_hasDerivAt p F θ ⟨0,hp⟩ hr).differentiableAt.hasDerivAt
  have hQ := polynomial_phase_hasDerivAt Q θ r
  have he : phaseOnRay p (addPhase p Q F) θ ⟨0,hp⟩ =ᶠ[𝓝 r]
      (fun t => phaseOnRay p F θ ⟨0,hp⟩ t + phaseOnRay 1 Q θ 0 t) := by
    filter_upwards [eventually_gt_nhds hr] with t ht
    exact phaseOnRay_addPhase p hp Q F θ ht.le
  exact ((hF.add hQ).congr_of_eventuallyEq he).deriv

/-- Exact evaluation of the scalar-restored rational matrix on one common
half-line. Totalized rational evaluation is never treated as a ring map. -/
theorem eventually_coefficient_addScalar {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (Q : Polynomial ℂ) (θ : ℝ) :
    ∀ᶠ r : ℝ in atTop, coefficientOnRay (addScalar A Q) θ r =
      coefficientOnRay A θ r +
        (Complex.exp ((θ : ℂ) * Complex.I) * Q.derivative.eval (ray θ r)) • 1 := by
  have he : ∀ᶠ r in atTop, ∀ i j,
      WasowRationalEvaluation.value θ r (addScalar A Q i j) =
        WasowRationalEvaluation.value θ r (A i j) +
          WasowRationalEvaluation.value θ r
            (Matrix.diagonal (fun _ : Fin m => algebraMap (Polynomial ℂ) (RatFunc ℂ) Q.derivative) i j) := by
    simp only [Filter.eventually_all]
    intro i j
    exact WasowRationalEvaluation.eventually_value_add _ _ θ
  filter_upwards [he] with r hr
  classical
  ext i j
  change Complex.exp ((θ : ℂ) * Complex.I) * WasowRationalEvaluation.value θ r (addScalar A Q i j) = _
  rw [hr i j]
  by_cases hij : i = j
  · subst j
    simp [WasowRationalEvaluation.value, coefficientOnRay,
      mul_add, RatFunc.eval_algebraMap]
  · simp [hij, WasowRationalEvaluation.value, coefficientOnRay]

/-- Restore a scalar phase using exactly the same T, S and T'. Only the common
starting radius is enlarged to exclude the original rational poles. -/
theorem addScalar_rayGauge {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (p : ℕ) (hp : 0 < p) (Q : Polynomial ℂ) (F : Fin m → Polynomial ℂ) (θ : ℝ)
    (W : RayGaugeWitness A θ (fun i => phaseOnRay p (F i) θ ⟨0,hp⟩)) :
    Nonempty (RayGaugeWitness (addScalar A Q) θ
      (fun i => phaseOnRay p (addPhase p Q (F i)) θ ⟨0,hp⟩)) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((eventually_coefficient_addScalar A Q θ).and
      (WasowRamifiedGauge.eventually_original_pole_free (addScalar A Q) θ))
  let R := max W.R B
  have hW {r : ℝ} (hr : R < r) : W.R < r := (le_max_left _ _).trans_lt hr
  have htail {r : ℝ} (hr : R < r) : B ≤ r := (le_max_right _ _).trans hr.le
  refine ⟨{
    T := W.T, S := W.S, T' := W.T', R := R, C := W.C, K := W.K
    R_pos := W.R_pos.trans_le (le_max_left _ _)
    C_pos := W.C_pos, K_nonneg := W.K_nonneg
    pole_free := fun r hr => (hB r (htail hr)).2
    T_derivative := fun r hr => W.T_derivative r (hW hr)
    inverse_left := fun r hr => W.inverse_left r (hW hr)
    inverse_right := fun r hr => W.inverse_right r (hW hr)
    T_bound := fun r hr => W.T_bound r (hW hr)
    S_bound := fun r hr => W.S_bound r (hW hr)
    gauge_identity := ?_ }⟩
  intro r hr
  rw [(hB r (htail hr)).1]
  have hmain := W.gauge_identity r (hW hr)
  have hi := W.inverse_left r (hW hr)
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hi]
  rw [add_sub_right_comm, hmain]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply,
    deriv_addPhase p hp Q (F i) θ (W.R_pos.trans (hW hr)), smul_eq_mul]
  split_ifs <;> simp

/-- Fixed-family closure under scalar extraction/addition. In particular the
new polynomial F_i + Q(X^p) has no dependence on the ray direction. -/
theorem scalar_family_addback {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (p : ℕ) (hp : 0 < p) (Q : Polynomial ℂ) (F : Fin m → Polynomial ℂ)
    (h : ∀ θ : ℝ, Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (F i) θ ⟨0,hp⟩))) :
    ∀ θ : ℝ, Nonempty (RayGaugeWitness (addScalar A Q) θ
      (fun i => phaseOnRay p (addPhase p Q (F i)) θ ⟨0,hp⟩)) := by
  intro θ
  obtain ⟨W⟩ := h θ
  exact addScalar_rayGauge A p hp Q F θ W

/-- Remove the actual scalar polynomial derivative before solving a block. -/
def removeScalar {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (Q : Polynomial ℂ) : Matrix (Fin m) (Fin m) (RatFunc ℂ) :=
  A - Matrix.diagonal (fun _ => algebraMap (Polynomial ℂ) (RatFunc ℂ) Q.derivative)

theorem addScalar_removeScalar {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (Q : Polynomial ℂ) : addScalar (removeScalar A Q) Q = A := by
  exact sub_add_cancel A _

/-- An actual witness of the scalar-stripped system yields one for the original
system, with the explicit fixed polynomial phase restored. -/
theorem removeScalar_rayGauge {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (p : ℕ) (hp : 0 < p) (Q : Polynomial ℂ) (F : Fin m → Polynomial ℂ) (θ : ℝ)
    (W : RayGaugeWitness (removeScalar A Q) θ
      (fun i => phaseOnRay p (F i) θ ⟨0,hp⟩)) :
    Nonempty (RayGaugeWitness A θ
      (fun i => phaseOnRay p (addPhase p Q (F i)) θ ⟨0,hp⟩)) := by
  simpa only [addScalar_removeScalar] using addScalar_rayGauge (removeScalar A Q) p hp Q F θ W

/-- The concrete scalar phase extracted at Wasow book rank q. -/
def rankPhase (q : ℕ) (α : ℂ) : Polynomial ℂ :=
  Polynomial.monomial (q+1) (α / ((q+1 : ℕ) : ℂ))

theorem rankPhase_coeff_zero (q : ℕ) (α : ℂ) : (rankPhase q α).coeff 0 = 0 := by
  simp [rankPhase, Polynomial.coeff_monomial]

theorem derivative_rankPhase (q : ℕ) (α : ℂ) :
    (rankPhase q α).derivative = Polynomial.monomial q α := by
  rw [rankPhase, Polynomial.derivative_monomial_succ]
  congr 1
  simpa only [Nat.cast_add, Nat.cast_one] using
    div_mul_cancel₀ α (show ((q+1 : ℕ) : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero q)

end WasowScalarPhase
#print axioms WasowScalarPhase.addPhase_coeff_zero
#print axioms WasowScalarPhase.phaseOnRay_addPhase
#print axioms WasowScalarPhase.polynomial_phase_hasDerivAt
#print axioms WasowScalarPhase.deriv_addPhase
#print axioms WasowScalarPhase.eventually_coefficient_addScalar
#print axioms WasowScalarPhase.addScalar_rayGauge
#print axioms WasowScalarPhase.scalar_family_addback

#print axioms WasowScalarPhase.rankPhase_coeff_zero
#print axioms WasowScalarPhase.derivative_rankPhase

#print axioms WasowScalarPhase.addScalar_removeScalar
#print axioms WasowScalarPhase.removeScalar_rayGauge
