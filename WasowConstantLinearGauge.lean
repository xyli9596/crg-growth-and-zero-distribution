import WasowConstantCoordinates
import WasowRegularGauge
import WasowShearingGauge

/-! A constant complex matrix has a fixed family of linear phases.
Jordan shearing turns each nilpotent block into a regular singular residue;
the existing exact regular gauge supplies both polynomial bounds. -/
set_option autoImplicit false
noncomputable section
open Matrix Set Filter
open scoped Topology BigOperators Matrix.Norms.Operator
namespace WasowConstantLinearGauge
open CRGNormalFormGoal WasowRegularSingular WasowRegularGauge
open WasowShearing WasowShearingGauge WasowGaugeComposition WasowRationalEvaluation
variable {m : ℕ}

theorem linear_phase (μ : ℂ) (θ r : ℝ) :
    phaseOnRay 1 (Polynomial.C μ * Polynomial.X) θ 0 r = μ * ray θ r := by
  simp [phaseOnRay, rootOnRay, ray]

theorem linear_phase_hasDerivAt (μ : ℂ) (θ r : ℝ) :
    HasDerivAt (fun t => phaseOnRay 1 (Polynomial.C μ * Polynomial.X) θ 0 t)
      (Complex.exp ((θ : ℂ)*Complex.I) * μ) r := by
  simp_rw [linear_phase]
  convert! (((hasDerivAt_id r).ofReal_comp).mul_const
    (Complex.exp ((θ : ℂ)*Complex.I))).const_mul μ using 1; simp [mul_comm]

/-- An exact commuting constant-plus-residue coefficient has linear phases. -/
theorem residue_rayGauge [NeZero m] (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (μ : Fin m → ℂ) (G : Matrix (Fin m) (Fin m) ℂ) (θ : ℝ)
    (hcomm : Commute (diagonal μ) G)
    (hc : ∀ᶠ r in atTop, coefficientOnRay A θ r =
      Complex.exp ((θ : ℂ)*Complex.I) • diagonal μ + ((r : ℂ)⁻¹) • G) :
    Nonempty (RayGaugeWitness A θ
      (fun i => phaseOnRay 1 (Polynomial.C (μ i)*Polynomial.X) θ 0)) := by
  obtain ⟨C,K,hC,hK,hbound⟩ := exists_polynomial_bounds G θ
  have hp : ∀ᶠ r in atTop, ∀ i j, (A i j).denom.eval (ray θ r) ≠ 0 := by
    simp only [Filter.eventually_all]
    intro i j
    exact eventually_pole_free (A i j) θ
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hc.and hp)
  let a := max 1 R
  have ha : 1 ≤ a := le_max_left _ _
  refine ⟨{
    T := rayPower G θ, S := rayPowerInverse G θ
    T' := fun r => ((r : ℂ)⁻¹) • (G*rayPower G θ r)
    R := a, C := C, K := K
    R_pos := zero_lt_one.trans_le ha, C_pos := hC, K_nonneg := hK
    pole_free := fun r hr => (hR r ((le_max_right _ _).trans hr.le)).2
    T_derivative := fun r hr i j => rayPower_hasDerivAt G θ
      (ne_of_gt (zero_lt_one.trans (ha.trans_lt hr))) i j
    inverse_left := fun r _ => rayPowerInverse_mul_rayPower G θ r
    inverse_right := fun r _ => rayPower_mul_rayPowerInverse G θ r
    T_bound := fun r hr x => (hbound r (ha.trans hr.le) x).1
    S_bound := fun r hr x => (hbound r (ha.trans hr.le) x).2
    gauge_identity := ?_ }⟩
  intro r hr
  rw [(hR r ((le_max_right _ _).trans hr.le)).1]
  have hDT := (commute_rayPower (diagonal μ) G hcomm θ r).eq
  have hST := rayPowerInverse_mul_rayPower G θ r
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul]
  rw [Matrix.mul_assoc, hDT, ← Matrix.mul_assoc, hST, Matrix.one_mul]
  simp only [Matrix.mul_assoc, add_sub_cancel_right]
  have hd : (fun i => deriv (phaseOnRay 1 (Polynomial.C (μ i)*Polynomial.X) θ 0) r) =
      fun i => Complex.exp ((θ : ℂ)*Complex.I)*μ i := by
    funext i
    exact (linear_phase_hasDerivAt (μ i) θ r).deriv
  rw [hd]
  ext i j
  by_cases hij : i=j <;> simp [hij]

def residue (J : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℂ) (k : Fin m → ℤ) :=
  J - diagonal μ - diagonal (fun i => (k i : ℂ))

theorem residue_commute (J : Matrix (Fin m) (Fin m) ℂ)
    (μ : Fin m → ℂ) (k : Fin m → ℤ)
    (hoff : ∀ i j, i ≠ j → J i j ≠ 0 → μ i = μ j ∧ k j-k i=-1) :
    Commute (diagonal μ) (residue J μ k) := by
  change diagonal μ * residue J μ k = residue J μ k * diagonal μ
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, residue, Matrix.sub_apply]
  by_cases hij : i=j
  · subst j
    ring
  · simp only [Matrix.diagonal_apply_ne _ hij]
    by_cases hz : J i j=0
    · simp [hz]
    · rw [(hoff i j hij hz).1]
      ring

theorem shearing_identity (J : Matrix (Fin m) (Fin m) ℂ)
    (μ : Fin m → ℂ) (k : Fin m → ℤ)
    (hd : ∀ i, J i i=μ i)
    (hoff : ∀ i j, i ≠ j → J i j ≠ 0 → μ i = μ j ∧ k j-k i=-1)
    {z : ℂ} (hz : z ≠ 0) :
    inverseShear k z * J * shear k z - inverseShear k z * derivativeShear k z =
      diagonal μ + z⁻¹ • residue J μ k := by
  rw [exact_transformed_coefficient k J hz]
  ext i j
  change z ^ (k j-k i) * J i j - (diagonal (fun i => (k i : ℂ)/z)) i j =
    (diagonal μ) i j + z⁻¹ * (J i j - (diagonal μ) i j - (diagonal (fun i => (k i : ℂ))) i j)
  by_cases hij : i=j
  · subst j
    simp only [sub_self, zpow_zero, one_mul, Matrix.diagonal_apply_eq, hd, sub_self,
      zero_sub, div_eq_mul_inv]
    ring
  · simp only [Matrix.diagonal_apply_ne _ hij, sub_zero, zero_add]
    by_cases hzero : J i j=0
    · simp [hzero]
    · rw [(hoff i j hij hzero).2]
      simp

theorem jordan_linear_rayGauge [NeZero m] (J : Matrix (Fin m) (Fin m) ℂ)
    (μ : Fin m → ℂ) (k : Fin m → ℤ)
    (hd : ∀ i, J i i=μ i)
    (hoff : ∀ i j, i ≠ j → J i j ≠ 0 → μ i = μ j ∧ k j-k i=-1)
    (θ : ℝ) :
    Nonempty (RayGaugeWitness (constantMatrix J) θ
      (fun i => phaseOnRay 1 (Polynomial.C (μ i)*Polynomial.X) θ 0)) := by
  let B := shearedCoefficient (constantMatrix J) k
  have hc : ∀ᶠ r in atTop, coefficientOnRay B θ r =
      Complex.exp ((θ : ℂ)*Complex.I) • diagonal μ +
        ((r : ℂ)⁻¹) • residue J μ k := by
    filter_upwards [eventually_sheared_value (constantMatrix J) k θ,
      eventually_gt_atTop (0 : ℝ)] with r he hr
    have hz : ray θ r ≠ 0 := by
      simp [ray, hr.ne', Complex.exp_ne_zero]
    change Complex.exp ((θ : ℂ)*Complex.I) • B.map (value θ r) = _
    rw [he, value_constantMatrix, shearing_identity J μ k hd hoff hz,
      smul_add, smul_smul]
    have hrot : Complex.exp ((θ : ℂ)*Complex.I) * (ray θ r)⁻¹ = (r : ℂ)⁻¹ := by
      simp [ray, _root_.mul_inv_rev, Complex.exp_ne_zero]
    rw [hrot]
  obtain ⟨W⟩ := residue_rayGauge B μ (residue J μ k) θ
    (residue_commute J μ k hoff) hc
  exact pullback_shearing_rayGauge (constantMatrix J) k θ _ W

theorem constantConjugate_eq (A C : Matrix (Fin m) (Fin m) ℂ) :
    constantConjugate (constantMatrix A) C = constantMatrix (C⁻¹*A*C) := by
  ext i j
  simp [constantConjugate, constantMatrix, Matrix.mul_apply, map_sum, map_mul]

/-- Actual arbitrary constant matrix: fixed linear phases, constructed gauges. -/
theorem constant_linear_normal_form [NeZero m] (A : Matrix (Fin m) (Fin m) ℂ) :
    ∃ μ : Fin m → ℂ, ∀ θ : ℝ,
      Nonempty (RayGaugeWitness (constantMatrix A) θ
        (fun i => phaseOnRay 1 (Polynomial.C (μ i)*Polynomial.X) θ 0)) := by
  obtain ⟨C,μ,k,hC,hd,hoff⟩ := WasowConstantCoordinates.exists_weighted_coordinates A
  refine ⟨μ,fun θ => ?_⟩
  obtain ⟨W⟩ := jordan_linear_rayGauge (C⁻¹*A*C) μ k hd hoff θ
  apply pullback_constant_rayGauge (constantMatrix A) C hC θ _
  simpa only [constantConjugate_eq] using W

#print axioms linear_phase
#print axioms linear_phase_hasDerivAt
#print axioms residue_rayGauge
#print axioms residue_commute
#print axioms shearing_identity
#print axioms jordan_linear_rayGauge
#print axioms constantConjugate_eq
#print axioms constant_linear_normal_form
end WasowConstantLinearGauge
