import WasowGlobalFiniteRealization
import WasowCanonicalPhaseEvaluation
import WasowLaurentRayEquation
import WasowRamifiedGauge
import WasowFuchsianTruncation

/-! Exact ray data for the automatically constructed global finite gauge.
The source is the actual ramified rational system, and the target retains the
same fixed polynomial phases. All real chain factors are derived explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix.Norms.Operator BigOperators
open Filter Set
namespace WasowGlobalRayData
open CRGNormalFormGoal WasowLaurentGauge WasowGlobalFormalCanonical
open WasowGlobalFormalSquare WasowLaurentClearing WasowLaurentTruncation
open WasowLaurentRayEquation
variable {m : ℕ}

/-- Direction in the inverse variable, opposite to the physical ray angle. -/
def direction (φ : ℝ) : ℂ := Complex.exp (-(φ : ℂ) * Complex.I)

theorem direction_ne_zero (φ : ℝ) : direction φ ≠ 0 := Complex.exp_ne_zero _

theorem direction_norm (φ : ℝ) : ‖direction φ‖ = 1 := by
  simpa only [direction, ← Complex.ofReal_neg] using Complex.norm_exp_ofReal_mul_I (-φ)

theorem direction_inv (φ : ℝ) : (direction φ)⁻¹ = Complex.exp ((φ : ℂ) * Complex.I) := by
  simp [direction, neg_mul, Complex.exp_neg]

/-- Inverting the inverse-variable ray gives the exact physical ray. -/
theorem inverseRay_inv (φ r : ℝ) : (inverseRay (direction φ) r)⁻¹ = ray φ r := by
  simp only [inverseRay, mul_inv, inv_inv, direction_inv, ray, mul_comm]

theorem inverseRay_ne_zero (φ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    inverseRay (direction φ) r ≠ 0 :=
  mul_ne_zero (direction_ne_zero φ) (inv_ne_zero (by exact_mod_cast hr))

/-- The regular-singular chain factor loses its angular dependence exactly. -/
theorem regular_chain_factor (φ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    chainFactor (direction φ) r * (inverseRay (direction φ) r)⁻¹ = -(r : ℂ)⁻¹ := by
  have hu := direction_ne_zero φ
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [chainFactor, inverseRay, mul_inv, inv_inv]
  field_simp

/-- A fixed polynomial phase has the required actual real ray derivative. -/
theorem phase_chain_factor (F : Polynomial ℂ) (φ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    chainFactor (direction φ) r *
      deriv (fun z : ℂ => F.eval z⁻¹) (inverseRay (direction φ) r) =
      deriv (phaseOnRay 1 F φ 0) r := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hd := ((WasowCanonicalPhaseEvaluation.phase_hasDerivAt F
    (inverseRay_ne_zero φ hr)).comp (r : ℂ)
      ((hasDerivAt_inv hrC).const_mul (direction φ))).comp_ofReal
  have he : (fun t : ℝ => F.eval (direction φ * (t : ℂ)⁻¹)⁻¹) = phaseOnRay 1 F φ 0 := by
    funext t
    rw [← show inverseRay (direction φ) t = direction φ * (t : ℂ)⁻¹ from rfl,
      inverseRay_inv]
    simp [phaseOnRay, rootOnRay, ray]
  simp only [Function.comp_apply] at hd
  rw [he] at hd
  rw [hd.deriv, (WasowCanonicalPhaseEvaluation.phase_hasDerivAt F
    (inverseRay_ne_zero φ hr)).deriv]
  simp only [chainFactor, div_eq_mul_inv]
  ring

/-- The finite regular coefficient in the ramified physical ray variable. -/
def regularOnRay (R : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (M : ℕ) (φ r : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  -(r : ℂ)⁻¹ • WasowMatrixPolynomial.eval (PowerSeries.trunc M R)
    (inverseRay (direction φ) r)

/-- Finite canonical evaluation along the ray, with the original phase and
exact regular truncation length. No canonical identity is assumed here. -/
theorem canonical_on_ray (D : NormalData (Fin m)) (h N : ℕ)
    (hh : 0 < h) (hN : h ≤ N) (hD : poleOrder (coefficient D) ≤ h)
    (φ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    chainFactor (direction φ) r •
      ((inverseRay (direction φ) r)^(-(h : ℤ)) •
        WasowMatrixPolynomial.eval (PowerSeries.trunc N (clearAt h (coefficient D)))
          (inverseRay (direction φ) r)) =
      Matrix.diagonal (fun i => deriv (phaseOnRay 1 (D.phase i) φ 0) r) +
        regularOnRay D.regular (N-h+1) φ r := by
  rw [WasowCanonicalPhaseEvaluation.eval_trunc_canonical_derivative h N hh hN D hD
    (inverseRay_ne_zero φ hr), smul_add, smul_smul, regular_chain_factor φ hr]
  congr 1
  apply Matrix.ext
  intro i j
  by_cases hij : i=j
  · subst j
    simpa only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul] using
      phase_chain_factor (D.phase i) φ hr
  · simp [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij]

/-- Polynomial chain factors agree with genuine positive power ramification. -/
theorem source_chain_factor (p : ℕ) (hp : 0 < p) (φ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    chainFactor (direction φ) r * (-(p : ℂ) *
      (inverseRay (direction φ) r)^(-(p : ℤ)-1)) =
      Complex.exp ((φ : ℂ)*Complex.I) * ((p : ℂ) * (ray φ r)^(p-1)) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have he : -(p : ℤ)-1 = -((p+1 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast, ← inv_pow, inverseRay_inv,
    show p+1 = (p-1)+2 by omega, pow_add]
  have hu := direction_ne_zero φ
  have hv : Complex.exp ((φ : ℂ)*Complex.I) = (direction φ)⁻¹ := (direction_inv φ).symm
  rw [hv]
  simp only [chainFactor, ray, hv, mul_pow]
  field_simp

/-- Pointwise identification of the actual source at genuine nonpoles. -/
theorem source_on_ray (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (p : ℕ) (hp : 0 < p) (φ : ℝ) {r : ℝ} (hr : r ≠ 0)
    (hA : ∀ i j, (A i j).denom.eval ((ray φ r)^p) ≠ 0) :
    WasowLaurentRayEquation.coefficientOnRay
      (WasowGlobalFiniteRealization.ramifiedCoefficient p (WasowRationalAtInfinity.order A)
        (WasowRationalAtInfinity.coefficient A)) (direction φ) r =
      CRGNormalFormGoal.coefficientOnRay (WasowRamification.rationalCoefficient p hp A) φ r := by
  unfold WasowLaurentRayEquation.coefficientOnRay
  rw [WasowGlobalFiniteRealization.ramifiedCoefficient_rational A p (inverseRay_ne_zero φ hr),
    smul_smul, source_chain_factor p hp φ hr]
  have he := WasowRamification.eval_rationalCoefficient p hp A (ray φ r) hA
  have hi : ((inverseRay (direction φ) r)^p)⁻¹ = (ray φ r)^p := by
    rw [← inv_pow, inverseRay_inv]
  rw [hi]
  apply Matrix.ext
  intro i j
  have hij := congrFun (congrFun he i) j
  change RatFunc.eval (RingHom.id ℂ) (ray φ r)
      (WasowRamification.rationalCoefficient p hp A i j) =
    ((p : ℂ)*(ray φ r)^(p-1))*RatFunc.eval (RingHom.id ℂ) ((ray φ r)^p) (A i j) at hij
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, CRGNormalFormGoal.coefficientOnRay]
  rw [hij]
  ring

/-- Required nonpoles of the original coefficient hold automatically on a tail. -/
theorem eventually_power_ray_pole_free (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (p : ℕ) (hp : 0 < p) (φ : ℝ) :
    ∀ᶠ r : ℝ in atTop, ∀ i j, (A i j).denom.eval ((ray φ r)^p) ≠ 0 := by
  simp only [Filter.eventually_all]
  intro i j
  obtain ⟨_, _, R, hR, hb⟩ := WasowRational.exists_polynomial_part_tail (A i j)
  filter_upwards [eventually_gt_atTop R] with r hr
  apply (hb ((ray φ r)^p) ?_).1
  rw [norm_pow, WasowRational.norm_ray φ (zero_le_one.trans (hR.trans hr.le))]
  exact hr.trans_le (le_self_pow₀ (hR.trans hr.le) hp.ne')

/-- The real source identity and actual ramified-system nonpoles share a tail. -/
theorem eventually_source_on_ray (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (p : ℕ) (hp : 0 < p) (φ : ℝ) :
    ∀ᶠ r : ℝ in atTop,
      (∀ i j, (WasowRamification.rationalCoefficient p hp A i j).denom.eval (ray φ r) ≠ 0) ∧
      WasowLaurentRayEquation.coefficientOnRay
        (WasowGlobalFiniteRealization.ramifiedCoefficient p (WasowRationalAtInfinity.order A)
          (WasowRationalAtInfinity.coefficient A)) (direction φ) r =
        CRGNormalFormGoal.coefficientOnRay (WasowRamification.rationalCoefficient p hp A) φ r := by
  filter_upwards [eventually_power_ray_pole_free A p hp φ,
    WasowRamifiedGauge.eventually_original_pole_free (WasowRamification.rationalCoefficient p hp A) φ,
    eventually_gt_atTop (0 : ℝ)] with r hA hB hr
  exact ⟨hB, source_on_ray A p hp φ hr.ne' hA⟩

/-- The regular truncation length after every fixed Laurent pole has been paid. -/
def regularLength {F : PowerSeries (Matrix (Fin m) (Fin m) ℂ)} {q : ℕ}
    (W : SquareRealization (differentialCoefficient q F)) (k : ℕ) : ℕ :=
  poleOrder W.change.G + poleOrder W.change.H + k + 1

/-- The actual finite gauge restricted to the ramified physical ray. -/
def rayGauge {F : PowerSeries (Matrix (Fin m) (Fin m) ℂ)} {q : ℕ}
    (W : SquareRealization (differentialCoefficient q F)) (k : ℕ) (φ : ℝ) :=
  onRay (WasowLaurentFiniteRealization.gauge (WasowGlobalFiniteRealization.clearingOrder W)
    W.change.G W.change.H k) (direction φ)

/-- The actual residual in the real ray equation, with its derivative factor. -/
def rayRemainder {F : PowerSeries (Matrix (Fin m) (Fin m) ℂ)} {q : ℕ}
    (a : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (W : SquareRealization (differentialCoefficient q F)) (k : ℕ) (φ : ℝ) :=
  WasowLaurentRayEquation.coefficientOnRay
    (WasowLaurentFiniteRealization.residual (WasowGlobalFiniteRealization.clearingOrder W)
      (coefficient W.normal) W.change.G W.change.H
      (WasowGlobalFiniteRealization.clearedCoefficient a W.denominator q
        (WasowGlobalFiniteRealization.clearingOrder W)) k) (direction φ)

/-- The specific global finite target automatically has the canonical ray identity. -/
theorem global_target_on_ray {F : PowerSeries (Matrix (Fin m) (Fin m) ℂ)} {q : ℕ}
    (W : SquareRealization (differentialCoefficient q F)) (k : ℕ) (φ : ℝ)
    {r : ℝ} (hr : r ≠ 0) :
    WasowLaurentRayEquation.coefficientOnRay
      (WasowLaurentFiniteRealization.target (WasowGlobalFiniteRealization.clearingOrder W)
        (coefficient W.normal) W.change.G W.change.H k) (direction φ) r =
      Matrix.diagonal (fun i => deriv (phaseOnRay 1 (W.normal.phase i) φ 0) r) +
        regularOnRay W.normal.regular (regularLength W k) φ r := by
  have hb := WasowGlobalFiniteRealization.clearingOrder_bounds W
  unfold WasowLaurentRayEquation.coefficientOnRay WasowLaurentFiniteRealization.target
  rw [canonical_on_ray W.normal _ _ hb.1
    (by unfold WasowLaurentFiniteRealization.truncationOrder; omega) hb.2.2.1 φ hr]
  congr 2
  unfold WasowLaurentFiniteRealization.truncationOrder regularLength
  omega

/-- A common actual tail has source and canonical identities simultaneously,
with true inverse bounds and the full differential equation. Only the original
analytic germ and its fixed Taylor coefficients are supplied as analytic input. -/
theorem global_ray_control
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (F : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    {s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt (WasowRationalAtInfinity.coefficient A) s 0)
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n F)
    (W : SquareRealization (differentialCoefficient (WasowRationalAtInfinity.order A) F))
    (k : ℕ) (φ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      (∀ i j, (WasowRamification.rationalCoefficient W.denominator W.positive A i j).denom.eval
        (ray φ r) ≠ 0) ∧
      (rayGauge W k φ r)⁻¹ * rayGauge W k φ r = 1 ∧
      rayGauge W k φ r * (rayGauge W k φ r)⁻¹ = 1 ∧
      ‖rayGauge W k φ r‖ ≤ C * r ^ poleOrder W.change.G ∧
      ‖(rayGauge W k φ r)⁻¹‖ ≤ C * r ^ poleOrder W.change.H ∧
      DifferentiableAt ℝ (rayGauge W k φ) r ∧
      CRGNormalFormGoal.coefficientOnRay
          (WasowRamification.rationalCoefficient W.denominator W.positive A) φ r * rayGauge W k φ r =
        deriv (rayGauge W k φ) r + rayGauge W k φ r *
          (Matrix.diagonal (fun i => deriv (phaseOnRay 1 (W.normal.phase i) φ 0) r) +
            regularOnRay W.normal.regular (regularLength W k) φ r +
            rayRemainder (WasowRationalAtInfinity.coefficient A) W k φ r) := by
  have hb := WasowGlobalFiniteRealization.clearingOrder_bounds W
  obtain ⟨hc, hmatch⟩ := WasowGlobalFiniteRealization.clearedCoefficient_expansion
    ha F hcoeff (WasowRationalAtInfinity.order A) W
  obtain ⟨C, hC, R₀, hR₀, hcontrol⟩ := finite_realization_on_ray
    _ _ _ _ (WasowGlobalFiniteRealization.clearingOrder W) hb.1 hb.2.1 hb.2.2.1
    W.change.GH W.change.HG W.change.equation hc hmatch k (direction_norm φ)
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp (eventually_source_on_ray A W.denominator W.positive φ)
  refine ⟨C, hC, max R₀ R₁, hR₀.trans (le_max_left _ _), ?_⟩
  intro r hr
  have hr₀ := (le_max_left R₀ R₁).trans hr
  have hr₁ := (le_max_right R₀ R₁).trans hr
  have hrpos : 0 < r := zero_lt_one.trans_le (hR₀.trans hr₀)
  have hz := inverseRay_ne_zero φ hrpos.ne'
  have ht := hcontrol r hr₀
  dsimp only at ht
  have hsource : WasowLaurentRayEquation.coefficientOnRay
      (WasowLaurentFiniteRealization.actualCoefficient (WasowGlobalFiniteRealization.clearingOrder W)
        (WasowGlobalFiniteRealization.clearedCoefficient (WasowRationalAtInfinity.coefficient A)
          W.denominator (WasowRationalAtInfinity.order A) (WasowGlobalFiniteRealization.clearingOrder W)))
      (direction φ) r =
      CRGNormalFormGoal.coefficientOnRay
        (WasowRamification.rationalCoefficient W.denominator W.positive A) φ r := by
    change chainFactor (direction φ) r • _ = _
    rw [WasowGlobalFiniteRealization.actualCoefficient_cleared _ _ _ _ hb.2.2.2 hz]
    exact (hR₁ r hr₁).2
  refine ⟨(hR₁ r hr₁).1, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ?_⟩
  have he := ht.2.2.2.2.2
  rw [hsource, global_target_on_ray W k φ hrpos.ne'] at he
  exact he

/-- The regular series rotated to a chosen inverse ray, with the sign from
its true Jacobian. This is a formal coefficient definition, never an infinite evaluation. -/
def rotatedSeries (R : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (u : ℂ) :
    PowerSeries (Matrix (Fin m) (Fin m) ℂ) :=
  PowerSeries.mk (fun n => -(u ^ n) • PowerSeries.coeff n R)

@[simp] theorem coeff_rotatedSeries (R : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (u : ℂ) (n : ℕ) :
    PowerSeries.coeff n (rotatedSeries R u) = -(u ^ n) • PowerSeries.coeff n R :=
  PowerSeries.coeff_mk _ _

/-- The residue is fixed independently of angle and truncation degree. -/
theorem constantCoeff_rotatedSeries (R : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (u : ℂ) : PowerSeries.constantCoeff (rotatedSeries R u) = -PowerSeries.constantCoeff R := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_rotatedSeries]
  simp

/-- Actual finite evaluation as a sum over precisely the retained coefficients. -/
theorem eval_trunc_sum (R : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (M : ℕ) (z : ℂ) :
    WasowMatrixPolynomial.eval (PowerSeries.trunc M R) z =
      ∑ n ∈ Finset.range M, z ^ n • PowerSeries.coeff n R := by
  change Polynomial.eval₂ (RingHom.id _) (algebraMap ℂ (Matrix (Fin m) (Fin m) ℂ) z)
    (PowerSeries.trunc M R) = _
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [RingHom.id_apply, ← map_pow, Algebra.smul_def]
  exact (Algebra.commutes (z ^ n) (PowerSeries.coeff n R)).symm

/-- Finite rotated evaluation is exactly the original evaluation at u*z. -/
theorem eval_trunc_rotatedSeries (R : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (u z : ℂ) (M : ℕ) :
    WasowMatrixPolynomial.eval (PowerSeries.trunc M (rotatedSeries R u)) z =
      -WasowMatrixPolynomial.eval (PowerSeries.trunc M R) (u*z) := by
  rw [eval_trunc_sum, eval_trunc_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [coeff_rotatedSeries, smul_smul, mul_pow]
  simp only [mul_neg, neg_smul, mul_comm]

/-- The canonical regular ray term is literally the existing Fuchsian
finite-truncation coefficient, so no new fundamental-solution premise is needed. -/
theorem regularOnRay_eq_rotated (R : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (M : ℕ) (φ : ℝ) :
    regularOnRay R M φ =
      WasowFuchsianTruncation.regularCoefficient (rotatedSeries R (direction φ)) M := by
  funext r
  unfold regularOnRay WasowFuchsianTruncation.regularCoefficient WasowTruncatedGauge.gauge
  rw [eval_trunc_rotatedSeries]
  simp only [inverseRay, neg_smul, smul_neg]

#print axioms coeff_rotatedSeries
#print axioms constantCoeff_rotatedSeries
#print axioms eval_trunc_sum
#print axioms eval_trunc_rotatedSeries
#print axioms regularOnRay_eq_rotated

#print axioms global_target_on_ray
#print axioms global_ray_control

#print axioms direction_ne_zero
#print axioms direction_norm
#print axioms direction_inv
#print axioms inverseRay_inv
#print axioms inverseRay_ne_zero
#print axioms regular_chain_factor
#print axioms phase_chain_factor
#print axioms canonical_on_ray
#print axioms source_chain_factor
#print axioms source_on_ray
#print axioms eventually_power_ray_pole_free
#print axioms eventually_source_on_ray
end WasowGlobalRayData
