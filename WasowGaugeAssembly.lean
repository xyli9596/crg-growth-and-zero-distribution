import WasowWeightedRemainder
import WasowRealization
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual inverse-variable finite gauges and the exact transformed equation.
The operator remainder is the concrete rank-weighted inverse-gauge defect,
whose small integrable tail was proved from the analytic coefficient expansion.
No exact ray normal form is assumed in the analytic assembly. -/
set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Operator
attribute [local instance] Measure.Subtype.measureSpace
namespace WasowGaugeAssembly
open WasowMatrixPolynomial WasowActualTruncation WasowTruncatedGauge
open WasowWeightedRemainder WasowRealization WasowVolterra CRGNormalFormGoal
variable {m : ℕ}

/-- A matrix and its actual action on the finite-dimensional vector space. -/
def toOperator : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ]
    ((Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) :=
  (Matrix.toLin'.trans LinearMap.toContinuousLinearMap).toLinearMap

theorem continuous_toOperator : Continuous (toOperator (m := m)) :=
  toOperator.continuous_of_finiteDimensional

@[simp] theorem norm_toOperator (M : Matrix (Fin m) (Fin m) ℂ) : ‖toOperator M‖ = ‖M‖ := by
  exact (Matrix.linfty_opNorm_eq_opNorm M).symm

@[simp] theorem operatorMatrix_toOperator (M : Matrix (Fin m) (Fin m) ℂ) :
    operatorMatrix (toOperator M) = M := by
  exact LinearMap.toMatrix'_toLin' M

/-- Actual finite gauge in the real inverse variable. -/
def rayGauge (P : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (N : ℕ) (r : ℝ) :=
  gauge P N ((r : ℂ)⁻¹)

/-- Its actual real derivative, with the inverse-variable chain factor. -/
def rayGaugeDerivative (P : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (N : ℕ) (r : ℝ) :=
  (-((r : ℂ) ^ 2)⁻¹) • eval (PowerSeries.trunc N P).derivative ((r : ℂ)⁻¹)

/-- Entry evaluation is a genuine continuous linear functional. -/
def entryMap (i j : Fin m) : Matrix (Fin m) (Fin m) ℂ →L[ℂ] ℂ :=
  ({ toFun := fun M => M i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

theorem rayGauge_hasDerivAt (P : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (N : ℕ) {r : ℝ} (hr : r ≠ 0) (i j : Fin m) :
    HasDerivAt (fun s => rayGauge P N s i j) (rayGaugeDerivative P N r i j) r := by
  have hpoly : HasDerivAt (fun z : ℂ => gauge P N z i j)
      (eval (PowerSeries.trunc N P).derivative ((r : ℂ)⁻¹) i j) ((r : ℂ)⁻¹) :=
    (entryMap i j).hasFDerivAt.comp_hasDerivAt _ (gauge_hasDerivAt P N ((r : ℂ)⁻¹))
  have hh := (hpoly.comp (r : ℂ) (hasDerivAt_inv (by exact_mod_cast hr))).comp_ofReal
  simpa only [rayGauge, rayGaugeDerivative, Matrix.smul_apply, smul_eq_mul,
    Function.comp_apply, mul_comm] using hh

def rayCoefficient (a : ℂ → Matrix (Fin m) (Fin m) ℂ) (q : ℕ) (r : ℝ) :=
  (r : ℂ) ^ (q - 1) • a ((r : ℂ)⁻¹)

def truncatedCoefficient (B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (q N : ℕ) (r : ℝ) :=
  (r : ℂ) ^ (q - 1) • eval (PowerSeries.trunc N B) ((r : ℂ)⁻¹)

/-- The rank weight and the inverse-variable derivative factor agree exactly. -/
theorem rank_chain_factor (q : ℕ) (hq : 0 < q) {z : ℂ} (hz : z ≠ 0) :
    z ^ (q - 1) * (z⁻¹) ^ (q + 1) = (z ^ 2)⁻¹ := by
  have he : q + 1 = (q - 1) + 2 := by omega
  rw [he, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hz, one_pow, one_mul, inv_pow]

/-- The actual transformed differential equation, with its true remainder.
The sole pointwise condition is the established right inverse identity. -/
theorem transformed_identity (a : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (q N : ℕ)
    (hq : 0 < q) {r : ℝ} (hr : r ≠ 0)
    (hinv : rayGauge P N r * (rayGauge P N r)⁻¹ = 1) :
    rayCoefficient a q r * rayGauge P N r = rayGaugeDerivative P N r +
      rayGauge P N r * (truncatedCoefficient B q N r + remainder a P B q N r) := by
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hrem : rayGauge P N r * remainder a P B q N r =
      (r : ℂ) ^ (q - 1) • actualDefect a P B q N ((r : ℂ)⁻¹) := by
    unfold remainder normalizedDefect
    rw [Matrix.mul_smul, ← Matrix.mul_assoc]
    change (r : ℂ) ^ (q - 1) •
      ((rayGauge P N r * (rayGauge P N r)⁻¹) * _) = _
    rw [hinv, Matrix.one_mul]
  rw [Matrix.mul_add, hrem]
  unfold rayCoefficient truncatedCoefficient rayGaugeDerivative
  rw [Matrix.smul_mul, Matrix.mul_smul]
  unfold actualDefect
  have hd : deriv (eval (PowerSeries.trunc N P)) ((r : ℂ)⁻¹) =
      eval (PowerSeries.trunc N P).derivative ((r : ℂ)⁻¹) :=
    (hasDerivAt_eval _ _).deriv
  rw [hd, smul_add, smul_sub, smul_smul, rank_chain_factor q hq hc, neg_smul]
  change (r : ℂ) ^ (q - 1) • (_ * _) = _
  dsimp only [rayGauge, WasowTruncatedGauge.gauge]
  abel

/-- The concrete operator remainder on a selected common half-line. -/
def tailOperator (a : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (q N : ℕ) (R : ℝ) :
    Ici R → ((Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) :=
  fun r => toOperator (remainder a P B q N r)

/-- Actual finite truncation supplies the complete analytic input to Volterra
realization. The two structural identifications are explicit: the rational ray
coefficient must equal the rank-scaled analytic coefficient, and the finite
transformed coefficient must equal the chosen diagonal phase derivative.
Neither an approximate gauge nor any remainder estimate is assumed. -/
theorem exists_approximateRayGauge_of_formal_truncation
    (A₀ : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ Rmin : ℝ)
    {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt a p 0)
    (A P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hc : ∀ n, p.coeff n = PowerSeries.coeff n A)
    (q N : ℕ) (hq : 0 < q) (hN : q + 1 ≤ N) (hP : PowerSeries.constantCoeff P = 1)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P))
    (dQ : Fin m → ℝ → ℂ)
    (hcoef : ∀ r > Rmin, coefficientOnRay A₀ θ r = rayCoefficient a q r)
    (hdiag : ∀ r > Rmin, truncatedCoefficient B q N r = Matrix.diagonal (fun i => dQ i r))
    (hpole : ∀ r > Rmin, ∀ i j, (RatFunc.denom (A₀ i j)).eval (ray θ r) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ Rmin ≤ R ∧
      Nonempty (ApproximateRayGauge A₀ θ R dQ (tailOperator a P B q N R)) ∧
      Continuous (tailOperator a P B q N R) ∧
      Integrable (fun r : Ici R => ‖tailOperator a P B q N R r‖) ∧
      (∫ r : Ici R, ‖tailOperator a P B q N R r‖) < ε := by
  obtain ⟨C, hC, Rg, hRg, hg⟩ := exists_inverse_tail_bounds P hP (by omega : 0 < N)
  obtain ⟨R, hR, hRlarge, hcont, hi, hsmall⟩ :=
    exists_small_remainder_tail ha A P B hc q N hq hN hP heq (max Rmin Rg) hε
  have hmin : Rmin ≤ R := (le_max_left Rmin Rg).trans hRlarge
  have hRgR : Rg ≤ R := (le_max_right Rmin Rg).trans hRlarge
  have htail {r : ℝ} (hr : R < r) : Rg ≤ r := hRgR.trans hr.le
  have hext {r : ℝ} (hr : R < r) :
      operatorMatrix (WasowVolterra.extend R (tailOperator a P B q N R) r) = remainder a P B q N r := by
    simp only [WasowVolterra.extend, retract, tailOperator, max_eq_right hr.le, operatorMatrix_toOperator]
  refine ⟨R, hR, hmin, ⟨{
    H := rayGauge P N
    Hinv := fun r => (rayGauge P N r)⁻¹
    H' := rayGaugeDerivative P N
    C := C, K := 0
    a_pos := lt_of_lt_of_le zero_lt_one hR
    C_pos := hC
    K_nonneg := le_refl 0
    pole_free := fun r hr => hpole r (hmin.trans_lt hr)
    H_derivative := fun r hr i j => rayGauge_hasDerivAt P N
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (hR.trans hr.le))) i j
    inverse_left := fun r hr => (hg r (htail hr)).2.1
    inverse_right := fun r hr => (hg r (htail hr)).2.2.1
    H_bound := ?_
    Hinv_bound := ?_
    residual_identity := ?_
  }⟩, ?_, ?_, ?_⟩
  · intro r hr x
    simpa only [rayGauge, Real.rpow_zero, mul_one] using (hg r (htail hr)).2.2.2.1 x
  · intro r hr x
    simpa only [rayGauge, Real.rpow_zero, mul_one] using (hg r (htail hr)).2.2.2.2 x
  · intro r hr
    rw [hcoef r (hmin.trans_lt hr), hext hr, ← hdiag r (hmin.trans_lt hr)]
    exact transformed_identity a P B q N hq
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (hR.trans hr.le))) (hg r (htail hr)).2.2.1
  · exact continuous_toOperator.comp (continuousOn_iff_continuous_domRestrict.mp hcont)
  · simp only [tailOperator, norm_toOperator]
    change Integrable ((fun r : ℝ => ‖remainder a P B q N r‖) ∘ Subtype.val)
      (Measure.comap Subtype.val volume)
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ici).mp hi.norm
  · simp only [tailOperator, norm_toOperator]
    have hh := integral_subtype (s := Ici R) measurableSet_Ici (fun r : ℝ => ‖remainder a P B q N r‖)
    exact hh.symm ▸ hsmall

end WasowGaugeAssembly
#print axioms WasowGaugeAssembly.continuous_toOperator
#print axioms WasowGaugeAssembly.norm_toOperator
#print axioms WasowGaugeAssembly.operatorMatrix_toOperator
#print axioms WasowGaugeAssembly.rayGauge_hasDerivAt
#print axioms WasowGaugeAssembly.rank_chain_factor
#print axioms WasowGaugeAssembly.transformed_identity

#print axioms WasowGaugeAssembly.exists_approximateRayGauge_of_formal_truncation
