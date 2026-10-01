import WasowRegularTail
import WasowPhaseRealization

/-! Actual realization of a finite canonical part `D(r) + G/r`.
The constant matrix `G` may have repeated eigenvalues and nilpotent parts.
It is required to commute with the specified diagonal phase derivative.
The true regular-singular gauge is inserted, and its conjugation losses are
absorbed by increasing the finite truncation order before constructing the tail.
No additional low-order terms in the finite canonical part are silently discarded. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix.Norms.Operator
attribute [local instance] Measure.Subtype.measureSpace
namespace WasowRegularTruncation
open WasowRegularSingular WasowRegularGauge WasowRegularTail
open WasowGaugeAssembly WasowRealization WasowPhaseRealization CRGNormalFormGoal
variable {m : ℕ}

/-- Exact algebraic identity for insertion of a commuting regular factor. -/
theorem regular_transformed_identity (A H H' D J R T S : Matrix (Fin m) (Fin m) ℂ)
    (hH : A * H = H' + H * (D + J + R))
    (hTS : T * S = 1) (hDT : Commute D T) :
    A * (H * T) = (H' * T + H * (J * T)) +
      (H * T) * (D + S * R * T) := by
  have hc : D * T = T * D := hDT.eq
  calc
    A * (H * T) = (H' + H * (D + J + R)) * T := by rw [← Matrix.mul_assoc, hH]
    _ = (H' * T + H * (J * T)) + H * (D * T) + H * R * T := by noncomm_ring
    _ = (H' * T + H * (J * T)) + (H * T) * D + H * R * T := by simp only [hc, Matrix.mul_assoc]
    _ = _ := by
      have hh : H * T * (S * R * T) = H * R * T := by
        calc
          _ = H * (T * S) * R * T := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hTS, Matrix.mul_one]
      rw [Matrix.mul_add, hh]
      abel

/-- Concrete operator remainder after the true constant regular factor. -/
def regularTailOperator [NeZero m] (G : Matrix (Fin m) (Fin m) ℂ) (θ : ℝ)
    (a : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (q N : ℕ) (R : ℝ) :
    Ici R → ((Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) :=
  fun r => toOperator (conjugatedRemainder G θ a P B q N r)

/-- The actual approximate gauge with its genuine inverse, derivative,
polynomial bounds, exact residual identity, and arbitrarily small operator tail.
The explicit canonical-part identity includes the entire finite truncation. -/
theorem exists_approximateRayGauge_of_regular_formal_truncation [NeZero m]
    (A₀ : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ Rmin : ℝ)
    (G : Matrix (Fin m) (Fin m) ℂ) (L : ℕ) (hL : ‖matrixOperator G‖ ≤ L)
    {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt a p 0)
    (A P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hc : ∀ n, p.coeff n = PowerSeries.coeff n A)
    (q N : ℕ) (hq : 0 < q) (hN : q + 2 * L + 1 ≤ N)
    (hP : PowerSeries.constantCoeff P = 1)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P))
    (dQ : Fin m → ℝ → ℂ)
    (hcoef : ∀ r > Rmin, coefficientOnRay A₀ θ r = rayCoefficient a q r)
    (hcanon : ∀ r > Rmin, truncatedCoefficient B q N r =
      Matrix.diagonal (fun i => dQ i r) + ((r : ℂ)⁻¹) • G)
    (hcomm : ∀ r > Rmin, Commute (Matrix.diagonal (fun i => dQ i r)) G)
    (hpole : ∀ r > Rmin, ∀ i j, (RatFunc.denom (A₀ i j)).eval (ray θ r) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ Rmin ≤ R ∧
      Nonempty (ApproximateRayGauge A₀ θ R dQ (regularTailOperator G θ a P B q N R)) ∧
      Continuous (regularTailOperator G θ a P B q N R) ∧
      Integrable (fun r : Ici R => ‖regularTailOperator G θ a P B q N R r‖) ∧
      (∫ r : Ici R, ‖regularTailOperator G θ a P B q N R r‖) < ε := by
  obtain ⟨C, hC, Rg, _, hg⟩ := WasowTruncatedGauge.exists_inverse_tail_bounds P hP (by omega : 0 < N)
  obtain ⟨R, hR, hRlarge, hcont, hi, hsmall⟩ :=
    exists_small_conjugated_tail G θ L hL ha A P B hc q N hq hN hP heq (max Rmin Rg) hε
  let E := Real.exp (|θ| * ‖matrixOperator G‖)
  have hE : 0 < E := Real.exp_pos _
  have hmin : Rmin ≤ R := (le_max_left _ _).trans hRlarge
  have htail {r : ℝ} (hr : R < r) : Rg ≤ r := (le_max_right _ _).trans (hRlarge.trans hr.le)
  have hr1 {r : ℝ} (hr : R < r) : 1 ≤ r := hR.trans hr.le
  have hrne {r : ℝ} (hr : R < r) : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le (hr1 hr))
  have hnorm {r : ℝ} (hr : R < r) :
      r ^ ‖matrixOperator G‖ ≤ r ^ (L : ℝ) := Real.rpow_le_rpow_of_exponent_le (hr1 hr) hL
  have htbound {r : ℝ} (hr : R < r) (x : Fin m → ℂ) :
      ‖(rayPower G θ r).mulVec x‖ ≤ E * r ^ (L : ℝ) * ‖x‖ := by
    exact (rayPower_mulVec_bound G θ (hr1 hr) x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hnorm hr) hE.le) (norm_nonneg _))
  have hsbound {r : ℝ} (hr : R < r) (x : Fin m → ℂ) :
      ‖(rayPowerInverse G θ r).mulVec x‖ ≤ E * r ^ (L : ℝ) * ‖x‖ := by
    exact (rayPowerInverse_mulVec_bound G θ (hr1 hr) x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hnorm hr) hE.le) (norm_nonneg _))
  have hext {r : ℝ} (hr : R < r) :
      operatorMatrix (WasowVolterra.extend R (regularTailOperator G θ a P B q N R) r) =
        conjugatedRemainder G θ a P B q N r := by
    simp only [WasowVolterra.extend, WasowVolterra.retract, regularTailOperator,
      max_eq_right hr.le, operatorMatrix_toOperator]
  refine ⟨R, hR, hmin, ⟨{
    H := fun r => rayGauge P N r * rayPower G θ r
    Hinv := fun r => rayPowerInverse G θ r * (rayGauge P N r)⁻¹
    H' := fun r => rayGaugeDerivative P N r * rayPower G θ r +
      rayGauge P N r * (((r : ℂ)⁻¹) • (G * rayPower G θ r))
    C := C * E, K := (L : ℝ)
    a_pos := zero_lt_one.trans_le hR
    C_pos := mul_pos hC hE
    K_nonneg := Nat.cast_nonneg _
    pole_free := fun r hr => hpole r (hmin.trans_lt hr)
    H_derivative := fun r hr i j => matrix_product_hasDerivAt _ _ _ _
      (rayGauge_hasDerivAt P N (hrne hr)) (rayPower_hasDerivAt G θ (hrne hr)) i j
    inverse_left := ?_
    inverse_right := ?_
    H_bound := ?_
    Hinv_bound := ?_
    residual_identity := ?_
  }⟩, ?_, ?_, ?_⟩
  · intro r hr
    calc
      _ = rayPowerInverse G θ r * ((rayGauge P N r)⁻¹ * rayGauge P N r) * rayPower G θ r := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        have hh : (rayGauge P N r)⁻¹ * rayGauge P N r = 1 := (hg r (htail hr)).2.1
        rw [hh, Matrix.mul_one, rayPowerInverse_mul_rayPower]
  · intro r hr
    calc
      _ = rayGauge P N r * (rayPower G θ r * rayPowerInverse G θ r) * (rayGauge P N r)⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [rayPower_mul_rayPowerInverse, Matrix.mul_one]; exact (hg r (htail hr)).2.2.1
  · intro r hr x
    rw [← Matrix.mulVec_mulVec]
    calc
      _ ≤ C * ‖(rayPower G θ r).mulVec x‖ := (hg r (htail hr)).2.2.2.1 _
      _ ≤ C * (E * r ^ (L : ℝ) * ‖x‖) := mul_le_mul_of_nonneg_left (htbound hr x) hC.le
      _ = _ := by ring
  · intro r hr x
    rw [← Matrix.mulVec_mulVec]
    calc
      _ ≤ E * r ^ (L : ℝ) * ‖(rayGauge P N r)⁻¹.mulVec x‖ := hsbound hr _
      _ ≤ E * r ^ (L : ℝ) * (C * ‖x‖) := mul_le_mul_of_nonneg_left
        ((hg r (htail hr)).2.2.2.2 x) (mul_nonneg hE.le (Real.rpow_nonneg (zero_le_one.trans (hr1 hr)) _))
      _ = _ := by ring
  · intro r hr
    rw [hext hr]
    have hh := transformed_identity a P B q N hq (hrne hr) (hg r (htail hr)).2.2.1
    rw [← hcoef r (hmin.trans_lt hr), hcanon r (hmin.trans_lt hr)] at hh
    have hj : ((r : ℂ)⁻¹) • (G * rayPower G θ r) =
        (((r : ℂ)⁻¹) • G) * rayPower G θ r := by rw [Matrix.smul_mul]
    rw [hj]
    exact regular_transformed_identity _ _ _ _ _ _ _ _ hh
      (rayPower_mul_rayPowerInverse G θ r)
      (commute_rayPower _ G (hcomm r (hmin.trans_lt hr)) θ r)
  · exact continuous_toOperator.comp (continuousOn_iff_continuous_domRestrict.mp hcont)
  · simp only [regularTailOperator, norm_toOperator]
    change Integrable ((fun r : ℝ => ‖conjugatedRemainder G θ a P B q N r‖) ∘ Subtype.val)
      (Measure.comap Subtype.val volume)
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ici).mp hi.norm
  · simp only [regularTailOperator, norm_toOperator]
    have hh := integral_subtype (s := Ici R) measurableSet_Ici
      (fun r : ℝ => ‖conjugatedRemainder G θ a P B q N r‖)
    exact hh.symm ▸ hsmall

/-- Actual finite-truncation realization including the entire commuting `G/r`
block. The truncation order explicitly pays for both regular-factor norms. -/
theorem exists_exact_rayGauge_of_regular_formal_truncation [NeZero m]
    (A₀ : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ Rmin : ℝ)
    (G : Matrix (Fin m) (Fin m) ℂ) (L : ℕ) (hL : ‖matrixOperator G‖ ≤ L)
    {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt a s 0)
    (A P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hc : ∀ n, s.coeff n = PowerSeries.coeff n A)
    (q N : ℕ) (hq : 0 < q) (hN : q + 2 * L + 1 ≤ N)
    (hP : PowerSeries.constantCoeff P = 1)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P))
    (p : ℕ) (hp : 0 < p) (F : Fin m → Polynomial ℂ) (ℓ : Fin p)
    (hcoef : ∀ r > Rmin, coefficientOnRay A₀ θ r = rayCoefficient a q r)
    (hcanon : ∀ r > Rmin, truncatedCoefficient B q N r =
      Matrix.diagonal (fun i => deriv (phaseOnRay p (F i) θ ℓ) r) + ((r : ℂ)⁻¹) • G)
    (hcomm : ∀ r > Rmin, Commute (Matrix.diagonal
      (fun i => deriv (phaseOnRay p (F i) θ ℓ) r)) G)
    (hpole : ∀ r > Rmin, ∀ i j, (RatFunc.denom (A₀ i j)).eval (ray θ r) ≠ 0) :
    Nonempty (RayGaugeWitness A₀ θ (fun i => phaseOnRay p (F i) θ ℓ)) := by
  obtain ⟨R₀, hmin, _, hrealize⟩ :=
    exists_exact_rayGauge_of_puiseux_phases A₀ p hp F θ ℓ Rmin
  obtain ⟨R, _, hR, ⟨H⟩, hcont, hL1, hsmall⟩ :=
    exists_approximateRayGauge_of_regular_formal_truncation A₀ θ R₀ G L hL ha A P B hc
      q N hq hN hP heq (fun i => deriv (phaseOnRay p (F i) θ ℓ))
      (fun r hr => hcoef r (hmin.trans_lt hr))
      (fun r hr => hcanon r (hmin.trans_lt hr))
      (fun r hr => hcomm r (hmin.trans_lt hr))
      (fun r hr => hpole r (hmin.trans_lt hr)) (by norm_num : (0 : ℝ) < 1)
  exact hrealize R hR (regularTailOperator G θ a P B q N R) H hcont hL1 hsmall

end WasowRegularTruncation
#print axioms WasowRegularTruncation.regular_transformed_identity
#print axioms WasowRegularTruncation.exists_approximateRayGauge_of_regular_formal_truncation
#print axioms WasowRegularTruncation.exists_exact_rayGauge_of_regular_formal_truncation
