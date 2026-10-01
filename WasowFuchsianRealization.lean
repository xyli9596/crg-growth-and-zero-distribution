import WasowPolynomialTail
import WasowRegularTruncation

/-! Analytic realization allowing a variable regular-singular coefficient.
The entire finite canonical part is retained. The regular factor is an actual
fundamental matrix with its proved inverse and polynomial bounds. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix.Norms.Operator
attribute [local instance] Measure.Subtype.measureSpace
namespace WasowFuchsianRealization
open WasowGaugeAssembly WasowRealization WasowPhaseRealization CRGNormalFormGoal
open WasowPolynomialTail
variable {m : ℕ}

structure RegularGauge (J T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (L : ℕ) where
  control : Control T S L
  derivative : ∀ r > control.R, ∀ i j,
    HasDerivAt (fun t => T t i j) ((J r * T r) i j) r
  inverse_left : ∀ r > control.R, S r * T r = 1
  inverse_right : ∀ r > control.R, T r * S r = 1

/-- Actual remainder after the general regular factor. -/
def regularTailOperator (T S : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (a : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (q N : ℕ) (R : ℝ) :
    Ici R → ((Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) :=
  fun r => toOperator (conjugatedRemainder T S a P B q N r)

/-- The actual approximate gauge with its genuine inverse, derivative,
polynomial bounds, exact residual identity, and arbitrarily small operator tail.
The explicit canonical-part identity includes the entire finite truncation. -/
theorem exists_approximateRayGauge_of_fuchsian_formal_truncation
    (A₀ : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ Rmin : ℝ)
    (J T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (L : ℕ) (g : RegularGauge J T S L)
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
      Matrix.diagonal (fun i => dQ i r) + J r)
    (hcomm : ∀ r > Rmin, Commute (Matrix.diagonal (fun i => dQ i r)) (T r))
    (hpole : ∀ r > Rmin, ∀ i j, (RatFunc.denom (A₀ i j)).eval (ray θ r) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ Rmin ≤ R ∧
      Nonempty (ApproximateRayGauge A₀ θ R dQ (regularTailOperator T S a P B q N R)) ∧
      Continuous (regularTailOperator T S a P B q N R) ∧
      Integrable (fun r : Ici R => ‖regularTailOperator T S a P B q N R r‖) ∧
      (∫ r : Ici R, ‖regularTailOperator T S a P B q N R r‖) < ε := by
  obtain ⟨C, hC, Rg, _, hg⟩ := WasowTruncatedGauge.exists_inverse_tail_bounds P hP (by omega : 0 < N)
  obtain ⟨R, hR, hRlarge, hcont, hi, hsmall⟩ :=
    WasowPolynomialTail.exists_small_conjugated_tail T S L g.control ha A P B hc q N hq hN hP heq (max (max Rmin g.control.R) Rg) hε
  let E := g.control.C
  have hE : 0 < E := g.control.C_pos
  have hmin : Rmin ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hRlarge)
  have hgR : g.control.R ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hRlarge)
  have hgr {r : ℝ} (hr : R < r) : g.control.R < r := hgR.trans_lt hr
  have htail {r : ℝ} (hr : R < r) : Rg ≤ r := (le_max_right _ _).trans (hRlarge.trans hr.le)
  have hr1 {r : ℝ} (hr : R < r) : 1 ≤ r := hR.trans hr.le
  have hrne {r : ℝ} (hr : R < r) : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le (hr1 hr))
  have htbound {r : ℝ} (hr : R < r) (x : Fin m → ℂ) :
      ‖(T r).mulVec x‖ ≤ E * r ^ (L : ℝ) * ‖x‖ := by
    exact (Matrix.linfty_opNorm_mulVec (T r) x).trans
      (mul_le_mul_of_nonneg_right (by simpa using g.control.T_bound r (hgr hr).le) (norm_nonneg x))
  have hsbound {r : ℝ} (hr : R < r) (x : Fin m → ℂ) :
      ‖(S r).mulVec x‖ ≤ E * r ^ (L : ℝ) * ‖x‖ := by
    exact (Matrix.linfty_opNorm_mulVec (S r) x).trans
      (mul_le_mul_of_nonneg_right (by simpa using g.control.S_bound r (hgr hr).le) (norm_nonneg x))
  have hext {r : ℝ} (hr : R < r) :
      operatorMatrix (WasowVolterra.extend R (regularTailOperator T S a P B q N R) r) =
        conjugatedRemainder T S a P B q N r := by
    simp only [WasowVolterra.extend, WasowVolterra.retract, regularTailOperator,
      max_eq_right hr.le, operatorMatrix_toOperator]
  refine ⟨R, hR, hmin, ⟨{
    H := fun r => rayGauge P N r * T r
    Hinv := fun r => S r * (rayGauge P N r)⁻¹
    H' := fun r => rayGaugeDerivative P N r * T r +
      rayGauge P N r * (J r * T r)
    C := C * E, K := (L : ℝ)
    a_pos := zero_lt_one.trans_le hR
    C_pos := mul_pos hC hE
    K_nonneg := Nat.cast_nonneg _
    pole_free := fun r hr => hpole r (hmin.trans_lt hr)
    H_derivative := fun r hr i j => matrix_product_hasDerivAt _ _ _ _
      (rayGauge_hasDerivAt P N (hrne hr)) (g.derivative r (hgr hr)) i j
    inverse_left := ?_
    inverse_right := ?_
    H_bound := ?_
    Hinv_bound := ?_
    residual_identity := ?_
  }⟩, ?_, ?_, ?_⟩
  · intro r hr
    calc
      _ = S r * ((rayGauge P N r)⁻¹ * rayGauge P N r) * T r := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        have hh : (rayGauge P N r)⁻¹ * rayGauge P N r = 1 := (hg r (htail hr)).2.1
        rw [hh, Matrix.mul_one, g.inverse_left r (hgr hr)]
  · intro r hr
    calc
      _ = rayGauge P N r * (T r * S r) * (rayGauge P N r)⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [g.inverse_right r (hgr hr), Matrix.mul_one]; exact (hg r (htail hr)).2.2.1
  · intro r hr x
    rw [← Matrix.mulVec_mulVec]
    calc
      _ ≤ C * ‖(T r).mulVec x‖ := (hg r (htail hr)).2.2.2.1 _
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
    exact WasowRegularTruncation.regular_transformed_identity _ _ _ _ _ _ _ _ hh
      (g.inverse_right r (hgr hr)) (hcomm r (hmin.trans_lt hr))
  · exact continuous_toOperator.comp (continuousOn_iff_continuous_domRestrict.mp hcont)
  · simp only [regularTailOperator, norm_toOperator]
    change Integrable ((fun r : ℝ => ‖conjugatedRemainder T S a P B q N r‖) ∘ Subtype.val)
      (Measure.comap Subtype.val volume)
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ici).mp hi.norm
  · simp only [regularTailOperator, norm_toOperator]
    have hh := integral_subtype (s := Ici R) measurableSet_Ici
      (fun r : ℝ => ‖conjugatedRemainder T S a P B q N r‖)
    exact hh.symm ▸ hsmall

/-- Exact realization with the full variable regular coefficient retained.
The truncation order pays for both actual fundamental matrix bounds. -/
theorem exists_exact_rayGauge_of_fuchsian_formal_truncation
    (A₀ : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ Rmin : ℝ)
    (J T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (L : ℕ) (g : RegularGauge J T S L)
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
      Matrix.diagonal (fun i => deriv (phaseOnRay p (F i) θ ℓ) r) + J r)
    (hcomm : ∀ r > Rmin, Commute (Matrix.diagonal
      (fun i => deriv (phaseOnRay p (F i) θ ℓ) r)) (T r))
    (hpole : ∀ r > Rmin, ∀ i j, (RatFunc.denom (A₀ i j)).eval (ray θ r) ≠ 0) :
    Nonempty (RayGaugeWitness A₀ θ (fun i => phaseOnRay p (F i) θ ℓ)) := by
  obtain ⟨R₀, hmin, _, hrealize⟩ :=
    exists_exact_rayGauge_of_puiseux_phases A₀ p hp F θ ℓ Rmin
  obtain ⟨R, _, hR, ⟨H⟩, hcont, hL1, hsmall⟩ :=
    exists_approximateRayGauge_of_fuchsian_formal_truncation A₀ θ R₀ J T S L g ha A P B hc
      q N hq hN hP heq (fun i => deriv (phaseOnRay p (F i) θ ℓ))
      (fun r hr => hcoef r (hmin.trans_lt hr))
      (fun r hr => hcanon r (hmin.trans_lt hr))
      (fun r hr => hcomm r (hmin.trans_lt hr))
      (fun r hr => hpole r (hmin.trans_lt hr)) (by norm_num : (0 : ℝ) < 1)
  exact hrealize R hR (regularTailOperator T S a P B q N R) H hcont hL1 hsmall

#print axioms exists_approximateRayGauge_of_fuchsian_formal_truncation
#print axioms exists_exact_rayGauge_of_fuchsian_formal_truncation
end WasowFuchsianRealization
