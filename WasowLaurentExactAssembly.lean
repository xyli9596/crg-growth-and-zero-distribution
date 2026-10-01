import WasowLaurentExactAssemblyData

/-! Exact analytic assembly for arbitrary finite Laurent gauges. The actual
finite gauge and regular fundamental matrix are multiplied, their full
residual is retained, and the proven mixed Volterra solver removes it. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix.Norms.Operator
attribute [local instance] Measure.Subtype.measureSpace
namespace WasowLaurentExactAssembly
open WasowPolynomialTail WasowGaugeAssembly WasowFuchsianRealization
open WasowRealization WasowPhaseRealization CRGNormalFormGoal
variable {m : ℕ}

local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by
    simp_rw [Matrix.linfty_opNNNorm_def]
    fun_prop

/-- Construct the actual approximate gauge from separate concrete factors.
Its polynomial exponent is exactly K+L; both actual inverse identities and
the differentiated product are retained. -/
theorem exists_approximateRayGauge_of_laurent_regular
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ Rmin : ℝ)
    (Z W Z' : ℝ → Mat (m := m)) (K : ℕ) (z : FiniteGauge Z W Z' K)
    (J T S : ℝ → Mat (m := m)) (L : ℕ) (g : RegularGauge J T S L)
    (E : ℝ → Mat (m := m)) (dQ : Fin m → ℝ → ℂ)
    (heq : ∀ r > Rmin,
      coefficientOnRay A θ r * Z r = Z' r +
        Z r * (Matrix.diagonal (fun i => dQ i r) + J r + E r))
    (hcomm : ∀ r > Rmin, Commute (Matrix.diagonal (fun i => dQ i r)) (T r))
    (hpole : ∀ r > Rmin, ∀ i j, (RatFunc.denom (A i j)).eval (ray θ r) ≠ 0)
    (htail : SmallConjugatedTails T S E) {ε : ℝ} (hε : 0<ε) :
    ∃ R : ℝ, 1≤R ∧ Rmin≤R ∧
      Nonempty (ApproximateRayGauge A θ R dQ (tailOperator T S E R)) ∧
      Continuous (tailOperator T S E R) ∧
      Integrable (fun r : Ici R => ‖tailOperator T S E R r‖) ∧
      (∫ r : Ici R, ‖tailOperator T S E R r‖) < ε := by
  obtain ⟨R,hR,hlarge,hcont,hi,hsmall⟩ :=
    htail (max Rmin (max z.control.R g.control.R)) ε hε
  have hmin : Rmin≤R := (le_max_left _ _).trans hlarge
  have hzR : z.control.R≤R := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hgR : g.control.R≤R := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hzr {r : ℝ} (hr : R<r) : z.control.R<r := hzR.trans_lt hr
  have hgr {r : ℝ} (hr : R<r) : g.control.R<r := hgR.trans_lt hr
  have hrnonneg {r : ℝ} (hr : R<r) : 0≤r := zero_le_one.trans (hR.trans hr.le)
  have hext {r : ℝ} (hr : R<r) :
      operatorMatrix (WasowVolterra.extend R (tailOperator T S E R) r) = S r*E r*T r := by
    simp only [WasowVolterra.extend, WasowVolterra.retract, tailOperator,
      max_eq_right hr.le, operatorMatrix_toOperator]
  refine ⟨R,hR,hmin,⟨{
    H := fun r => Z r*T r
    Hinv := fun r => S r*W r
    H' := fun r => Z' r*T r + Z r*(J r*T r)
    C := z.control.C*g.control.C
    K := ((K+L:ℕ):ℝ)
    a_pos := zero_lt_one.trans_le hR
    C_pos := mul_pos z.control.C_pos g.control.C_pos
    K_nonneg := Nat.cast_nonneg _
    pole_free := fun r hr => hpole r (hmin.trans_lt hr)
    H_derivative := fun r hr i j => matrix_product_hasDerivAt _ _ _ _
      (z.derivative r (hzr hr)) (g.derivative r (hgr hr)) i j
    inverse_left := ?_
    inverse_right := ?_
    H_bound := ?_
    Hinv_bound := ?_
    residual_identity := ?_
  }⟩,?_,?_,?_⟩
  · intro r hr
    calc
      _ = S r*(W r*Z r)*T r := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [z.inverse_left r (hzr hr), Matrix.mul_one, g.inverse_left r (hgr hr)]
  · intro r hr
    calc
      _ = Z r*(T r*S r)*W r := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [g.inverse_right r (hgr hr), Matrix.mul_one, z.inverse_right r (hzr hr)]
  · intro r hr x
    exact product_mulVec_bound (Z r) (T r) _ _ z.control.C_pos.le K L (hrnonneg hr)
      (z.control.T_bound r (hzr hr).le) (g.control.T_bound r (hgr hr).le) x
  · intro r hr x
    simpa only [Nat.add_comm L K, mul_comm g.control.C z.control.C] using
      product_mulVec_bound (S r) (W r) _ _ g.control.C_pos.le L K (hrnonneg hr)
        (g.control.S_bound r (hgr hr).le) (z.control.S_bound r (hzr hr).le) x
  · intro r hr
    rw [hext hr]
    exact WasowRegularTruncation.regular_transformed_identity _ _ _ _ _ _ _ _
      (heq r (hmin.trans_lt hr)) (g.inverse_right r (hgr hr)) (hcomm r (hmin.trans_lt hr))
  · exact continuous_toOperator.comp (continuousOn_iff_continuous_domRestrict.mp hcont)
  · simp only [tailOperator, norm_toOperator]
    change Integrable ((fun r : ℝ => ‖S r*E r*T r‖) ∘ Subtype.val)
      (Measure.comap Subtype.val volume)
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ici).mp hi.norm
  · simp only [tailOperator, norm_toOperator]
    have hh := integral_subtype (s := Ici R) measurableSet_Ici (fun r : ℝ => ‖S r*E r*T r‖)
    exact hh.symm ▸ hsmall

/-- Fixed Puiseux phases provide the integration modes automatically. The
actual Volterra correction produces a complete exact RayGaugeWitness from
an arbitrary finite Laurent gauge and the actual commuting regular factor. -/
theorem exists_exact_rayGauge_of_laurent_regular
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ Rmin : ℝ)
    (Z W Z' : ℝ → Mat (m := m)) (K : ℕ) (z : FiniteGauge Z W Z' K)
    (J T S : ℝ → Mat (m := m)) (L : ℕ) (g : RegularGauge J T S L)
    (E : ℝ → Mat (m := m))
    (p : ℕ) (hp : 0<p) (F : Fin m → Polynomial ℂ) (ℓ : Fin p)
    (heq : ∀ r > Rmin,
      coefficientOnRay A θ r * Z r = Z' r +
        Z r * (Matrix.diagonal (fun i => deriv (phaseOnRay p (F i) θ ℓ) r) + J r + E r))
    (hcomm : ∀ r > Rmin,
      Commute (Matrix.diagonal (fun i => deriv (phaseOnRay p (F i) θ ℓ) r)) (T r))
    (hpole : ∀ r > Rmin, ∀ i j, (RatFunc.denom (A i j)).eval (ray θ r) ≠ 0)
    (htail : SmallConjugatedTails T S E) :
    Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (F i) θ ℓ)) := by
  obtain ⟨R₀,hmin,_,hrealize⟩ :=
    exists_exact_rayGauge_of_puiseux_phases A p hp F θ ℓ Rmin
  obtain ⟨R,_,hR,⟨H⟩,hcont,hL1,hsmall⟩ :=
    exists_approximateRayGauge_of_laurent_regular A θ R₀ Z W Z' K z J T S L g E
      (fun i => deriv (phaseOnRay p (F i) θ ℓ))
      (fun r hr => heq r (hmin.trans_lt hr))
      (fun r hr => hcomm r (hmin.trans_lt hr))
      (fun r hr => hpole r (hmin.trans_lt hr)) htail (by norm_num : (0:ℝ)<1)
  exact hrealize R hR (tailOperator T S E R) H hcont hL1 hsmall

#print axioms exists_approximateRayGauge_of_laurent_regular
#print axioms exists_exact_rayGauge_of_laurent_regular
end WasowLaurentExactAssembly
