import WasowRealization
import WasowPhaseRealization
import WasowLaurentExactAssembly

/-! Exact Volterra realization for arbitrary actual continuous matrix
coefficients along a ray. Rational-function structure is unnecessary here. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators BoundedContinuousFunction Matrix.Norms.Operator
attribute [local instance] Measure.Subtype.measureSpace
namespace CRGGeneralRayGauge
open CRGNormalFormGoal WasowVolterra WasowFundamental WasowRealization

structure RayGaugeWitness {m : ℕ} (A : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (q : Fin m → ℝ → ℂ) where
  T : ℝ → Matrix (Fin m) (Fin m) ℂ
  S : ℝ → Matrix (Fin m) (Fin m) ℂ
  T' : ℝ → Matrix (Fin m) (Fin m) ℂ
  R : ℝ
  C : ℝ
  K : ℝ
  R_pos : 0 < R
  C_pos : 0 < C
  K_nonneg : 0 ≤ K
  T_derivative : ∀ r > R, ∀ i j,
    HasDerivAt (fun t => T t i j) (T' r i j) r
  inverse_left : ∀ r > R, S r * T r = 1
  inverse_right : ∀ r > R, T r * S r = 1
  T_bound : ∀ r > R, ∀ x : Fin m → ℂ, ‖(T r).mulVec x‖ ≤ C * r ^ K * ‖x‖
  S_bound : ∀ r > R, ∀ x : Fin m → ℂ, ‖(S r).mulVec x‖ ≤ C * r ^ K * ‖x‖
  gauge_identity : ∀ r > R,
    S r * A r * T r - S r * T' r = Matrix.diagonal (fun i => deriv (q i) r)

structure ApproximateRayGauge {m : ℕ}
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (a : ℝ)
    (dQ : Fin m → ℝ → ℂ)
    (R : Ici a → (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) where
  H : ℝ → Matrix (Fin m) (Fin m) ℂ
  Hinv : ℝ → Matrix (Fin m) (Fin m) ℂ
  H' : ℝ → Matrix (Fin m) (Fin m) ℂ
  C : ℝ
  K : ℝ
  a_pos : 0 < a
  C_pos : 0 < C
  K_nonneg : 0 ≤ K
  H_derivative : ∀ r > a, ∀ i j, HasDerivAt (fun t => H t i j) (H' r i j) r
  inverse_left : ∀ r > a, Hinv r * H r = 1
  inverse_right : ∀ r > a, H r * Hinv r = 1
  H_bound : ∀ r > a, ∀ x : Fin m → ℂ, ‖(H r).mulVec x‖ ≤ C * r ^ K * ‖x‖
  Hinv_bound : ∀ r > a, ∀ x : Fin m → ℂ, ‖(Hinv r).mulVec x‖ ≤ C * r ^ K * ‖x‖
  residual_identity : ∀ r > a,
    A r * H r = H' r + H r *
      (Matrix.diagonal (fun i => dQ i r) + operatorMatrix (extend a R r))

/-- Construct an exact ray gauge by an actual Volterra correction of the
approximate gauge. The input remainder need not vanish. -/
theorem exists_exact_rayGauge {m : ℕ}
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (a : ℝ)
    (Q dQ : Fin m → ℝ → ℂ)
    (R : Ici a → (Fin m → ℂ) →L[ℂ] (Fin m → ℂ))
    (H : ApproximateRayGauge A a dQ R)
    (mode : Fin m → Fin m → Bool)
    (hQ : ∀ i, Continuous (Q i))
    (hdQ : ∀ i r, a < r → HasDerivAt (Q i) (dQ i r) r)
    (hord : ∀ j i, if mode j i then
      Antitone (fun t : Ici a => (Q i t - Q j t).re)
      else Monotone (fun t : Ici a => (Q i t - Q j t).re))
    (hdecay : ∀ j i, mode j i = true →
      Tendsto (fun r : Ici a => (Q i r - Q j r).re) atTop atBot)
    (hR : Continuous R) (hL1 : Integrable (fun s : Ici a => ‖R s‖))
    (hsmall : (∫ s : Ici a, ‖R s‖) < 1) :
    Nonempty (RayGaugeWitness A Q) := by
  obtain ⟨U, hUlim, hUode⟩ := exists_normalized_correction m a mode Q dQ
    hQ hdQ hord hdecay R hR hL1 hsmall
  obtain ⟨C, hC, htail⟩ := WasowMatrixBounds.eventually_uniform_mulVec_bounds hUlim
  obtain ⟨B, hB⟩ := eventually_atTop.mp htail
  let U' : ℝ → Matrix (Fin m) (Fin m) ℂ := fun r =>
    (Matrix.diagonal (fun k => dQ k r) + operatorMatrix (extend a R r)) * U r -
      U r * Matrix.diagonal (fun k => dQ k r)
  have ha {r : ℝ} (hr : max a B < r) : a < r := (le_max_left _ _).trans_lt hr
  have hb {r : ℝ} (hr : max a B < r) : B ≤ r := ((le_max_right _ _).trans_lt hr).le
  have hleft {r : ℝ} (hr : max a B < r) :
      ((U r)⁻¹ * H.Hinv r) * (H.H r * U r) = 1 := by
    calc
      _ = (U r)⁻¹ * (H.Hinv r * H.H r) * U r := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [H.inverse_left r (ha hr), Matrix.mul_one, (hB r (hb hr)).1]
  refine ⟨{
    T := fun r => H.H r * U r
    S := fun r => (U r)⁻¹ * H.Hinv r
    T' := fun r => H.H' r * U r + H.H r * U' r
    R := max a B
    C := H.C * C
    K := H.K
    R_pos := H.a_pos.trans_le (le_max_left _ _)
    C_pos := mul_pos H.C_pos hC
    K_nonneg := H.K_nonneg
    T_derivative := fun r hr i j => matrix_product_hasDerivAt H.H U (H.H' r) (U' r)
      (H.H_derivative r (ha hr)) (hUode r (ha hr)) i j
    inverse_left := fun _ hr => hleft hr
    inverse_right := ?_
    T_bound := ?_
    S_bound := ?_
    gauge_identity := ?_
  }⟩
  · intro r hr
    calc
      (H.H r * U r) * ((U r)⁻¹ * H.Hinv r) =
          H.H r * (U r * (U r)⁻¹) * H.Hinv r := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [(hB r (hb hr)).2.1, Matrix.mul_one, H.inverse_right r (ha hr)]
  · intro r hr x
    rw [← Matrix.mulVec_mulVec]
    calc
      ‖(H.H r).mulVec ((U r).mulVec x)‖ ≤ H.C * r ^ H.K * ‖(U r).mulVec x‖ :=
        H.H_bound r (ha hr) _
      _ ≤ H.C * r ^ H.K * (C * ‖x‖) :=
        mul_le_mul_of_nonneg_left ((hB r (hb hr)).2.2.1 x)
          (mul_nonneg H.C_pos.le (Real.rpow_nonneg (H.a_pos.trans (ha hr)).le _))
      _ = H.C * C * r ^ H.K * ‖x‖ := by ring
  · intro r hr x
    rw [← Matrix.mulVec_mulVec]
    calc
      ‖((U r)⁻¹).mulVec ((H.Hinv r).mulVec x)‖ ≤ C * ‖(H.Hinv r).mulVec x‖ :=
        (hB r (hb hr)).2.2.2 _
      _ ≤ C * (H.C * r ^ H.K * ‖x‖) :=
        mul_le_mul_of_nonneg_left (H.Hinv_bound r (ha hr) x) hC.le
      _ = H.C * C * r ^ H.K * ‖x‖ := by ring
  · intro r hr
    have hp := corrected_derivative_identity (A r)
      (H.H r) (H.H' r) (U r) (U' r) (Matrix.diagonal (fun k => dQ k r))
      (operatorMatrix (extend a R r)) (H.residual_identity r (ha hr)) rfl
    rw [hp]
    calc
      (U r)⁻¹ * H.Hinv r * A r * (H.H r * U r) -
          ((U r)⁻¹ * H.Hinv r) *
            (A r * (H.H r * U r) -
              (H.H r * U r) * Matrix.diagonal (fun k => dQ k r)) =
          ((U r)⁻¹ * H.Hinv r) * ((H.H r * U r) * Matrix.diagonal (fun k => dQ k r)) := by
        simp only [Matrix.mul_sub, Matrix.mul_assoc]
        abel
      _ = Matrix.diagonal (fun k => dQ k r) := by
        rw [← Matrix.mul_assoc, hleft hr, Matrix.one_mul]
      _ = Matrix.diagonal (fun i => deriv (Q i) r) := by
        congr 1
        funext i
        exact (hdQ i r (ha hr)).deriv.symm


theorem exists_exact_rayGauge_of_puiseux_phases {m : ℕ}
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (p : ℕ) (hp : 0 < p) (G : Fin m → Polynomial ℂ) (θ : ℝ) (ℓ : Fin p) (a₀ : ℝ) :
    ∃ a : ℝ, a₀ ≤ a ∧ 1 ≤ a ∧ ∀ b : ℝ, a ≤ b →
      ∀ R : Ici b → (Fin m → ℂ) →L[ℂ] (Fin m → ℂ),
      ApproximateRayGauge A b (fun i => deriv (phaseOnRay p (G i) θ ℓ)) R →
      Continuous R → Integrable (fun t : Ici b => ‖R t‖) →
      (∫ t : Ici b, ‖R t‖) < 1 →
      Nonempty (RayGaugeWitness A (fun i => phaseOnRay p (G i) θ ℓ)) := by
  obtain ⟨a,ha₀,ha,mode,hm⟩ := WasowPhaseRealization.exists_persistent_phase_ordering p hp G θ ℓ a₀
  refine ⟨a,ha₀,ha,?_⟩
  intro b hb R H hR hL1 hsmall
  apply exists_exact_rayGauge A b (fun i => phaseOnRay p (G i) θ ℓ)
    (fun i => deriv (phaseOnRay p (G i) θ ℓ)) R H mode
    (fun i => WasowPhaseOrdering.phase_continuous p hp (G i) θ ℓ) ?_ (hm b hb).1 (hm b hb).2 hR hL1 hsmall
  intro i r hr
  have hh := WasowPhaseOrdering.phase_hasDerivAt p (G i) θ ℓ
    (show 0 < r from lt_of_lt_of_le zero_lt_one (ha.trans (hb.trans hr.le)))
  exact hh.deriv.symm ▸ hh

open WasowPolynomialTail WasowGaugeAssembly WasowFuchsianRealization
open WasowLaurentExactAssembly
variable {m : ℕ}

local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by
    simp_rw [Matrix.linfty_opNNNorm_def]
    fun_prop

theorem exists_approximateRayGauge_of_laurent_regular
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (Rmin : ℝ)
    (Z W Z' : ℝ → Mat (m := m)) (K : ℕ) (z : FiniteGauge Z W Z' K)
    (J T S : ℝ → Mat (m := m)) (L : ℕ) (g : RegularGauge J T S L)
    (E : ℝ → Mat (m := m)) (dQ : Fin m → ℝ → ℂ)
    (heq : ∀ r > Rmin,
      A r * Z r = Z' r +
        Z r * (Matrix.diagonal (fun i => dQ i r) + J r + E r))
    (hcomm : ∀ r > Rmin, Commute (Matrix.diagonal (fun i => dQ i r)) (T r))
    (htail : SmallConjugatedTails T S E) {ε : ℝ} (hε : 0<ε) :
    ∃ R : ℝ, 1≤R ∧ Rmin≤R ∧
      Nonempty (ApproximateRayGauge A R dQ (WasowLaurentExactAssembly.tailOperator T S E R)) ∧
      Continuous (WasowLaurentExactAssembly.tailOperator T S E R) ∧
      Integrable (fun r : Ici R => ‖WasowLaurentExactAssembly.tailOperator T S E R r‖) ∧
      (∫ r : Ici R, ‖WasowLaurentExactAssembly.tailOperator T S E R r‖) < ε := by
  obtain ⟨R,hR,hlarge,hcont,hi,hsmall⟩ :=
    htail (max Rmin (max z.control.R g.control.R)) ε hε
  have hmin : Rmin≤R := (le_max_left _ _).trans hlarge
  have hzR : z.control.R≤R := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hgR : g.control.R≤R := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hzr {r : ℝ} (hr : R<r) : z.control.R<r := hzR.trans_lt hr
  have hgr {r : ℝ} (hr : R<r) : g.control.R<r := hgR.trans_lt hr
  have hrnonneg {r : ℝ} (hr : R<r) : 0≤r := zero_le_one.trans (hR.trans hr.le)
  have hext {r : ℝ} (hr : R<r) :
      operatorMatrix (WasowVolterra.extend R (WasowLaurentExactAssembly.tailOperator T S E R) r) = S r*E r*T r := by
    simp only [WasowVolterra.extend, WasowVolterra.retract, WasowLaurentExactAssembly.tailOperator,
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
  · simp only [WasowLaurentExactAssembly.tailOperator, norm_toOperator]
    change Integrable ((fun r : ℝ => ‖S r*E r*T r‖) ∘ Subtype.val)
      (Measure.comap Subtype.val volume)
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ici).mp hi.norm
  · simp only [WasowLaurentExactAssembly.tailOperator, norm_toOperator]
    have hh := integral_subtype (s := Ici R) measurableSet_Ici (fun r : ℝ => ‖S r*E r*T r‖)
    exact hh.symm ▸ hsmall

/-- Fixed Puiseux phases provide the integration modes automatically. The
actual Volterra correction produces a complete exact RayGaugeWitness from
an arbitrary finite Laurent gauge and the actual commuting regular factor. -/
theorem exists_exact_rayGauge_of_laurent_regular
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (θ Rmin : ℝ)
    (Z W Z' : ℝ → Mat (m := m)) (K : ℕ) (z : FiniteGauge Z W Z' K)
    (J T S : ℝ → Mat (m := m)) (L : ℕ) (g : RegularGauge J T S L)
    (E : ℝ → Mat (m := m))
    (p : ℕ) (hp : 0<p) (F : Fin m → Polynomial ℂ) (ℓ : Fin p)
    (heq : ∀ r > Rmin,
      A r * Z r = Z' r +
        Z r * (Matrix.diagonal (fun i => deriv (phaseOnRay p (F i) θ ℓ) r) + J r + E r))
    (hcomm : ∀ r > Rmin,
      Commute (Matrix.diagonal (fun i => deriv (phaseOnRay p (F i) θ ℓ) r)) (T r))
    (htail : SmallConjugatedTails T S E) :
    Nonempty (RayGaugeWitness A (fun i => phaseOnRay p (F i) θ ℓ)) := by
  obtain ⟨R₀,hmin,_,hrealize⟩ :=
    exists_exact_rayGauge_of_puiseux_phases A p hp F θ ℓ Rmin
  obtain ⟨R,_,hR,⟨H⟩,hcont,hL1,hsmall⟩ :=
    exists_approximateRayGauge_of_laurent_regular A R₀ Z W Z' K z J T S L g E
      (fun i => deriv (phaseOnRay p (F i) θ ℓ))
      (fun r hr => heq r (hmin.trans_lt hr))
      (fun r hr => hcomm r (hmin.trans_lt hr))
      htail (by norm_num : (0:ℝ)<1)
  exact hrealize R hR (WasowLaurentExactAssembly.tailOperator T S E R) H hcont hL1 hsmall


#print axioms exists_approximateRayGauge_of_laurent_regular
#print axioms exists_exact_rayGauge_of_laurent_regular
#print axioms exists_exact_rayGauge
#print axioms exists_exact_rayGauge_of_puiseux_phases
end CRGGeneralRayGauge
