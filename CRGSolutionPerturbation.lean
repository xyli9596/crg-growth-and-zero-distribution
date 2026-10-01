import CRGSolutionSpanning
import WasowLaurentExactAssemblyData
import WasowPhaseRealization

/-! True fundamental matrices for a perturbed rational equation, obtained
from the proved rational gauge and actual mixed Volterra solutions. -/
set_option autoImplicit false
noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Matrix.Norms.Operator
attribute [local instance] Measure.Subtype.measureSpace
namespace CRGSolutionPerturbation
open CRGNormalFormGoal WasowLaurentExactAssembly WasowGaugeAssembly
open WasowFundamental WasowRealization WasowVolterra
variable {m : ℕ}

theorem perturbed_gauge_identity
    (A P T S T' D : Matrix (Fin m) (Fin m) ℂ)
    (hTS : T*S=1) (hg : S*A*T-S*T'=D) :
    (A+P)*T=T'+T*(D+S*P*T) := by
  have hh := congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => T*M) hg
  have ht : A*T-T'=T*D := by
    simpa only [Matrix.mul_sub,←Matrix.mul_assoc,hTS,Matrix.one_mul] using hh
  calc
    (A+P)*T = (A*T-T')+T'+P*T := by noncomm_ring
    _ = T*D+T'+P*T := by rw [ht]
    _ = T'+T*(D+S*P*T) := by
      rw [Matrix.mul_add]
      simp only [←Matrix.mul_assoc,hTS]
      simp only [Matrix.one_mul]
      abel

/-- The only analytic input here is the concrete conjugated perturbation's
small-tail property. It is subsequently derived from exponential decay. -/
theorem exists_perturbed_fundamental
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (p : ℕ) (hp : 0<p)
    (G : Fin m → Polynomial ℂ) (θ : ℝ) (ℓ : Fin p)
    (H : RayGaugeWitness A θ (fun i=>phaseOnRay p (G i) θ ℓ))
    (P : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (hsmall : SmallConjugatedTails H.T H.S P) :
    ∃a : ℝ, H.R<a ∧ ∃U : ℝ → Matrix (Fin m) (Fin m) ℂ,
      Tendsto U atTop (𝓝 1) ∧
      let Y := fun r => H.T r * U r * diagonal (fun i=>Complex.exp (phaseOnRay p (G i) θ ℓ r))
      (∀r>a,∀i j, HasDerivAt (fun t=>Y t i j)
        (((coefficientOnRay A θ r+P r)*Y r) i j) r) ∧
      ∀r≥a, (Y r).det≠0 := by
  let Q := fun i=>phaseOnRay p (G i) θ ℓ
  obtain ⟨b,hb0,hb1,mode,hmode⟩ :=
    WasowPhaseRealization.exists_persistent_phase_ordering p hp G θ ℓ (H.R+1)
  obtain ⟨d,hd1,hbd,hcont,hint,hintsmall⟩ := hsmall b 1 zero_lt_one
  let R := WasowLaurentExactAssembly.tailOperator H.T H.S P d
  have hR : Continuous R :=
    continuous_toOperator.comp (continuousOn_iff_continuous_domRestrict.mp hcont)
  have hi : Integrable (fun r:Ici d=>‖R r‖) := by
    simp only [R,WasowLaurentExactAssembly.tailOperator,norm_toOperator]
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ici).mp hint.norm
  have his : (∫r:Ici d,‖R r‖)<1 := by
    simp only [R,WasowLaurentExactAssembly.tailOperator,norm_toOperator]
    have hh := integral_subtype (s:=Ici d) measurableSet_Ici (fun r:ℝ=>‖H.S r*P r*H.T r‖)
    exact hh.symm ▸ hintsmall
  have hdH : H.R<d := (lt_add_one H.R).trans_le (hb0.trans hbd)
  have hQd (i : Fin m) (r : ℝ) (hr : d<r) : HasDerivAt (Q i) (deriv (Q i) r) r := by
    have hh := WasowPhaseOrdering.phase_hasDerivAt p (G i) θ ℓ
      ((zero_lt_one.trans_le hd1).trans hr)
    exact hh.deriv.symm ▸ hh
  obtain ⟨u,_hu,hulim,hud,c,hdc,hdet⟩ := exists_fundamental_matrix m d mode Q
    (fun i=>deriv (Q i)) (fun i=>WasowPhaseOrdering.phase_continuous p hp (G i) θ ℓ)
    hQd (hmode d hbd).1 (hmode d hbd).2 R hR hi his
  refine ⟨c,hdH.trans hdc,normalizedMatrix u,hulim,?_,?_⟩
  · intro r hr i j
    have hdr : d<r := hdc.trans hr
    have hHr : H.R<r := hdH.trans hdr
    have hext : operatorMatrix (extend d R r)=H.S r*P r*H.T r := by
      simp only [WasowVolterra.extend,retract,R,WasowLaurentExactAssembly.tailOperator,max_eq_right hdr.le,operatorMatrix_toOperator]
    let F := fundamentalMatrix u Q
    have hFd : ∀i j, HasDerivAt (fun t=>F t i j)
        (((diagonal (fun i=>deriv (Q i) r)+H.S r*P r*H.T r)*F r) i j) r := by
      intro i j
      have hh := hasDerivAt_pi.mp (hud r hdr j) i
      simpa only [F,Matrix.add_mul,Matrix.add_apply,Matrix.diagonal_mul,
        ←hext,operatorMatrix_mul_apply] using hh
    have hh := matrix_product_hasDerivAt H.T F (H.T' r)
      ((diagonal (fun i=>deriv (Q i) r)+H.S r*P r*H.T r)*F r)
      (H.T_derivative r hHr) hFd i j
    have he := perturbed_gauge_identity (coefficientOnRay A θ r) (P r)
      (H.T r) (H.S r) (H.T' r) (diagonal (fun i=>deriv (Q i) r))
      (H.inverse_right r hHr) (H.gauge_identity r hHr)
    have he' : H.T' r*F r+H.T r*((diagonal (fun i=>deriv (Q i) r)+
        H.S r*P r*H.T r)*F r) = (coefficientOnRay A θ r+P r)*(H.T r*F r) := by
      rw [←Matrix.mul_assoc (H.T r),←Matrix.add_mul,←he,Matrix.mul_assoc]
    rw [he'] at hh
    simpa only [F,fundamentalMatrix,Matrix.mul_assoc,Q] using hh
  · intro r hr
    have hHr : H.R<r := (hdH.trans hdc).trans_le hr
    have ht := Matrix.det_ne_zero_of_left_inverse (H.inverse_left r hHr)
    have hf := (hdet r hr).2
    simpa only [fundamentalMatrix,Matrix.det_mul,Q,mul_assoc] using mul_ne_zero ht hf

#print axioms perturbed_gauge_identity
#print axioms exists_perturbed_fundamental
end CRGSolutionPerturbation
