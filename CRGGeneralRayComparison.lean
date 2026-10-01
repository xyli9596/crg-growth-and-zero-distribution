import CRGGeneralRayGauge
import CRGSolutionPerturbation
import CRGSolutionPerturbationTail
import CRGRayComparisonLog

/-! Actual fundamental solutions and logarithmic comparison for arbitrary
matrix coefficients on a ray. All witnesses below retain true inverse
identities and two-sided polynomial bounds. -/
set_option autoImplicit false
noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Matrix.Norms.Operator
attribute [local instance] Measure.Subtype.measureSpace
namespace CRGGeneralRayComparison
open CRGNormalFormGoal WasowLaurentExactAssembly WasowGaugeAssembly
open WasowFundamental WasowRealization WasowVolterra CRGRayComparisonLog
open CRGSolutionPerturbation
variable {m : ℕ}

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin m → ℂ))

local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by
    simp_rw [Matrix.linfty_opNNNorm_def]
    fun_prop

theorem gauge_continuousOn (A : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (q : Fin m → ℝ → ℂ) (H : CRGGeneralRayGauge.RayGaugeWitness A q) :
    ContinuousOn H.T (Ioi H.R) ∧ ContinuousOn H.S (Ioi H.R) := by
  have ht : ContinuousOn H.T (Ioi H.R) := by
    intro r hr
    exact (continuousAt_pi.mpr (fun i=>continuousAt_pi.mpr
      (fun j=>(H.T_derivative r hr i j).continuousAt))).continuousWithinAt
  refine ⟨ht,?_⟩
  have hi : ContinuousOn (fun r=>(H.T r)⁻¹) (Ioi H.R) := by
    intro r hr
    apply (continuousAt_matrix_inv (H.T r) ?_).comp_continuousWithinAt (ht r hr)
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (Matrix.det_ne_zero_of_left_inverse (H.inverse_left r hr))
  apply hi.congr
  intro r hr
  exact (Matrix.inv_eq_left_inv (H.inverse_left r hr)).symm

theorem gauge_operator_norm_bound (A : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (q : Fin m → ℝ → ℂ) (H : CRGGeneralRayGauge.RayGaugeWitness A q) {r : ℝ} (hr : H.R<r) :
    ‖H.T r‖≤H.C*r^H.K ∧ ‖H.S r‖≤H.C*r^H.K := by
  have hnon : 0≤H.C*r^H.K := mul_nonneg H.C_pos.le
    (Real.rpow_nonneg (H.R_pos.trans hr).le _)
  constructor
  · rw [←norm_toOperator]
    exact ContinuousLinearMap.opNorm_le_bound _ hnon (H.T_bound r hr)
  · rw [←norm_toOperator]
    exact ContinuousLinearMap.opNorm_le_bound _ hnon (H.S_bound r hr)

/-- An actual continuous exponentially decreasing matrix perturbation supplies
all the analytic hypotheses of the mixed Volterra construction. -/
theorem smallConjugatedTails_of_exponential
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (q : Fin m → ℝ → ℂ) (H : CRGGeneralRayGauge.RayGaugeWitness A q)
    (P : ℝ → Matrix (Fin m) (Fin m) ℂ) (a B J c : ℝ)
    (hP : ContinuousOn P (Ioi a)) (hB : 0<B) (hJ : 0≤J) (hc : 0<c)
    (hb : ∀r>a, ‖P r‖≤B*(r^J*Real.exp (-c*r))) :
    SmallConjugatedTails H.T H.S P := by
  obtain ⟨ht,hs⟩ := gauge_continuousOn A q H
  intro Rmin ε hε
  let d := max 1 (max (H.R+1) (max (a+1) Rmin))
  have hd1 : 1≤d := le_max_left ..
  have hdH : H.R<d := (lt_add_one H.R).trans_le ((le_max_left _ _).trans (le_max_right _ _))
  have hda : a<d := (lt_add_one a).trans_le
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hdmin : Rmin≤d := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hcont : ContinuousOn (fun r=>H.S r*P r*H.T r) (Ici d) :=
    ((hs.mono (fun _ hr=>hdH.trans_le hr)).mul
      (hP.mono (fun _ hr=>hda.trans_le hr))).mul (ht.mono (fun _ hr=>hdH.trans_le hr))
  let K := H.K+J+H.K
  let C := H.C*B*H.C
  have hK : -1<K := by dsimp [K]; have := H.K_nonneg; linarith
  have hbound (r:ℝ) (hr:d<r) :
      ‖H.S r*P r*H.T r‖≤C*(r^K*Real.exp (-c*r)) := by
    have hrp : 0<r := (zero_lt_one.trans_le hd1).trans hr
    have hHr : H.R<r := hdH.trans hr
    obtain ⟨htr,hsr⟩ := gauge_operator_norm_bound A q H hHr
    have hCr : 0≤H.C*r^H.K := mul_nonneg H.C_pos.le (Real.rpow_nonneg hrp.le _)
    calc
      _ ≤ (‖H.S r‖*‖P r‖)*‖H.T r‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ((H.C*r^H.K)*(B*(r^J*Real.exp (-c*r))))*(H.C*r^H.K) :=
        mul_le_mul (mul_le_mul hsr (hb r (hda.trans hr)) (norm_nonneg _) hCr)
          htr (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [C,K]; rw [Real.rpow_add hrp,Real.rpow_add hrp]; ring
  have hint : IntegrableOn (fun r=>H.S r*P r*H.T r) (Ioi d) := by
    apply CRGProgress.perturbation_integrable _ K c C d hK hc (by linarith) 
      ((hcont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun r hr=>hbound r hr)
  have hlim : Tendsto (fun b:ℝ=>∫r in Ici b,‖H.S r*P r*H.T r‖) atTop (𝓝 0) :=
    tendsto_integral_Ici_zero tendsto_id
  obtain ⟨e,he⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  let b := max d e
  have hdb : d≤b := le_max_left ..
  refine ⟨b,hd1.trans hdb,hdmin.trans hdb,hcont.mono (Ici_subset_Ici.mpr hdb),?_,
    he b (le_max_right ..)⟩
  rw [IntegrableOn, ←restrict_Ioi_eq_restrict_Ici]
  exact hint.mono_set (Ioi_subset_Ioi hdb)

theorem exists_perturbed_fundamental
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (p : ℕ) (hp : 0<p)
    (G : Fin m → Polynomial ℂ) (θ : ℝ) (ℓ : Fin p)
    (H : CRGGeneralRayGauge.RayGaugeWitness A (fun i=>phaseOnRay p (G i) θ ℓ))
    (P : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (hsmall : SmallConjugatedTails H.T H.S P) :
    ∃a : ℝ, H.R<a ∧ ∃U : ℝ → Matrix (Fin m) (Fin m) ℂ,
      Tendsto U atTop (𝓝 1) ∧
      let Y := fun r => H.T r * U r * diagonal (fun i=>Complex.exp (phaseOnRay p (G i) θ ℓ r))
      (∀r>a,∀i j, HasDerivAt (fun t=>Y t i j)
        (((A r+P r)*Y r) i j) r) ∧
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
    have he := perturbed_gauge_identity (A r) (P r)
      (H.T r) (H.S r) (H.T' r) (diagonal (fun i=>deriv (Q i) r))
      (H.inverse_right r hHr) (H.gauge_identity r hHr)
    have he' : H.T' r*F r+H.T r*((diagonal (fun i=>deriv (Q i) r)+
        H.S r*P r*H.T r)*F r) = (A r+P r)*(H.T r*F r) := by
      rw [←Matrix.mul_assoc (H.T r),←Matrix.add_mul,←he,Matrix.mul_assoc]
    rw [he'] at hh
    simpa only [F,fundamentalMatrix,Matrix.mul_assoc,Q] using hh
  · intro r hr
    have hHr : H.R<r := (hdH.trans hdc).trans_le hr
    have ht := Matrix.det_ne_zero_of_left_inverse (H.inverse_left r hHr)
    have hf := (hdet r hr).2
    simpa only [fundamentalMatrix,Matrix.det_mul,Q,mul_assoc] using mul_ne_zero ht hf

theorem represented_scalar_log_comparison
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (p : ℕ) (hp : 0<p)
    (G : Fin m → Polynomial ℂ) (θ : ℝ) (ℓ : Fin p)
    (H : CRGGeneralRayGauge.RayGaugeWitness A (fun i=>phaseOnRay p (G i) θ ℓ))
    (U : ℝ → Matrix (Fin m) (Fin m) ℂ) (hU : Tendsto U atTop (𝓝 1))
    (c : Fin m → ℂ) (hc : c≠0) (x : ℝ → Fin m → ℂ) (f : ℝ → ℂ)
    (hx : ∀ᶠr in atTop, x r = (H.T r).mulVec ((U r).mulVec
      (exponentialVector (fun i=>phaseOnRay p (G i) θ ℓ r) c)))
    (hf : ∀ᶠr in atTop, f r≠0)
    (D J : ℝ) (hD : 0<D) (hJ : 0≤J)
    (hjet : ∀ᶠr in atTop, ‖f r‖≤‖x r‖ ∧ ‖x r‖≤D*r^J*‖f r‖) :
    ∃j : Fin m, c j≠0 ∧ ∃M : ℝ, 0<M ∧ ∀ᶠr in atTop,
      |Real.log ‖f r‖-(phaseOnRay p (G j) θ ℓ r).re|≤M*Real.log r := by
  obtain ⟨j,hcj,hmax⟩ := CRGRayComparisonOrder.exists_dominant_phase p hp G θ ℓ c hc
  obtain ⟨B,hB,hbounds⟩ := WasowMatrixBounds.eventually_uniform_mulVec_bounds hU
  let Bu := H.C*B*‖c‖
  let Bl := B*H.C*D/‖c j‖
  let K := H.K+J
  have hC := H.C_pos
  have hcpos : 0<‖c‖ := norm_pos_iff.mpr hc
  have hcjpos : 0<‖c j‖ := norm_pos_iff.mpr hcj
  have hBu : 0<Bu := by dsimp [Bu]; positivity
  have hBl : 0<Bl := by dsimp [Bl]; positivity
  let M := |Real.log Bu|+|Real.log Bl|+K+1
  have hK : 0≤K := add_nonneg H.K_nonneg hJ
  refine ⟨j,hcj,M,by dsimp [M]; positivity,?_⟩
  have hlog : ∀ᶠr:ℝ in atTop, 1≤Real.log r :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hx,hf,hjet,hmax,hbounds,eventually_gt_atTop H.R,
    eventually_ge_atTop (1:ℝ),hlog] with r hxr hfr hjr hmr hbr hr hr1 hlr
  have hrp : 0<r := zero_lt_one.trans_le hr1
  obtain ⟨hu,hl⟩ := represented_solution_exponential_bounds
    (H.T r) (H.S r) (U r) ((U r)⁻¹)
    (fun i=>phaseOnRay p (G i) θ ℓ r) c j H.C B r H.K H.C_pos hB hrp
    (H.inverse_left r hr) hbr.1 (H.T_bound r hr) (H.S_bound r hr)
    hbr.2.2.1 hbr.2.2.2 hmr
  rw [←hxr] at hu hl
  have hpup : r^H.K ≤ r^K := Real.rpow_le_rpow_of_exponent_le hr1 (by dsimp [K]; linarith)
  have hu' : ‖f r‖ ≤ Bu*r^K*Real.exp (phaseOnRay p (G j) θ ℓ r).re :=
    hjr.1.trans (hu.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpup hBu.le) (Real.exp_pos _).le))
  have hl' : Real.exp (phaseOnRay p (G j) θ ℓ r).re ≤ Bl*r^K*‖f r‖ := by
    have hh := hl.trans (mul_le_mul_of_nonneg_left hjr.2 (by positivity : 0≤(B*H.C)*r^H.K))
    have he : (B*H.C)*r^H.K*(D*r^J*‖f r‖) =
        (Bl*r^K*‖f r‖)*‖c j‖ := by
      dsimp [Bl,K]
      rw [Real.rpow_add hrp]
      field_simp
    rw [he] at hh
    exact (mul_le_mul_iff_left₀ hcjpos).mp (by simpa only [mul_comm] using hh)
  have hh := log_of_polynomial_exponential_bounds ‖f r‖
    (phaseOnRay p (G j) θ ℓ r).re r Bu Bl K (norm_pos_iff.mpr hfr) hr1 hBu hBl hK hu' hl'
  refine hh.trans ?_
  have hc0 : 0≤|Real.log Bu|+|Real.log Bl| := by positivity
  have hh' := mul_le_mul_of_nonneg_left hlr hc0
  dsimp [M]
  nlinarith

theorem ray_comparison
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (p : ℕ) (hp : 0<p)
    (G : Fin m → Polynomial ℂ) (θ : ℝ) (ℓ : Fin p)
    (H : CRGGeneralRayGauge.RayGaugeWitness A (fun i=>phaseOnRay p (G i) θ ℓ))
    (P : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (hsmall : SmallConjugatedTails H.T H.S P) (a : ℝ)
    (hcoef : ContinuousOn (fun r=>A r+P r) (Ioi a))
    (x : ℝ → Fin m → ℂ) (f : ℝ → ℂ)
    (hx : ∀r>a, HasDerivAt x ((A r+P r).mulVec (x r)) r)
    (hf : ∀ᶠr in atTop, f r≠0)
    (D K : ℝ) (hD : 0<D) (hK : 0≤K)
    (hjet : ∀ᶠr in atTop, ‖f r‖≤‖x r‖ ∧ ‖x r‖≤D*r^K*‖f r‖) :
    ∃j : Fin m, ∃M : ℝ, 0<M ∧ ∀ᶠr in atTop,
      |Real.log ‖f r‖-(phaseOnRay p (G j) θ ℓ r).re|≤M*Real.log r := by
  obtain ⟨b,hHb,U,hU,hY,hdet⟩ :=
    exists_perturbed_fundamental A p hp G θ ℓ H P hsmall
  let Y := fun r=>H.T r*U r*diagonal (fun i=>Complex.exp (phaseOnRay p (G i) θ ℓ r))
  have hxy : ∀ᶠr in atTop,x r≠0 := by
    filter_upwards [hf,hjet] with r hfr hjr
    intro he
    have hh := hjr.1
    rw [he,norm_zero] at hh
    exact hfr (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  obtain ⟨e,he⟩ := eventually_atTop.mp hxy
  let b' := max (max a b) e+1
  have hab' : max a b<b' := by dsimp [b']; linarith [le_max_left (max a b) e]
  have hbb' : b<b' := (le_max_right a b).trans_lt hab'
  have heb' : e≤b' := by dsimp [b']; linarith [le_max_right (max a b) e]
  obtain ⟨v,hv,hrep⟩ := CRGSolutionSpanning.exists_nonzero_coefficients
    (fun r=>A r+P r) Y x (max a b) b' hab' (hcoef.mono (fun r hr=>(le_max_left a b).trans_lt hr))
    (fun r hr=>hY r ((le_max_right a b).trans_lt hr))
    (fun r hr=>hx r ((le_max_left a b).trans_lt hr)) (hdet b' hbb'.le) (he b' heb')
  have hrep' : ∀ᶠr in atTop,x r=(H.T r).mulVec ((U r).mulVec
      (CRGRayComparisonLog.exponentialVector
        (fun i=>phaseOnRay p (G i) θ ℓ r) v)) := by
    filter_upwards [eventually_ge_atTop b'] with r hr
    have he : (diagonal (fun i=>Complex.exp (phaseOnRay p (G i) θ ℓ r))).mulVec v =
        CRGRayComparisonLog.exponentialVector (fun i=>phaseOnRay p (G i) θ ℓ r) v :=
      funext (fun i=>Matrix.mulVec_diagonal _ _ i)
    simpa only [Y,←Matrix.mulVec_mulVec,he] using hrep r hr
  obtain ⟨j,_hj,M,hM,hlog⟩ := represented_scalar_log_comparison
    A p hp G θ ℓ H U hU v hv x f hrep' hf D K hD hK hjet
  exact ⟨j,M,hM,hlog⟩

#print axioms gauge_continuousOn
#print axioms gauge_operator_norm_bound
#print axioms smallConjugatedTails_of_exponential
#print axioms exists_perturbed_fundamental
#print axioms represented_scalar_log_comparison
#print axioms ray_comparison
end CRGGeneralRayComparison
