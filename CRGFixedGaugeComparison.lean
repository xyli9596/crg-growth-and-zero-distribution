import CRGRayComparison

/-! Ray comparison retains a prescribed, already constructed finite phase family. -/
set_option autoImplicit false
noncomputable section
open Filter Set Matrix
open scoped Topology Matrix.Norms.Operator
namespace CRGFixedGaugeComparison
open CRGNormalFormGoal CRGRayComparison
variable {m : ℕ}

theorem of_fixed_normal_form
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (p : ℕ) (hp : 0<p) (G : Fin m→Polynomial ℂ)
    (hNF : ∀θ:ℝ, Nonempty (RayGaugeWitness A θ
      (fun i=>phaseOnRay p (G i) θ ⟨0,hp⟩))) :
      ∀θ:ℝ, ∀P:ℝ→Matrix (Fin m) (Fin m) ℂ,
      ∀a B J c:ℝ, ContinuousOn P (Ioi a) → 0<B → 0≤J → 0<c →
      (∀r>a,‖P r‖≤B*(r^J*Real.exp (-c*r))) →
      ∀x:ℝ→Fin m→ℂ, ∀f:ℝ→ℂ,
      (∀r>a,HasDerivAt x ((coefficientOnRay A θ r+P r).mulVec (x r)) r) →
      (∀ᶠr in atTop,f r≠0) →
      ∀D K:ℝ, 0<D → 0≤K →
      (∀ᶠr in atTop,‖f r‖≤‖x r‖ ∧ ‖x r‖≤D*r^K*‖f r‖) →
      ∃j:Fin m, ∃M:ℝ, 0<M ∧ ∀ᶠr in atTop,
        |Real.log ‖f r‖-(phaseOnRay p (G j) θ ⟨0,hp⟩ r).re|≤M*Real.log r := by
  intro θ P a B J c hP hB hJ hc hb x f hx hf D K hD hK hjet
  obtain ⟨H⟩ := hNF θ
  have hs := CRGSolutionPerturbationTail.smallConjugatedTails_of_exponential
    A θ _ H P a B J c hP hB hJ hc hb
  obtain ⟨b,hHb,U,hU,hY,hdet⟩ :=
    CRGSolutionPerturbation.exists_perturbed_fundamental A p hp G θ ⟨0,hp⟩ H P hs
  let Y := fun r=>H.T r*U r*diagonal (fun i=>Complex.exp (phaseOnRay p (G i) θ ⟨0,hp⟩ r))
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
  have hcoef : ContinuousOn (fun r=>coefficientOnRay A θ r+P r) (Ioi (max a b)) := by
    apply ContinuousOn.add
    · exact (coefficientOnRay_continuousOn A θ H.R H.pole_free).mono
        (fun r hr=>hHb.trans ((le_max_right a b).trans_lt hr))
    · exact hP.mono (fun r hr=>(le_max_left a b).trans_lt hr)
  obtain ⟨v,hv,hrep⟩ := CRGSolutionSpanning.exists_nonzero_coefficients
    (fun r=>coefficientOnRay A θ r+P r) Y x (max a b) b' hab' hcoef
    (fun r hr=>hY r ((le_max_right a b).trans_lt hr))
    (fun r hr=>hx r ((le_max_left a b).trans_lt hr)) (hdet b' hbb'.le) (he b' heb')
  have hrep' : ∀ᶠr in atTop,x r=(H.T r).mulVec ((U r).mulVec
      (CRGRayComparisonLog.exponentialVector
        (fun i=>phaseOnRay p (G i) θ ⟨0,hp⟩ r) v)) := by
    filter_upwards [eventually_ge_atTop b'] with r hr
    have he : (diagonal (fun i=>Complex.exp (phaseOnRay p (G i) θ ⟨0,hp⟩ r))).mulVec v =
        CRGRayComparisonLog.exponentialVector (fun i=>phaseOnRay p (G i) θ ⟨0,hp⟩ r) v :=
      funext (fun i=>Matrix.mulVec_diagonal _ _ i)
    simpa only [Y,←Matrix.mulVec_mulVec,he] using hrep r hr
  obtain ⟨j,_hj,M,hM,hlog⟩ := CRGRayComparisonLog.represented_scalar_log_comparison
    A p hp G θ ⟨0,hp⟩ H U hU v hv x f hrep' hf D K hD hK hjet
  exact ⟨j,M,hM,hlog⟩

#print axioms of_fixed_normal_form
end CRGFixedGaugeComparison
