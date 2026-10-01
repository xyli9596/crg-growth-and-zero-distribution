import CRGRayComparisonLog
import CRGSolutionPerturbation
import CRGSolutionPerturbationTail
import WasowRationalNormalForm

/-! The ray comparison theorem for a scalar component of a perturbed rational
system. Every normal form, correction, fundamental matrix, and solution
coefficient vector is constructed; none is an input assumption. -/
set_option autoImplicit false
noncomputable section
open Filter Set Matrix
open scoped Topology Matrix.Norms.Operator
namespace CRGRayComparison
open CRGNormalFormGoal
variable {m : ℕ}

theorem coefficientOnRay_continuousOn
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ a : ℝ)
    (hp : ∀r>a,∀i j,(A i j).denom.eval (ray θ r)≠0) :
    ContinuousOn (coefficientOnRay A θ) (Ioi a) := by
  have hr : Continuous (ray θ) := Complex.continuous_ofReal.mul continuous_const
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  change ContinuousOn (fun r=>Complex.exp ((θ:ℂ)*Complex.I)*
    ((A i j).num.eval (ray θ r)/(A i j).denom.eval (ray θ r))) (Ioi a)
  exact continuousOn_const.mul (((A i j).num.continuous.comp hr).continuousOn.div
    ((A i j).denom.continuous.comp hr).continuousOn (fun r hr=>hp r hr i j))

/-- Given the actual ray equation and polynomial scalar-to-jet comparison,
the finite Puiseux phase family of the rational matrix controls its scalar
component on every ray. The phase family is fixed before the angle is chosen. -/
theorem exists_fixed_phase_comparison
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) :
    ∃p:ℕ, ∃hp:0<p, ∃G:Fin m→Polynomial ℂ,
      (∀i,(G i).coeff 0=0) ∧
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
  obtain ⟨p,hp,G,hG,hNF⟩ := WasowRationalNormalForm.exists_fixed_phase_normal_form A
  refine ⟨p,hp,G,hG,?_⟩
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

#print axioms coefficientOnRay_continuousOn
#print axioms exists_fixed_phase_comparison
end CRGRayComparison
