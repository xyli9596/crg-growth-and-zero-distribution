import CRGCompanion

/-! Scalar ray comparison from an actual entire solution of a perturbed
rational scalar ODE. All jet, gauge, fundamental-solution, and dominance
bridges are proved; the finite phase family precedes the ray direction. -/
set_option autoImplicit false
noncomputable section
open Filter Set Matrix
open scoped Topology Matrix.Norms.Operator
namespace CRGCompanionComparison
open CRGNormalFormGoal CRGCompanion
variable {m : ℕ}

/-- Manuscript ray-comparison lemma in solved scalar-equation form. No
solution representation, normal form, or phase selection is assumed. -/
theorem scalar_ray_comparison (a : Fin (m+1)→RatFunc ℂ) :
    ∃p:ℕ, ∃hp:0<p, ∃G:Fin (m+1)→Polynomial ℂ,
      (∀i,(G i).coeff 0=0) ∧
      ∀θ:ℝ, ∀f:ℂ→ℂ, Differentiable ℂ f →
      ∀ε:ℝ→ℂ, ∀R B J c:ℝ,
      ContinuousOn ε (Ioi R) → 0<B → 0≤J → 0<c →
      (∀r>R,‖ε r‖≤B*(r^J*Real.exp (-c*r))) →
      (∀r>R,iteratedDeriv (m+1) f (ray θ r)=
        (∑j:Fin (m+1),RatFunc.eval (RingHom.id ℂ) (ray θ r) (a j)*
          iteratedDeriv j.val f (ray θ r))+ε r*f (ray θ r)) →
      (∀ᶠr in atTop,f (ray θ r)≠0) →
      ∀D K:ℝ, 0<D → 0≤K →
      (∀ᶠr in atTop,∀k:ℕ,1≤k→k<m+1→
        ‖iteratedDeriv k f (ray θ r)/f (ray θ r)‖≤D*r^K) →
      ∃j:Fin (m+1), ∃M:ℝ, 0<M ∧ ∀ᶠr in atTop,
        |Real.log ‖f (ray θ r)‖-(phaseOnRay p (G j) θ ⟨0,hp⟩ r).re|≤M*Real.log r := by
  obtain ⟨p,hp,G,hG,h⟩ := CRGRayComparison.exists_fixed_phase_comparison (companion a)
  refine ⟨p,hp,G,hG,?_⟩
  intro θ f hf ε R B J c hε hB hJ hc hb heq hnon D K hD hK hquot
  apply h θ (perturbation θ ε) R B J c (perturbation_continuousOn θ R ε hε)
    hB hJ hc (fun r hr=>(norm_perturbation_le θ r ε).trans (hb r hr))
    (jet f θ) (fun r=>f (ray θ r))
    (fun r hr=>jet_hasDerivAt_of_scalar_equation a f hf θ r ε (heq r hr))
    hnon (D+1) K (by linarith) hK
  filter_upwards [hnon,hquot,eventually_ge_atTop (1:ℝ)] with r hfr hqr hr
  exact jet_polynomial_comparison f θ r D K hr hD hK hfr hqr

#print axioms scalar_ray_comparison
end CRGCompanionComparison
