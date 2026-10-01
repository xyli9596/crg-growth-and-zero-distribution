import CRGGroupHighest
import CRGCompanionComparison

/-! A fixed finite phase family for one nonzero polynomial differential group.
The zero-order alternative is excluded by the actual small residual; every
positive-order alternative uses the proved scalar rational ray comparison. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace CRGPolynomialGroupComparison
open CRGNormalFormGoal CRGGroupHighest

theorem group_ray_comparison {n : ℕ} (b : Fin (n+1)→Polynomial ℂ) (H : Highest b) :
    ∃d p:ℕ, ∃hp:0<p, ∃G:Fin (d+1)→Polynomial ℂ,
      (∀i,(G i).coeff 0=0) ∧
      ∀θ:ℝ, ∀f:ℂ→ℂ, Differentiable ℂ f →
      ∀ε:ℝ→ℂ, ∀R B J c:ℝ,
      ContinuousOn ε (Ioi R) → 0<B → 0≤J → 0<c →
      (∀r>R,‖ε r‖≤B*(r^J*Real.exp (-c*r))) →
      (∀r>R,(b H.index).eval (ray θ r)≠0 ∧ ε r≠1 ∧
        (∑j,(b j).eval (ray θ r)*iteratedDeriv j.val f (ray θ r)) /
          (b H.index).eval (ray θ r)=ε r*f (ray θ r)) →
      (∀ᶠr in atTop,f (ray θ r)≠0) →
      ∀D K:ℝ, 0<D → 0≤K →
      (∀ᶠr in atTop,∀k:ℕ,1≤k→k≤n→
        ‖iteratedDeriv k f (ray θ r)/f (ray θ r)‖≤D*r^K) →
      ∃j:Fin (d+1), ∃M:ℝ, 0<M ∧ ∀ᶠr in atTop,
        |Real.log ‖f (ray θ r)‖-(phaseOnRay p (G j) θ ⟨0,hp⟩ r).re|≤M*Real.log r := by
  classical
  cases hm : H.index.val with
  | zero =>
    refine ⟨0,1,by omega,fun _=>0,by simp,?_⟩
    intro θ f _hf ε R _B _J _c _hcont _hB _hJ _hc _hbound heq hnon D K _hD _hK _hquot
    obtain ⟨r,hfr,hr⟩ := (hnon.and (eventually_gt_atTop R)).exists
    obtain ⟨hbr,hε,her⟩ := heq r hr
    rw [quotient_eq_function_of_order_zero H hm f hbr] at her
    have hεone : ε r=1 := mul_right_cancel₀ hfr (by simpa using her.symm)
    exact (hε hεone).elim
  | succ m =>
    let a : Fin (m+1)→RatFunc ℂ := positiveCoeff H hm
    obtain ⟨p,hp,G,hG,hcompare⟩ := CRGCompanionComparison.scalar_ray_comparison a
    refine ⟨m,p,hp,G,hG,?_⟩
    intro θ f hf ε R B J c hcont hB hJ hc hbound heq hnon D K hD hK hquot
    refine hcompare θ f hf ε R B J c hcont hB hJ hc hbound ?_ hnon D K hD hK ?_
    · intro r hr
      obtain ⟨hdr,_hε,her⟩ := heq r hr
      exact positive_reduced_differential_equation H hm f (ray θ r) (ε r) hdr her
    · filter_upwards [hquot] with r hr
      intro k hk hkm
      exact hr k hk (by have hh:=H.index.isLt; omega)

#print axioms group_ray_comparison
end CRGPolynomialGroupComparison
