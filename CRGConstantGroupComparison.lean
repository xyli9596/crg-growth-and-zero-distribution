import CRGFixedGaugeComparison
import WasowConstantLinearGauge
import CRGPolynomialGroupComparison

/-! Constant coefficient groups retain a finite family of linear phases. -/
set_option autoImplicit false
noncomputable section
open Filter Set Matrix Polynomial
open scoped Topology BigOperators Matrix.Norms.Operator
namespace CRGConstantGroupComparison
open CRGNormalFormGoal CRGCompanion CRGGroupHighest
variable {m : ℕ}

theorem scalar_constant_comparison (a : Fin (m+1)→RatFunc ℂ)
    (ha : ∀j, ∃c:ℂ, a j=algebraMap ℂ (RatFunc ℂ) c) :
    ∃G:Fin (m+1)→Polynomial ℂ,
      (∀i,(G i).coeff 0=0) ∧ (∀i,(G i).natDegree≤1) ∧
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
        |Real.log ‖f (ray θ r)‖-(phaseOnRay 1 (G j) θ 0 r).re|≤M*Real.log r := by
  classical
  choose c hc using ha
  let M : Matrix (Fin (m+1)) (Fin (m+1)) ℂ :=
    fun i j => Fin.lastCases (c j) (fun k => if j=k.succ then 1 else 0) i
  have hM : companion a = WasowGaugeComposition.constantMatrix M := by
    ext i j
    change companion a i j = algebraMap ℂ (RatFunc ℂ) (M i j)
    induction i using Fin.lastCases with
    | last => simp [companion, M, hc]
    | cast k => simp [companion, M, apply_ite]
  obtain ⟨μ,hμ⟩ := WasowConstantLinearGauge.constant_linear_normal_form M
  let G : Fin (m+1)→Polynomial ℂ := fun i => C (μ i)*X
  have hNF : ∀θ:ℝ, Nonempty (RayGaugeWitness (companion a) θ
      (fun i=>phaseOnRay 1 (G i) θ 0)) := by
    intro θ
    simpa only [hM] using hμ θ
  have h := CRGFixedGaugeComparison.of_fixed_normal_form (companion a) 1 (by omega) G hNF
  refine ⟨G, by intro i; simp [G], ?_, ?_⟩
  · intro i
    exact (Polynomial.natDegree_mul_le).trans (by simp)
  · intro θ f hf ε R B J c hε hB hJ hc hb heq hnon D K hD hK hquot
    apply h θ (perturbation θ ε) R B J c (perturbation_continuousOn θ R ε hε)
      hB hJ hc (fun r hr=>(norm_perturbation_le θ r ε).trans (hb r hr))
      (jet f θ) (fun r=>f (ray θ r))
      (fun r hr=>jet_hasDerivAt_of_scalar_equation a f hf θ r ε (heq r hr))
      hnon (D+1) K (by linarith) hK
    filter_upwards [hnon,hquot,eventually_ge_atTop (1:ℝ)] with r hfr hqr hr
    exact jet_polynomial_comparison f θ r D K hr hD hK hfr hqr

theorem group_constant_comparison {n : ℕ} (b : Fin (n+1)→Polynomial ℂ) (H : Highest b)
    (hb : ∀j, b j=C ((b j).coeff 0)) :
    ∃d:ℕ, ∃G:Fin (d+1)→Polynomial ℂ,
      (∀i,(G i).coeff 0=0) ∧ (∀i,(G i).natDegree≤1) ∧
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
        |Real.log ‖f (ray θ r)‖-(phaseOnRay 1 (G j) θ 0 r).re|≤M*Real.log r := by
  classical
  cases hm : H.index.val with
  | zero =>
    refine ⟨0,fun _=>0,by simp,by simp,?_⟩
    intro θ f _hf ε R _B _J _c _hcont _hB _hJ _hc _hbound heq hnon D K _hD _hK _hquot
    obtain ⟨r,hfr,hr⟩ := (hnon.and (eventually_gt_atTop R)).exists
    obtain ⟨hbr,hε,her⟩ := heq r hr
    rw [quotient_eq_function_of_order_zero H hm f hbr] at her
    have hεone : ε r=1 := mul_right_cancel₀ hfr (by simpa using her.symm)
    exact (hε hεone).elim
  | succ m =>
    let a : Fin (m+1)→RatFunc ℂ := positiveCoeff H hm
    have ha : ∀j, ∃c:ℂ, a j=algebraMap ℂ (RatFunc ℂ) c := by
      intro j
      unfold a positiveCoeff rationalCoeff
      rw [hb H.index, hb (lowerIndex H.index (Fin.cast hm.symm j))]
      exact ⟨-((b (lowerIndex H.index (Fin.cast hm.symm j))).coeff 0) /
        ((b H.index).coeff 0), by simp [map_div₀]⟩
    obtain ⟨G,hG,hdeg,hcompare⟩ := scalar_constant_comparison a ha
    refine ⟨m,G,hG,hdeg,?_⟩
    intro θ f hf ε R B J c hcont hB hJ hc hbound heq hnon D K hD hK hquot
    refine hcompare θ f hf ε R B J c hcont hB hJ hc hbound ?_ hnon D K hD hK ?_
    · intro r hr
      obtain ⟨hdr,_hε,her⟩ := heq r hr
      exact positive_reduced_differential_equation H hm f (ray θ r) (ε r) hdr her
    · filter_upwards [hquot] with r hr
      intro k hk hkm
      exact hr k hk (by have hh:=H.index.isLt; omega)

#print axioms scalar_constant_comparison
#print axioms group_constant_comparison
end CRGConstantGroupComparison
