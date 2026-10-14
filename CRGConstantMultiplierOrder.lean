import CRGCollectedResidual
import CRGConstantGroupComparison
import CRGLinearPhaseEndgame

/-! Constant multipliers imply exact order one, finite positive type and CRG.
The proof uses actual dominant-group residuals and linear ray phases only. -/
set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory Polynomial
open scoped Topology BigOperators
namespace CRGConstantMultiplierOrder
open CRGNormalFormGoal CRGCollectedEquation CRGCollectedResidual
open CRGExponentialCoefficients CRGGroupHighest

theorem of_collected_constant_equation {n : ℕ} {f : ℂ→ℂ}
    (E : CollectedEquation n f)
    (hc : ∀q∈E.exponents,∀j,E.coeff q j=C ((E.coeff q j).coeff 0))
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬∃P:Polynomial ℂ,∀z:ℂ,f z=P.eval z) :
    CRGOrder.IsOrder f 1 ∧ LevinGrowth.FinitePositiveType f 1 ∧
      LevinGrowth.ManuscriptCRG f 1 := by
  classical
  let : Nonempty E.exponents := E.nonempty.to_subtype
  let H : (q:E.exponents)→Highest (E.coeff q.val) := fun q=>
    Classical.choice (exists_highest (E.coeff q.val) (E.nonzero_group q.val q.property))
  choose d G hG hdeg hcompare using fun q:E.exponents=>
    CRGConstantGroupComparison.group_constant_comparison (E.coeff q.val) (H q)
      (hc q.val q.property)
  let ι := (q:E.exponents) × Fin (d q+1)
  apply CRGLinearPhaseEndgame.order_one_of_linear_phases hf hfinite htrans
    (fun i : ι=>G i.1 i.2) (fun i=>hG i.1 i.2) (fun i=>hdeg i.1 i.2)
  obtain ⟨ρ,hρ,ho⟩ := hfinite
  have hn : ∃z : ℂ,f z≠0 := by
    by_contra hz
    push Not at hz
    apply htrans
    exact ⟨0,fun z=>by simpa using hz z⟩
  have hdom := CRGExponentialDominance.ae_exists_dominant_group
    (fun q:E.exponents=>q.val) (fun q=>E.normalized q.val q.property) Subtype.val_injective
  filter_upwards [hdom,GundersenTheorem.ae_ray_input hf hn hρ ho] with θ hθ hg
  obtain ⟨ν,c,hc,hphase⟩ := hθ
  have hnon : ∀ᶠr in atTop,f (ray θ r)≠0 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact hg.1 r hr
  have hjet := hg.2.1 n 1 zero_lt_one
  obtain ⟨B,hB,J,hJ,R,_hR,hcont,hcontrol⟩ := exists_residual_control E hf θ ρ hρ ν
    (E.coeff ν.val (H ν).index) (H ν).nonzero c hc hphase hnon hjet
  have hcommon := common_jet_bound θ ρ hρ hnon hjet
  obtain ⟨j,M,_hM,herror⟩ := hcompare ν θ f hf
    (residual E ν (E.coeff ν.val (H ν).index) θ) R B J c hcont hB hJ hc
    (fun r hr=>(hcontrol r hr).2.2.1)
    (fun r hr=>⟨(hcontrol r hr).1,(hcontrol r hr).2.2.2.2,
      (hcontrol r hr).2.2.2.1⟩)
    hnon 1 ((n:ℝ)*ρ) zero_lt_one (mul_nonneg (Nat.cast_nonneg _) hρ) (by
      filter_upwards [hcommon] with r hr
      intro k _hk hkn
      simpa only [one_mul] using hr ⟨k,Nat.lt_succ_of_le hkn⟩)
  exact ⟨⟨ν,j⟩,hnon,M,herror⟩

theorem exists_constant_collected_equation {n : ℕ} (N : Fin n→ℕ)
    (c ω : (k:Fin n)→Fin (N k)→ℂ) (f : ℂ→ℂ)
    (heq : ∀z:ℂ, iteratedDeriv n f z +
      ∑k:Fin n, (∑i:Fin (N k),c k i*Complex.exp (ω k i*z))*iteratedDeriv k.val f z=0) :
    ∃E:CollectedEquation n f,∀q j,E.coeff q j=C ((E.coeff q j).coeff 0) := by
  classical
  let P : (k:Fin n)→Fin (N k)→Polynomial ℂ := fun k i=>C (c k i)
  let Q : (k:Fin n)→Fin (N k)→Polynomial ℂ := fun k i=>C (ω k i)*X
  have hraw : ∀z:ℂ, ∑i:TermIndex N,
      (termPolynomial P i).eval z*Complex.exp ((termExponent Q i).eval z)*
      iteratedDeriv (termOrder i).val f z=0 := by
    intro z
    simpa [Fintype.sum_sum_type,Fintype.sum_sigma,termPolynomial,termExponent,termOrder,
      P,Q,Finset.sum_mul] using heq z
  let b := coefficientGroup (termPolynomial P) (termExponent Q) termOrder
  let S := Finset.univ.image (fun i : TermIndex N => normalizedExponent (termExponent Q i))
  let T := S.filter (fun q => ∃j,b q j≠0)
  have h0S : 0∈S := by
    apply Finset.mem_image.mpr
    refine ⟨Sum.inl (),Finset.mem_univ _,?_⟩
    simp [termExponent,normalizedExponent]
  have h0T : 0∈T := by
    apply Finset.mem_filter.mpr
    refine ⟨h0S,Fin.last n,?_⟩
    simpa only [b,coefficientGroup_top] using (one_ne_zero : (1:Polynomial ℂ)≠0)
  refine ⟨⟨T,⟨0,h0T⟩,b,?_,?_,?_⟩,?_⟩
  · intro q hq
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
    rw [←hi]
    exact normalizedExponent_zero _
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro z
    have hh := collected_identity (termPolynomial P) (termExponent Q) termOrder
      (fun j => iteratedDeriv j.val f z) z
    have he : (∑q∈S,Complex.exp (q.eval z)*
        (∑j,(b q j).eval z*iteratedDeriv j.val f z))=0 := by
      rw [←hh]
      exact hraw z
    rw [show T=S.filter (fun q => ∃j,b q j≠0) from rfl,Finset.sum_filter]
    convert he using 1
    apply Finset.sum_congr rfl
    intro q _
    split_ifs with h
    · rfl
    · have hz : ∀j,b q j=0 := by simpa using h
      simp [hz]

  · intro q j
    change b q j=C ((b q j).coeff 0)
    simp only [b,coefficientGroup,finsetSum_coeff,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs
    · cases i with
      | inl u => simp [termPolynomial,normalizedMultiplier]
      | inr ki => simp [termPolynomial,normalizedMultiplier,P]
    · simp

theorem order_one_of_constant_multipliers {n : ℕ} (N : Fin n→ℕ)
    (c ω : (k:Fin n)→Fin (N k)→ℂ) (f : ℂ→ℂ)
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬∃P:Polynomial ℂ,∀z:ℂ,f z=P.eval z)
    (heq : ∀z:ℂ, iteratedDeriv n f z +
      ∑k:Fin n, (∑i:Fin (N k),c k i*Complex.exp (ω k i*z))*iteratedDeriv k.val f z=0) :
    CRGOrder.IsOrder f 1 ∧ LevinGrowth.FinitePositiveType f 1 ∧
      LevinGrowth.ManuscriptCRG f 1 := by
  obtain ⟨E,hE⟩ := exists_constant_collected_equation N c ω f heq
  exact of_collected_constant_equation E (fun q _ j=>hE q j) hf hfinite htrans

#print axioms of_collected_constant_equation
#print axioms exists_constant_collected_equation
#print axioms order_one_of_constant_multipliers
end CRGConstantMultiplierOrder
