import CRGZeroDistributionCorollary

/-! The literal real-order version of the finite indicator-pair statement.
The proved rational order is embedded into ℝ; order uniqueness ensures that
this covers every actual real-order solution pair. -/
set_option autoImplicit false
noncomputable section
open Set Polynomial
namespace CRGZeroDistributionRealPairs
open LevinGrowth CRGIndicatorFixedPhases CRGIndicatorAlternatives CRGIndicatorCorollary
open CRGZeroDistributionCorollary

theorem finite_real_solution_indicator_pairs {n : ℕ} (A : Fin (n+1) → ℂ → ℂ)
    (hA : ∀ j, CRGExponentialCoefficients.IsExponentialPolynomial (A j))
    (htop : ∃ z : ℂ, A (Fin.last n) z ≠ 0) :
    {x : ℝ × (Direction → ℝ) |
      ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ CRGOrder.FiniteOrder f ∧
        (¬∃Q : Polynomial ℂ,∀z : ℂ,f z=Q.eval z) ∧ SolvesEquation A f ∧
        CRGOrder.IsOrder f x.1 ∧ IsIndicator f x.1 x.2}.Finite := by
  have hfin := finite_actual_solution_indicator_pairs A hA htop
  let castPair : ℚ × (Direction → ℝ) → ℝ × (Direction → ℝ) := fun x=>((x.1:ℝ),x.2)
  apply (hfin.image castPair).subset
  intro x hx
  obtain ⟨f,hf,hfinite,htrans,heq,ho,hi⟩ := hx
  obtain ⟨_,R,hR⟩ := corollary_3_6 A hA htop
  obtain ⟨σ,_hσ,hoσ,_ht,h,_hcrg,_hi,_hpiece,_hzero⟩ := hR f hf hfinite htrans heq
  have he : x.1=(σ:ℝ) := isOrder_unique ho hoσ
  refine ⟨(σ,x.2),?_,?_⟩
  · exact ⟨f,hf,hfinite,htrans,heq,hoσ,by simpa only [←he] using hi⟩
  · apply Prod.ext
    · exact he.symm
    · rfl

#print axioms finite_real_solution_indicator_pairs
end CRGZeroDistributionRealPairs
