import CRGOrderRay
import CRGPolynomialGrowth

/-! A finite list of nondegenerate ray phases forces positive rational order
and finite positive type. The maximal degree is selected among the actual
positive leading terms; decay on other rays is kept, not discarded as an
assumed global growth estimate. -/
noncomputable section
open Set Filter
open scoped Topology
namespace CRGOrderPhaseCriterion
open CRGOrderRay

/-- A transcendental entire function cannot have nonpositive leading terms
on all directions of a dense finite phase description. -/
theorem exists_positive_leading {ι : Type*} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬ ∃ P : Polynomial ℂ, ∀ z : ℂ, f z = P.eval z)
    (degree : ι → ℚ) (chosen : ℝ → ι) (leading : ℝ → ℝ)
    {D : Set ℝ} (hD : Dense D)
    (hdata : ∀ θ ∈ D, RayData f θ (degree (chosen θ) : ℝ) (leading θ)) :
    ∃ θ ∈ D, 0 < (degree (chosen θ) : ℝ) ∧ 0 < leading θ := by
  by_contra hn
  have hpoly : ∀ θ ∈ D, ∃ A : ℝ, 0 < A ∧ ∃ k R : ℝ, ∀ r : ℝ, R ≤ r →
      ‖f (CRGPhragmenRay.point θ r)‖ ≤ A * r ^ k := by
    intro θ hθ
    have hd := hdata θ hθ
    by_cases hz : (degree (chosen θ) : ℝ) = 0
    · exact zero_degree_polynomial hd hz
    have hp : 0 < (degree (chosen θ) : ℝ) :=
      lt_of_le_of_ne hd.degree_nonneg (Ne.symm hz)
    have hnot : ¬ 0 < leading θ := fun hpos => hn ⟨θ, hθ, hp, hpos⟩
    have hneg : leading θ < 0 :=
      lt_of_le_of_ne (le_of_not_gt hnot) (hd.positive hp).1
    obtain ⟨R, hR⟩ := eventually_atTop.1 (negative_leading_bounded hd hp hneg)
    exact ⟨1, zero_lt_one, 0, R, fun r hr => by simpa using hR r hr⟩
  obtain ⟨A, hA, N, hbound⟩ :=
    CRGPhragmenPolynomialRay.dense_eventual_polynomial_bound hf hfinite hD hpoly
  exact htrans (CRGPolynomialGrowth.exists_polynomial_of_growth hf N hA.le hbound)

/-- Finite phase degree alternatives give a positive rational exponent of
finite positive type, without assuming existence or value of the order. -/
theorem finite_positive_type {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬ ∃ P : Polynomial ℂ, ∀ z : ℂ, f z = P.eval z)
    (degree : ι → ℚ) (chosen : ℝ → ι) (leading : ℝ → ℝ)
    {D : Set ℝ} (hD : Dense D)
    (hdata : ∀ θ ∈ D, RayData f θ (degree (chosen θ) : ℝ) (leading θ)) :
    ∃ σ : ℚ, 0 < σ ∧ LevinGrowth.FinitePositiveType f (σ : ℝ) := by
  classical
  let s : Finset ι := Finset.univ.filter fun i =>
    ∃ θ ∈ D, chosen θ = i ∧ 0 < (degree i : ℝ) ∧ 0 < leading θ
  obtain ⟨θ₀, hθ₀, hd₀, ha₀⟩ := exists_positive_leading hf hfinite htrans degree chosen leading hD hdata
  have hs : s.Nonempty := ⟨chosen θ₀, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, θ₀, hθ₀, rfl, hd₀, ha₀⟩⟩
  obtain ⟨i, hi, himax⟩ := s.exists_max_image (fun i => (degree i : ℝ)) hs
  obtain ⟨θ, hθ, hchosen, hd, ha⟩ := (Finset.mem_filter.mp hi).2
  have hdataθ := hdata θ hθ
  rw [hchosen] at hdataθ
  refine ⟨degree i, by exact_mod_cast hd, ?_, positive_leading_lower hdataθ hd ha⟩
  apply CRGPhragmenRay.dense_eventual_finiteType hf hfinite hd.le hD
  intro φ hφ
  have hφdata := hdata φ hφ
  by_cases hd0 : (degree (chosen φ) : ℝ) = 0
  · exact zero_degree_upper hφdata hd0 hd
  have hdpos : 0 < (degree (chosen φ) : ℝ) :=
    lt_of_le_of_ne hφdata.degree_nonneg (Ne.symm hd0)
  rcases lt_or_gt_of_ne (hφdata.positive hdpos).1 with haneg | hapos
  · obtain ⟨R, hR⟩ := eventually_atTop.1 (negative_leading_bounded hφdata hdpos haneg)
    exact ⟨0, R, fun r hr => by simpa using hR r hr⟩
  · apply positive_leading_upper hφdata hdpos hapos
    exact himax (chosen φ) (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, φ, hφ, rfl, hdpos, hapos⟩)

/-- The positive rational type exponent is the actual order as well. -/
theorem positive_rational_order {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬ ∃ P : Polynomial ℂ, ∀ z : ℂ, f z = P.eval z)
    (degree : ι → ℚ) (chosen : ℝ → ι) (leading : ℝ → ℝ)
    {D : Set ℝ} (hD : Dense D)
    (hdata : ∀ θ ∈ D, RayData f θ (degree (chosen θ) : ℝ) (leading θ)) :
    ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ : ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ : ℝ) := by
  obtain ⟨σ, hσ, htype⟩ := finite_positive_type hf hfinite htrans degree chosen leading hD hdata
  exact ⟨σ, hσ, CRGOrder.finitePositiveType_isOrder (by exact_mod_cast hσ.le) htype, htype⟩

#print axioms exists_positive_leading
#print axioms finite_positive_type
#print axioms positive_rational_order
end CRGOrderPhaseCriterion
