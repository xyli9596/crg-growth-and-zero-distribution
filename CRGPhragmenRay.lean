import CRGPhragmenGlobal

noncomputable section
open Set Filter Complex Metric
open scoped Topology
namespace CRGPhragmenRay

def point (θ r : ℝ) : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

theorem exp_lift (x θ : ℝ) :
    Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) = point θ (Real.exp x) := by
  simp [point, Complex.exp_add, Complex.ofReal_exp]

/-- Starting radii and bounded initial ray segments are absorbed into a constant. -/
theorem rayBound_of_eventual {f : ℂ → ℂ} (hf : Continuous f) {τ θ : ℝ}
    (h : ∃ C : ℝ, ∃ R : ℝ, ∀ r : ℝ, R ≤ r →
      ‖f (point θ r)‖ ≤ Real.exp (C * r ^ τ)) :
    CRGPhragmenGrowth.RayBound f τ θ := by
  obtain ⟨C, R, hR⟩ := h
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hf.continuousOn
  let A := max M 1
  let C₁ := max C 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC : 0 < C₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨A, hA, C₁, hC, fun x => ?_⟩
  by_cases hx : R ≤ Real.exp x
  · rw [exp_lift]
    apply (hR _ hx).trans
    have he : Real.exp (C * (Real.exp x) ^ τ) ≤ Real.exp (C₁ * Real.exp (τ * x)) := by
      rw [← Real.exp_mul, mul_comm x τ]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    exact he.trans (le_mul_of_one_le_left (Real.exp_pos _).le (le_max_right _ _))
  · have hn : ‖Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I)‖ ≤ R := by
      simpa [Complex.norm_exp] using (not_le.mp hx).le
    have hm := hM _ (by simpa [mem_closedBall_iff_norm] using hn)
    have he : 1 ≤ Real.exp (C₁ * Real.exp (τ * x)) := Real.one_le_exp (by positivity)
    exact hm.trans ((le_max_left _ _).trans (le_mul_of_one_le_right hA.le he))

/-- Exact manuscript form of the dense-ray exponential growth step. -/
theorem dense_eventual_finiteType {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfinite : CRGOrder.FiniteOrder f) {τ : ℝ} (hτ : 0 ≤ τ)
    {D : Set ℝ} (hD : Dense D)
    (hbound : ∀ θ ∈ D, ∃ C : ℝ, ∃ R : ℝ, ∀ r : ℝ, R ≤ r →
      ‖f (point θ r)‖ ≤ Real.exp (C * r ^ τ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ,
      R ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (C * ‖z‖ ^ τ) := by
  exact CRGPhragmenGlobal.finiteType_of_dense hf hfinite hτ hD
    (fun θ hθ => rayBound_of_eventual hf.continuous (hbound θ hθ))

#print axioms exp_lift
#print axioms rayBound_of_eventual
#print axioms dense_eventual_finiteType
end CRGPhragmenRay
