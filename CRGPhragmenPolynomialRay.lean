import CRGPhragmenPolynomialGlobal

noncomputable section
open Set Filter Complex Metric
open scoped Topology
namespace CRGPhragmenPolynomialRay

/-- Eventual real polynomial exponents are enlarged to an integer, and the
initial compact segment is absorbed into one positive constant. -/
theorem rayBound_of_eventual {f : ℂ → ℂ} (hf : Continuous f) {θ : ℝ}
    (h : ∃ A : ℝ, 0 < A ∧ ∃ k R : ℝ, ∀ r : ℝ, R ≤ r →
      ‖f (CRGPhragmenRay.point θ r)‖ ≤ A * r ^ k) :
    CRGPhragmenPolynomialGlobal.RayBound f θ := by
  obtain ⟨A, hA, k, R, hR⟩ := h
  obtain ⟨N, hN⟩ := exists_nat_ge k
  let S := max R 1
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) S).exists_bound_of_continuousOn hf.continuousOn
  let B := max A (max M 1)
  have hB : 0 < B := hA.trans_le (le_max_left _ _)
  refine ⟨B, hB, N, fun x => ?_⟩
  have hbase : 1 ≤ 1 + Real.exp x := by linarith [Real.exp_pos x]
  by_cases hx : S ≤ Real.exp x
  · rw [CRGPhragmenRay.exp_lift]
    apply (hR _ ((le_max_left _ _).trans hx)).trans
    have he : (Real.exp x) ^ k ≤ (1 + Real.exp x) ^ N := by
      calc
        (Real.exp x) ^ k ≤ (Real.exp x) ^ (N : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans hx) hN
        _ = (Real.exp x) ^ N := Real.rpow_natCast _ _
        _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le (by linarith) N
    exact mul_le_mul (le_max_left _ _) he (Real.rpow_nonneg (Real.exp_pos _).le _) hB.le
  · have hn : ‖Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I)‖ ≤ S := by
      simpa [Complex.norm_exp] using (not_le.mp hx).le
    have hm := hM _ (by simpa [mem_closedBall_iff_norm] using hn)
    exact hm.trans (((le_max_left M 1).trans (le_max_right A _)).trans
      (le_mul_of_one_le_right hB.le (one_le_pow₀ hbase)))

/-- Manuscript form with a separate starting radius, exponent and constant on
every direction of a dense set. -/
theorem dense_eventual_polynomial_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfinite : CRGOrder.FiniteOrder f) {D : Set ℝ} (hD : Dense D)
    (hbound : ∀ θ ∈ D, ∃ A : ℝ, 0 < A ∧ ∃ k R : ℝ, ∀ r : ℝ, R ≤ r →
      ‖f (CRGPhragmenRay.point θ r)‖ ≤ A * r ^ k) :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ z : ℂ, ‖f z‖ ≤ A * (1 + ‖z‖) ^ N := by
  exact CRGPhragmenPolynomialGlobal.global_bound_of_dense hf hfinite hD
    (fun θ hθ => rayBound_of_eventual hf.continuous (hbound θ hθ))

#print axioms rayBound_of_eventual
#print axioms dense_eventual_polynomial_bound
end CRGPhragmenPolynomialRay
