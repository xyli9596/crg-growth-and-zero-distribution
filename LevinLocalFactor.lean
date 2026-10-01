import LevinFiniteType
import LevinFactorization
import Mathlib.Analysis.Complex.AbsMax

/-! Local factors for a possibly vanishing entire function, with a single bound
valid at every large scale. This constructs and controls the zero-free factor;
the remaining finite zero product must still be estimated separately. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace LevinLocalFactor

/-- The boundary norm control in finite Blaschke removal extends to the full disk. -/
theorem zero_free_factor_log_bound {f g : ℂ → ℂ} {S M : ℝ} (hS : 0 < S)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 S))
    (hgnz : ∀ z ∈ closedBall 0 S, g z ≠ 0)
    (hboundary : ∀ z ∈ sphere 0 S, ‖g z‖ = ‖f z‖)
    (hbound : ∀ z ∈ sphere 0 S, ‖f z‖ ≤ Real.exp M) :
    ∀ z ∈ closedBall 0 S, Real.log ‖g z‖ ≤ M := by
  have hd : DiffContOnCl ℂ g (ball 0 S) := by
    apply DifferentiableOn.diffContOnCl
    simpa [closure_ball (0 : ℂ) hS.ne'] using hg.differentiableOn
  intro z hz
  have hnorm : ‖g z‖ ≤ Real.exp M := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) S)) hd
    · intro w hw
      have hw' : w ∈ sphere 0 S := by simpa [frontier_ball (0 : ℂ) hS.ne'] using hw
      rw [hboundary w hw']
      exact hbound w hw'
    · simpa [closure_ball (0 : ℂ) hS.ne'] using hz
  simpa only [Real.log_exp] using Real.log_le_log (norm_pos_iff.mpr (hgnz z hz)) hnorm

/-- At every scale r≥1, choose a boundary-free radius 4r<S<8r and construct an
actual zero-free local factor with uniform normalized growth bounds. The original
entire function is allowed to have arbitrary zeros away from its center. -/
theorem exists_scaled_local_factor {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 ≤ ρ)
    (htype : LevinGrowth.FinitePositiveType f ρ) (hf0 : f 0 ≠ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 1 ≤ r →
      ∃ S : ℝ, 4 * r < S ∧ S < 8 * r ∧ ∃ g : ℂ → ℂ,
        Complex.ECanonicalDecomp f g S ∧
        AnalyticOnNhd ℂ g (closedBall 0 S) ∧ (∀ z ∈ closedBall 0 S, g z ≠ 0) ∧
        (∀ z ∈ closedBall 0 S, f z = LevinFactorization.finiteBlaschke f S z * g z) ∧
        (∀ z ∈ closedBall 0 S, Real.log ‖g z‖ ≤ A * r ^ ρ) ∧
        -(A * r ^ ρ) ≤ Real.log ‖g 0‖ := by
  obtain ⟨B, hB, hb⟩ := LevinFiniteType.scaled_exp_bound hf.continuous hρ htype
  let A := max (B * (2 : ℝ) ^ ρ) |Real.log ‖f 0‖|
  have hBA : B * (2 : ℝ) ^ ρ ≤ A := le_max_left _ _
  have hLA : |Real.log ‖f 0‖| ≤ A := le_max_right _ _
  have hA : 0 < A := (mul_pos hB (Real.rpow_pos_of_pos (by norm_num) _)).trans_le hBA
  refine ⟨A, hA, fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  obtain ⟨S, hS, hboundary⟩ := LevinGrowth.exists_zero_free_sphere_between hf ⟨0, hf0⟩
    (show 4 * r < 8 * r by linarith)
  have hSpos : 0 < S := by linarith [hS.1]
  have hfS : AnalyticOnNhd ℂ f (closedBall 0 S) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).mono (subset_univ _)
  obtain ⟨g, hgD, hg, hgnz, heq, hbdy, hcenter⟩ :=
    LevinFactorization.exists_zero_free_factorization_with_center_bound hSpos hfS hf0
      (fun z hz => hboundary z (by simpa [mem_sphere_iff_norm] using hz))
  refine ⟨S, hS.1, hS.2, g, hgD, hg, hgnz, heq, ?_, ?_⟩
  · apply zero_free_factor_log_bound hSpos hg hgnz hbdy
    intro z hz
    have hzS : ‖z‖ = S := by simpa [mem_sphere_iff_norm] using hz
    have h := hb (2 * r) (by linarith) z (by linarith [hS.2])
    apply h.trans
    apply Real.exp_le_exp.mpr
    calc
      B * (2 * r) ^ ρ = (B * (2 : ℝ) ^ ρ) * r ^ ρ := by
        rw [Real.mul_rpow (by norm_num) hr0.le]; ring
      _ ≤ A * r ^ ρ := mul_le_mul_of_nonneg_right hBA (by positivity)
  · have hp : 1 ≤ r ^ ρ := Real.one_le_rpow hr hρ
    have hl := neg_abs_le (Real.log ‖f 0‖)
    nlinarith

#print axioms zero_free_factor_log_bound
#print axioms exists_scaled_local_factor
end LevinLocalFactor
