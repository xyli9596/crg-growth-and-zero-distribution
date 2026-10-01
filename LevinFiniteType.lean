import LevinGrowth
import LevinAnalytic
import LevinCompact
import Mathlib.Analysis.Normed.Group.Bounded

/-! Actual growth hypotheses imply uniform analytic estimates. The last theorem
applies to a globally zero-free entire function. For general entire functions,
one still has to estimate the zero factors after local Blaschke decomposition. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace LevinFiniteType

/-- Absorb the compact initial region into a single finite-type constant. -/
theorem scaled_exp_bound {f : ℂ → ℂ} {ρ : ℝ} (hf : Continuous f) (hρ : 0 ≤ ρ)
    (htype : LevinGrowth.FinitePositiveType f ρ) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 1 ≤ r → ∀ z : ℂ, ‖z‖ ≤ 4 * r →
      ‖f z‖ ≤ Real.exp (A * r ^ ρ) := by
  obtain ⟨C, hC, R, hR, hbound⟩ := htype.1
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hf.continuousOn
  let A := max (C * (4 : ℝ) ^ ρ) (max M 1)
  have hCA : C * (4 : ℝ) ^ ρ ≤ A := le_max_left _ _
  have hMA : M ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have h1A : 1 ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hA : 0 < A := by linarith
  refine ⟨A, hA, fun r hr z hz => ?_⟩
  have hpow : 1 ≤ r ^ ρ := Real.one_le_rpow hr hρ
  by_cases hlarge : R ≤ ‖z‖
  · apply (hbound z hlarge).trans
    apply Real.exp_le_exp.mpr
    calc
      C * ‖z‖ ^ ρ ≤ C * (4 * r) ^ ρ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hz hρ) hC.le
      _ = (C * (4 : ℝ) ^ ρ) * r ^ ρ := by rw [Real.mul_rpow (by norm_num) (by linarith)]; ring
      _ ≤ A * r ^ ρ := mul_le_mul_of_nonneg_right hCA (by positivity)
  · have hsmall : z ∈ closedBall (0 : ℂ) R := by
      simpa [mem_closedBall_iff_norm] using (not_le.mp hlarge).le
    calc
      ‖f z‖ ≤ M := hM z hsmall
      _ ≤ A := hMA
      _ ≤ A * r ^ ρ := by nlinarith
      _ ≤ Real.exp (A * r ^ ρ) := by linarith [Real.add_one_le_exp (A * r ^ ρ)]

/-- The same constant can also control the lower value at a fixed nonzero center. -/
theorem scaled_log_bounds {f : ℂ → ℂ} {ρ : ℝ} (hf : Continuous f) (hρ : 0 ≤ ρ)
    (htype : LevinGrowth.FinitePositiveType f ρ) (hnz : ∀ z : ℂ, f z ≠ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 1 ≤ r →
      (∀ z ∈ closedBall (0 : ℂ) (4 * r), Real.log ‖f z‖ ≤ A * r ^ ρ) ∧
      -(A * r ^ ρ) ≤ Real.log ‖f 0‖ := by
  obtain ⟨B, hB, hb⟩ := scaled_exp_bound hf hρ htype
  let A := max B |Real.log ‖f 0‖|
  have hBA : B ≤ A := le_max_left _ _
  have hLA : |Real.log ‖f 0‖| ≤ A := le_max_right _ _
  have hA : 0 < A := hB.trans_le hBA
  refine ⟨A, hA, fun r hr => ⟨?_, ?_⟩⟩
  · intro z hz
    have hz' : ‖z‖ ≤ 4 * r := by simpa [mem_closedBall_iff_norm] using hz
    have he := hb r hr z hz'
    have hlog := Real.log_le_log (norm_pos_iff.mpr (hnz z)) he
    rw [Real.log_exp] at hlog
    exact hlog.trans (mul_le_mul_of_nonneg_right hBA (by positivity))
  · have hpow : 1 ≤ r ^ ρ := Real.one_le_rpow hr hρ
    have hl := neg_abs_le (Real.log ‖f 0‖)
    nlinarith

/-- No equicontinuity premise is assumed here: the common Lipschitz bound is
derived from holomorphy, finite type, and absence of zeros. -/
theorem zero_free_normalized_lipschitz {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 ≤ ρ)
    (htype : LevinGrowth.FinitePositiveType f ρ) (hnz : ∀ z : ℂ, f z ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 1 ≤ r → ∀ v w : LevinGrowth.Direction,
      |LevinGrowth.normalizedLog f ρ r v - LevinGrowth.normalizedLog f ρ r w| ≤
        K * dist v w := by
  obtain ⟨A, hA, hb⟩ := scaled_log_bounds hf.continuous hρ htype hnz
  refine ⟨20 * A, by positivity, fun r hr v w => ?_⟩
  have ha : AnalyticOnNhd ℂ f univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have h := CRGLevinAnalytic.normalized_log_norm_oscillation (by linarith : 0 < r) hA.le
    (ha.mono (subset_univ _)) (fun z _ => hnz z) v.property.le w.property.le
    (hb r hr).1 (hb r hr).2
  simpa only [LevinGrowth.normalizedLog, LevinGrowth.rayPoint, Subtype.dist_eq, dist_eq_norm] using h

theorem zero_free_asymptotic_equicontinuity {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 ≤ ρ)
    (htype : LevinGrowth.FinitePositiveType f ρ) (hnz : ∀ z : ℂ, f z ≠ 0) :
    LevinCompact.AsymptoticUniformEquicontinuous (LevinGrowth.normalizedLog f ρ) atTop := by
  obtain ⟨K, hK, hb⟩ := zero_free_normalized_lipschitz hf hρ htype hnz
  intro ε hε
  refine ⟨ε / K, div_pos hε hK, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr v w hvw
  rw [Real.dist_eq]
  apply (hb r hr v w).trans_lt
  exact (lt_div_iff₀' hK).mp hvw

#print axioms scaled_exp_bound
#print axioms scaled_log_bounds
#print axioms zero_free_normalized_lipschitz
#print axioms zero_free_asymptotic_equicontinuity
end LevinFiniteType
