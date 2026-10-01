import GundersenBlaschke
import GundersenLogarithm
import LevinLocalFactor

/-! A local logarithmic derivative estimate derived from entire analyticity,
Jensen's formula, actual finite Blaschke removal, and finite-point Cartan covering.
The assumptions are growth data, not a logarithmic derivative estimate. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology
namespace GundersenLocal

/-- At scale R, an exponential growth bound on the disk of radius 32R gives
Cartan disks controlling the original function's actual logarithmic derivative.
N is its actual local zero count, retained with Jensen's bound. -/
theorem exists_disks_logDeriv_bound {f : ℂ → ℂ} {R M H : ℝ}
    (hf : Differentiable ℂ f) (hf0 : f 0 = 1)
    (hR : 0 < R) (hM : 0 ≤ M) (hH : 0 < H)
    (hbound : ∀ z ∈ closedBall 0 (32*R), ‖f z‖ ≤ Real.exp M) :
    ∃ N : ℕ, (N : ℝ) ≤ M / Real.log 2 ∧
      ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ s : Fin m → ℝ,
      (∀ j, 0 < s j) ∧ (∑ j, s j) ≤ 5*H ∧
      ∀ z ∈ closedBall 0 R, (∀ j, z ∉ ball (c j) (s j)) →
        f z ≠ 0 ∧ ‖logDeriv f z‖ ≤
          20*M/R + (N : ℝ)/H * (1+Real.log N) + (N : ℝ)/(4*R) := by
  obtain ⟨S, hS, hboundary⟩ := LevinGrowth.exists_zero_free_sphere_between
    hf ⟨0, by simp [hf0]⟩ (show 8*R < 16*R by linarith)
  have hS0 : 0 < S := by linarith [hS.1]
  have hfS : AnalyticOnNhd ℂ f (closedBall 0 S) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).mono (subset_univ _)
  have hbd : ∀ z ∈ sphere 0 S, f z ≠ 0 := by
    intro z hz
    exact hboundary z (by simpa [mem_sphere, dist_zero_right] using hz)
  obtain ⟨g, _, hg, hgnz, heq, hgnorm, hg0⟩ :=
    LevinFactorization.exists_zero_free_factorization_with_center_bound hS0 hfS
      (by simp [hf0]) hbd
  have hgbound : ∀ z ∈ closedBall 0 S, Real.log ‖g z‖ ≤ M := by
    apply LevinLocalFactor.zero_free_factor_log_bound hS0 hg hgnz hgnorm
    intro z hz
    apply hbound z
    have hzS := mem_sphere_zero_iff_norm.mp hz
    rw [mem_closedBall_zero_iff, hzS]
    linarith [hS.2]
  have hgcenter : -M ≤ Real.log ‖g 0‖ := by
    simp only [hf0, norm_one, Real.log_one] at hg0
    linarith
  let N := Fintype.card (LevinMinimumModulus.ZeroIndex hfS)
  have hN : (N : ℝ) ≤ M / Real.log 2 := by
    rw [show (N : ℝ) = LevinFiniteProduct.zeroCount hfS from
      LevinMinimumModulus.zeroIndex_card hfS]
    apply LevinMinimumModulus.zeroCount_local_bound hf (R := 4*R) (by positivity)
      hM hf0 (by linarith [hS.2]) ?_ hfS
    intro z hz
    exact hbound z (by convert hz using 1; congr 1; ring)
  obtain ⟨m, c, s, hs, hsum, hb⟩ :=
    GundersenBlaschke.exists_disks_finiteBlaschke_bound hfS hS0 hH
  refine ⟨N, hN, m, c, s, hs, hsum, fun z hz hout => ?_⟩
  have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hzq : z ∈ ball 0 (S/4) := by rw [mem_ball_zero_iff]; linarith [hS.1]
  have hzhalf : z ∈ closedBall 0 (S/2) := by
    rw [mem_closedBall_zero_iff]; linarith [hS.1]
  have hzS : z ∈ closedBall 0 S := by rw [mem_closedBall_zero_iff]; linarith [hS.1]
  have hzSi : z ∈ ball 0 S := by rw [mem_ball_zero_iff]; linarith [hS.1]
  obtain ⟨hB, hBbound⟩ := hb z hzhalf hout
  refine ⟨by rw [heq z hzS]; exact mul_ne_zero hB (hgnz z hzS), ?_⟩
  have hge : ‖logDeriv g z‖ ≤ 160*M/S :=
    GundersenLogarithm.zero_free_logDeriv_bound hS0 hM hg hgnz hzq hgbound hgcenter
  have hevent : f =ᶠ[𝓝 z] (fun w => LevinFactorization.finiteBlaschke f S w * g w) := by
    filter_upwards [isOpen_ball.mem_nhds hzSi] with w hw
    exact heq w (ball_subset_closedBall hw)
  have hlog : logDeriv f z = logDeriv (LevinFactorization.finiteBlaschke f S) z + logDeriv g z := by
    rw [(logDeriv_congr_nhds hevent).eq_of_nhds]
    exact logDeriv_mul z hB (hgnz z hzS)
      ((LevinFactorization.analyticOnNhd_finiteBlaschke hfS) z hzS).differentiableAt
      (hg z hzS).differentiableAt
  have hfirst : 160*M/S ≤ 20*M/R := by
    apply (div_le_div_iff₀ hS0 hR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hS.1.le hM]
  have hlast : (N : ℝ)*(2/S) ≤ (N : ℝ)/(4*R) := by
    have hh : 2/S ≤ 1/(4*R) := by
      apply (div_le_div_iff₀ hS0 (by positivity)).mpr
      linarith [hS.1]
    have hn := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg N : (0:ℝ)≤N)
    simpa only [mul_one_div] using hn
  rw [hlog]
  have hh := (norm_add_le _ _).trans (add_le_add hBbound hge)
  change ‖logDeriv (LevinFactorization.finiteBlaschke f S) z + logDeriv g z‖ ≤ _
  dsimp [N] at hlast
  linarith

#print axioms exists_disks_logDeriv_bound
end GundersenLocal
