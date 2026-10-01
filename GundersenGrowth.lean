import GundersenLocal
import CRGOrder

/-! Finite-order growth supplies the local disk estimates at every large scale.
The constants are independent of the scale. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace GundersenGrowth

/-- Absorb the initial compact disk, using only the upper-order bound. -/
theorem scaled_exp_bound {f : ℂ → ℂ} {ρ δ : ℝ} (hf : Continuous f)
    (hρ : 0 ≤ ρ) (hδ : 0 < δ) (horder : CRGOrder.UpperOrder f ρ) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 1 ≤ r → ∀ z ∈ closedBall 0 (32*r),
      ‖f z‖ ≤ Real.exp (A * r ^ (ρ+δ)) := by
  obtain ⟨R, hbound⟩ := horder δ hδ
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hf.continuousOn
  let A := max ((32 : ℝ)^(ρ+δ)) (max M 1)
  have hCA : (32 : ℝ)^(ρ+δ) ≤ A := le_max_left _ _
  have hMA : M ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have h1A : 1 ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hA : 0 < A := by linarith
  refine ⟨A, hA, fun r hr z hz => ?_⟩
  have hpow : 1 ≤ r^(ρ+δ) := Real.one_le_rpow hr (by linarith)
  by_cases hlarge : R ≤ ‖z‖
  · apply (hbound z hlarge).trans
    apply Real.exp_le_exp.mpr
    calc
      ‖z‖^(ρ+δ) ≤ (32*r)^(ρ+δ) :=
        Real.rpow_le_rpow (norm_nonneg _) (mem_closedBall_zero_iff.mp hz) (by linarith)
      _ = (32:ℝ)^(ρ+δ) * r^(ρ+δ) := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ A * r^(ρ+δ) := mul_le_mul_of_nonneg_right hCA (by positivity)
  · have hzR : z ∈ closedBall (0 : ℂ) R :=
      mem_closedBall_zero_iff.mpr (not_le.mp hlarge).le
    calc
      ‖f z‖ ≤ M := hM z hzR
      _ ≤ A := hMA
      _ ≤ A * r^(ρ+δ) := by nlinarith
      _ ≤ Real.exp (A * r^(ρ+δ)) := by linarith [Real.add_one_le_exp (A*r^(ρ+δ))]

theorem eventually_log_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, Real.log r ≤ r^ε := by
  have h := (isLittleO_log_rpow_atTop hε).bound (show (0:ℝ)<1 by norm_num)
  filter_upwards [h, eventually_gt_atTop (0:ℝ)] with r hr hr0
  have hh : |Real.log r| ≤ r^ε := by
    simpa only [Real.norm_eq_abs, one_mul, abs_of_pos (Real.rpow_pos_of_pos hr0 _)] using hr
  exact (le_abs_self _).trans hh

/-- The N log N Cartan loss can be absorbed into an arbitrarily small extra
power while retaining a summable angular disk budget. -/
theorem eventually_numerical_bound {A C σ η : ℝ}
    (hA : 0 ≤ A) (hC : 1 ≤ C) (hσ : 0 ≤ σ) (hη : 0 < η) :
    ∀ᶠ r : ℝ in atTop, ∀ N : ℕ, (N : ℝ) ≤ C*r^σ →
      20*(A*r^σ)/r + (N:ℝ)/r^(1-η) * (1+Real.log N) + (N:ℝ)/(4*r)
        ≤ r^(σ-1+3*η) := by
  let D := 1 + Real.log C + σ
  have hC0 : 0 < C := by linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hlog := eventually_log_le_rpow hη
  have hconst := CRGOrder.eventually_mul_rpow_le (C := 20*A+C*D+C/4)
    (show σ-1+2*η < σ-1+3*η by linarith)
  filter_upwards [hlog, hconst, eventually_ge_atTop (1:ℝ)] with r hlogr hfin hr
  have hr0 : 0 < r := by linarith
  intro N hN
  have hηpow : 1 ≤ r^η := Real.one_le_rpow hr hη.le
  have hp (t : ℝ) : 0 < r^t := Real.rpow_pos_of_pos hr0 t
  have hNlog : (N:ℝ)*(1+Real.log N) ≤ C*r^σ * (D*r^η) := by
    by_cases hNz : N = 0
    · simp only [hNz, Nat.cast_zero, zero_mul]
      positivity
    have hN0 : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hNz
    have hl : Real.log N ≤ Real.log C + σ*Real.log r := by
      have hh := Real.log_le_log hN0 hN
      rwa [Real.log_mul hC0.ne' (hp σ).ne', Real.log_rpow hr0] at hh
    have hlg : 1+Real.log N ≤ D*r^η := by
      have hs := mul_le_mul_of_nonneg_left hlogr hσ
      have hc := mul_le_mul_of_nonneg_left hηpow (show 0≤1+Real.log C by linarith)
      dsimp [D]
      nlinarith
    exact mul_le_mul hN hlg (by positivity) (by positivity)
  have hmid : (N:ℝ)/r^(1-η)*(1+Real.log N) ≤ C*D*r^(σ-1+2*η) := by
    calc
      _ = ((N:ℝ)*(1+Real.log N))/r^(1-η) := by ring
      _ ≤ (C*r^σ*(D*r^η))/r^(1-η) := div_le_div_of_nonneg_right hNlog (hp _).le
      _ = C*D*r^(σ-1+2*η) := by
        rw [show C*r^σ*(D*r^η) = C*D*(r^σ*r^η) by ring,
          ← Real.rpow_add hr0, mul_div_assoc, ← Real.rpow_sub hr0]
        congr 2; ring
  have hfirst : 20*(A*r^σ)/r ≤ 20*A*r^(σ-1+2*η) := by
    calc
      _ = 20*A*r^(σ-1) := by rw [Real.rpow_sub hr0, Real.rpow_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hr (by linarith)) (by positivity)
  have hlast : (N:ℝ)/(4*r) ≤ (C/4)*r^(σ-1+2*η) := by
    calc
      _ ≤ (C*r^σ)/(4*r) := div_le_div_of_nonneg_right hN (by positivity)
      _ = (C/4)*r^(σ-1) := by rw [Real.rpow_sub hr0, Real.rpow_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hr (by linarith)) (by positivity)
  have hh : 20*(A*r^σ)/r + (N:ℝ)/r^(1-η)*(1+Real.log N) + (N:ℝ)/(4*r) ≤
      (20*A+C*D+C/4)*r^(σ-1+2*η) := by nlinarith
  exact hh.trans hfin

/-- Finite order now yields sharp local logarithmic derivative estimates, with
an exceptional total radius small enough for angular Borel--Cantelli. -/
theorem eventually_disks_logDeriv_bound {f : ℂ → ℂ} {ρ δ : ℝ}
    (hf : Differentiable ℂ f) (hf0 : f 0 = 1) (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (horder : CRGOrder.UpperOrder f ρ) :
    ∀ᶠ R : ℝ in atTop,
      ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ s : Fin m → ℝ,
      (∀ j, 0 < s j) ∧ (∑ j, s j) ≤ 5*R^(1-δ/4) ∧
      ∀ z ∈ closedBall 0 R, (∀ j, z ∉ ball (c j) (s j)) →
        f z ≠ 0 ∧ ‖logDeriv f z‖ ≤ R^(ρ-1+δ) := by
  obtain ⟨A, hA, hb⟩ := scaled_exp_bound hf.continuous hρ
    (show 0 < δ/4 by linarith) horder
  let C := max 1 (A/Real.log 2)
  have hC : 1 ≤ C := le_max_left _ _
  have he := eventually_numerical_bound hA.le hC
    (show 0 ≤ ρ+δ/4 by linarith) (show 0 < δ/4 by linarith)
  filter_upwards [he, eventually_ge_atTop (1:ℝ)] with R hnum hR
  have hR0 : 0 < R := by linarith
  obtain ⟨N, hN, m, c, s, hs, hsum, hpoint⟩ :=
    GundersenLocal.exists_disks_logDeriv_bound hf hf0 hR0
      (show 0 ≤ A*R^(ρ+δ/4) by positivity)
      (Real.rpow_pos_of_pos hR0 (1-δ/4)) (hb R hR)
  refine ⟨m, c, s, hs, hsum, fun z hz hout => ?_⟩
  obtain ⟨hnz, hval⟩ := hpoint z hz hout
  refine ⟨hnz, hval.trans ?_⟩
  have hN' : (N:ℝ) ≤ C*R^(ρ+δ/4) := by
    calc
      (N:ℝ) ≤ (A*R^(ρ+δ/4))/Real.log 2 := hN
      _ = (A/Real.log 2)*R^(ρ+δ/4) := by ring
      _ ≤ C*R^(ρ+δ/4) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  simpa only [show ρ+δ/4-1+3*(δ/4) = ρ-1+δ by ring] using hnum N hN'

#print axioms eventually_disks_logDeriv_bound
#print axioms scaled_exp_bound
#print axioms eventually_log_le_rpow
#print axioms eventually_numerical_bound
end GundersenGrowth
