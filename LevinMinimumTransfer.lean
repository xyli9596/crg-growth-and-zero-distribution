import LevinMinimumModulus

/-!
# Translating the local Cartan minimum estimate

The function is normalized by its actual nonzero value at the chosen center.
The growth bound is divided at the norm level, so zeros away from the center
cause no logarithm substitution. Pointwise logarithms are used only after the
local theorem has established nonvanishing.
-/

noncomputable section
open Set Metric
open scoped BigOperators

namespace LevinMinimumTransfer

/-- Translation preserves membership in an open disk. -/
theorem sub_mem_ball_iff (z q c : ℂ) (r : ℝ) :
    z - q ∈ ball c r ↔ z ∈ ball (q + c) r := by
  simp only [mem_ball, dist_eq_norm, sub_sub]

/-- The genuine local Cartan estimate around an arbitrary nonzero center. -/
theorem exists_disks_local_lower {f : ℂ → ℂ} {q : ℂ} {R M η : ℝ}
    (hf : Differentiable ℂ f) (hfq : f q ≠ 0)
    (hR : 0 < R) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ closedBall q (8 * R),
      ‖f z‖ ≤ Real.exp (M + Real.log ‖f q‖))
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (r : Fin m → ℝ),
      (∀ j, 0 < r j) ∧ (∑ j, r j) ≤ 5 * η * R ∧
      ∀ z ∈ closedBall q R, (∀ j, z ∉ ball (c j) (r j)) →
        f z ≠ 0 ∧ Real.log ‖f q‖ - LevinMinimumModulus.loss η * M ≤ Real.log ‖f z‖ := by
  let F : ℂ → ℂ := fun w => f (q + w) / f q
  have hF : Differentiable ℂ F := by
    exact (hf.comp (by fun_prop)).div_const _
  have hF0 : F 0 = 1 := by simp [F, hfq]
  have hqpos : 0 < ‖f q‖ := norm_pos_iff.mpr hfq
  have hFbound : ∀ w ∈ closedBall (0 : ℂ) (8 * R), ‖F w‖ ≤ Real.exp M := by
    intro w hw
    have hqw : q + w ∈ closedBall q (8 * R) := by
      simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw
    calc
      ‖F w‖ = ‖f (q + w)‖ / ‖f q‖ := norm_div _ _
      _ ≤ Real.exp (M + Real.log ‖f q‖) / ‖f q‖ :=
        div_le_div_of_nonneg_right (hbound _ hqw) hqpos.le
      _ = Real.exp M := by rw [Real.exp_add, Real.exp_log hqpos]; field_simp
  obtain ⟨m, c, r, hrpos, hsum, hlocal⟩ :=
    LevinMinimumModulus.exists_disks_local_lower hF hR hM hF0 hFbound hη hη1
  refine ⟨m, (fun j => q + c j), r, hrpos, hsum, ?_⟩
  intro z hz hzout
  have hzw : z - q ∈ closedBall (0 : ℂ) R := by
    simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hz
  have hout : ∀ j, z - q ∉ ball (c j) (r j) := by
    intro j hj
    exact hzout j ((sub_mem_ball_iff z q (c j) (r j)).mp hj)
  have hgood := hlocal (z - q) hzw hout
  have hFz : F (z - q) = f z / f q := by
    dsimp [F]
    rw [show q + (z - q) = z by ring]
  have hfnz : f z ≠ 0 := by
    intro hzero
    exact hgood.1 (by rw [hFz, hzero, zero_div])
  have hlog : Real.log ‖F (z - q)‖ = Real.log ‖f z‖ - Real.log ‖f q‖ := by
    rw [hFz, norm_div, Real.log_div (norm_ne_zero_iff.mpr hfnz) hqpos.ne']
  refine ⟨hfnz, ?_⟩
  rw [hlog] at hgood
  linarith [hgood.2]

#print axioms sub_mem_ball_iff
#print axioms exists_disks_local_lower

end LevinMinimumTransfer
