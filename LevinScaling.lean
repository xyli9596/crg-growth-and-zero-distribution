import LevinScaledBounds

/-!
# Scaling annular estimates to physical radii

The homogeneous angular term scales by the same real power as the logarithmic
normalization. On the unit annulus its factor is at least one at positive order.
-/

noncomputable section
open Set Metric
open scoped BigOperators
open LevinGrowth LevinIndicatorModulus

namespace LevinScaling

/-- Positive dilation preserves membership in the corresponding open disk. -/
theorem mem_scaled_ball_iff {R : ℝ} (hR : 0 < R) (z c : ℂ) (s : ℝ) :
    (R : ℂ) * z ∈ ball ((R : ℂ) * c) (R * s) ↔ z ∈ ball c s := by
  rw [mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  exact mul_lt_mul_iff_right₀ hR

/-- Physical radii have exactly the scaled total radius. -/
theorem sum_scaled_radii {ι : Type*} [Fintype ι] (R : ℝ) (r : ι → ℝ) :
    (∑ j, R * r j) = R * ∑ j, r j := (Finset.mul_sum _ _ _).symm

/-- The homogeneous indicator has the intended polar form at positive radius. -/
theorem homogeneousIndicator_rayPoint {t ρ : ℝ} (ht : 0 < t)
    (h : Direction → ℝ) (ζ : Direction) :
    homogeneousIndicator ρ h (rayPoint t ζ) = t ^ ρ * h ζ := by
  rw [homogeneousIndicator, norm_rayPoint ht.le ζ,
    LevinScaledBounds.normalizedDirection_rayPoint ht ζ]

/-- A normalized unit-shell estimate transfers to the original physical shell.
The same absolute error remains valid because `(r/R)^ρ ≥ 1`. -/
theorem shell_estimate_of_scaled_shell {ι : Type*} [Fintype ι]
    {f : ℂ → ℂ} {ρ R ε : ℝ} {h : Direction → ℝ}
    (c : ι → ℂ) (radius : ι → ℝ)
    (hR : 0 < R) (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hscaled : ∀ z : ℂ, ‖z‖ ∈ Icc (1 : ℝ) 2 →
      (∀ j, z ∉ ball (c j) (radius j)) →
      f ((R : ℂ) * z) ≠ 0 ∧
        |Real.log ‖f ((R : ℂ) * z)‖ / R ^ ρ - homogeneousIndicator ρ h z| ≤ ε) :
    ∀ r : ℝ, r ∈ Icc R (2 * R) → ∀ ζ : Direction,
      (∀ j, rayPoint r ζ ∉ ball ((R : ℂ) * c j) (R * radius j)) →
      f (rayPoint r ζ) ≠ 0 ∧ |normalizedLog f ρ r ζ - h ζ| ≤ ε := by
  intro r hr ζ hout
  have hr0 : 0 < r := hR.trans_le hr.1
  let t := r / R
  have ht1 : 1 ≤ t := (le_div_iff₀ hR).mpr (by simpa using hr.1)
  have ht2 : t ≤ 2 := (div_le_iff₀ hR).mpr (by simpa [mul_comm] using hr.2)
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
  have hpoint : (R : ℂ) * rayPoint t ζ = rayPoint r ζ := by
    have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    dsimp [rayPoint, t]
    push_cast
    field_simp
  have hshell : ‖rayPoint t ζ‖ ∈ Icc (1 : ℝ) 2 := by
    rw [norm_rayPoint ht0.le ζ]
    exact ⟨ht1, ht2⟩
  have hnot : ∀ j, rayPoint t ζ ∉ ball (c j) (radius j) := by
    intro j hj
    apply hout j
    rw [← hpoint]
    exact (mem_scaled_ball_iff hR _ _ _).mpr hj
  have hgood := hscaled (rayPoint t ζ) hshell hnot
  rw [hpoint, homogeneousIndicator_rayPoint ht0 h ζ] at hgood
  refine ⟨hgood.1, ?_⟩
  have htρ : 1 ≤ t ^ ρ := Real.one_le_rpow ht1 hρ.le
  have htρpos : 0 < t ^ ρ := Real.rpow_pos_of_pos ht0 _
  have hRt : R * t = r := by dsimp [t]; field_simp
  have hscale := LevinScaledBounds.scaled_error_identity f ρ h hR
    (w := rayPoint t ζ) (by rw [norm_rayPoint ht0.le ζ]; exact ht0)
  rw [hpoint, norm_rayPoint ht0.le ζ,
    LevinScaledBounds.normalizedDirection_rayPoint ht0 ζ, hRt,
    homogeneousIndicator_rayPoint ht0 h ζ] at hscale
  have habs : |normalizedLog f ρ r ζ - h ζ| ≤ ε / t ^ ρ := by
    apply (le_div_iff₀ htρpos).mpr
    have hb := hgood.2
    rw [hscale, abs_mul, abs_of_pos htρpos] at hb
    simpa only [mul_comm] using hb
  exact habs.trans (div_le_self hε htρ)

#print axioms mem_scaled_ball_iff
#print axioms sum_scaled_radii
#print axioms homogeneousIndicator_rayPoint
#print axioms shell_estimate_of_scaled_shell

end LevinScaling
