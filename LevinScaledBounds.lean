import LevinIndicatorModulus
import LevinCriterion
import LevinGrid

/-!
# Uniform scaled upper bounds and good centers

All starting radii are uniform over the full enlarged annulus. Good centers
are obtained from the actual zero-density radial exception, using the uniform
mesh-radius theorem rather than point-dependent limiting thresholds.
-/

noncomputable section
open Set Filter MeasureTheory Topology Metric
open LevinGrowth LevinDensity LevinIndicatorModulus

namespace LevinScaledBounds

theorem rayPoint_scaled_normalizedDirection (R : ℝ) (w : ℂ) :
    rayPoint (R * ‖w‖) (normalizedDirection w) = (R : ℂ) * w := by
  have h := congrArg (fun z : ℂ => (R : ℂ) * z) (rayPoint_normalizedDirection w)
  simpa only [rayPoint, Complex.ofReal_mul, mul_assoc] using h

theorem normalizedDirection_rayPoint {s : ℝ} (hs : 0 < s) (ζ : Direction) :
    normalizedDirection (rayPoint s ζ) = ζ := by
  have hn := norm_rayPoint hs.le ζ
  have hz : rayPoint s ζ ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact hs.ne')
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  apply Subtype.ext
  unfold normalizedDirection
  rw [dif_neg hz]
  change rayPoint s ζ / (‖rayPoint s ζ‖ : ℂ) = (ζ : ℂ)
  rw [hn]
  exact mul_div_cancel_left₀ _ hsC

/-- The exact change from normalization at `R * ‖w‖` to normalization at `R`. -/
theorem scaled_error_identity (f : ℂ → ℂ) (ρ : ℝ) (h : Direction → ℝ)
    {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : 0 < ‖w‖) :
    Real.log ‖f ((R : ℂ) * w)‖ / R ^ ρ - homogeneousIndicator ρ h w =
      ‖w‖ ^ ρ * (normalizedLog f ρ (R * ‖w‖) (normalizedDirection w) -
        h (normalizedDirection w)) := by
  rw [normalizedLog, rayPoint_scaled_normalizedDirection, homogeneousIndicator,
    Real.mul_rpow hR.le hw.le]
  have hpR : R ^ ρ ≠ 0 := (Real.rpow_pos_of_pos hR ρ).ne'
  have hpw : ‖w‖ ^ ρ ≠ 0 := (Real.rpow_pos_of_pos hw ρ).ne'
  field_simp

/-- The unrestricted angular upper bound gives one upper estimate on the whole
scaled annulus `1/4 ≤ ‖w‖ ≤ 4`, including points where the function vanishes. -/
theorem eventually_scaled_upper_bound {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hreg : RadialRegular f ρ h) {a : ℝ} (ha : 0 < a) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ w : ℂ, ‖w‖ ∈ Icc (1 / 4 : ℝ) 4 →
        ‖f ((R : ℂ) * w)‖ ≤ Real.exp (R ^ ρ * (homogeneousIndicator ρ h w + a)) := by
  let t : ℝ := a / (4 : ℝ) ^ ρ
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨S, hS⟩ := eventually_atTop.1
    (LevinCriterion.uniform_upper_bounds_of_radialRegular hf hρ htype hreg t ht)
  refine ⟨max 1 (4 * S), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro R hR w hw
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hR0 : 0 < R := by linarith
  have hw0 : 0 < ‖w‖ := by linarith [hw.1]
  have hscale : S ≤ R * ‖w‖ := by
    have hRS : 4 * S ≤ R := (le_max_right _ _).trans hR
    nlinarith [hw.1]
  by_cases hz : f ((R : ℂ) * w) = 0
  · rw [hz, norm_zero]
    exact (Real.exp_pos _).le
  · have hu := hS (R * ‖w‖) hscale (normalizedDirection w)
    simp only [extendedNormalizedLog, rayPoint_scaled_normalizedDirection, if_neg hz] at hu
    have hreal := EReal.coe_le_coe_iff.mp hu
    rw [normalizedLog, rayPoint_scaled_normalizedDirection] at hreal
    have hp : 0 < (R * ‖w‖) ^ ρ := Real.rpow_pos_of_pos (mul_pos hR0 hw0) ρ
    have hlog := (div_le_iff₀ hp).mp hreal
    rw [Real.mul_rpow hR0.le hw0.le] at hlog
    have hwp : ‖w‖ ^ ρ ≤ (4 : ℝ) ^ ρ := Real.rpow_le_rpow hw0.le hw.2 hρ.le
    have herror : ‖w‖ ^ ρ * t ≤ a := by
      calc
        _ ≤ (4 : ℝ) ^ ρ * t := mul_le_mul_of_nonneg_right hwp ht.le
        _ = a := by dsimp [t]; field_simp
    have hupper : Real.log ‖f ((R : ℂ) * w)‖ ≤
        R ^ ρ * (homogeneousIndicator ρ h w + a) := by
      unfold homogeneousIndicator
      have hpos : 0 ≤ R ^ ρ := Real.rpow_nonneg hR0.le _
      nlinarith [mul_le_mul_of_nonneg_left herror hpos]
    calc
      ‖f ((R : ℂ) * w)‖ = Real.exp (Real.log ‖f ((R : ℂ) * w)‖) :=
        (Real.exp_log (norm_pos_iff.mpr hz)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hupper

/-- A single starting scale supplies nearby regular centers everywhere on the
scaled annulus. Only radial regularity is needed for this lower estimate. -/
theorem eventually_scaled_good_centers {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hρ : 0 ≤ ρ) (hreg : RadialRegular f ρ h)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ w : ℂ, ‖w‖ ∈ Icc (1 / 2 : ℝ) 3 →
        ∃ q : ℂ, ‖q - w‖ ≤ δ ∧ ‖q‖ ∈ Icc (1 / 4 : ℝ) 4 ∧
          f ((R : ℂ) * q) ≠ 0 ∧
          |Real.log ‖f ((R : ℂ) * q)‖ / R ^ ρ - homogeneousIndicator ρ h q| ≤ a := by
  obtain ⟨_, E, _, hE, hgood⟩ := hreg
  let t : ℝ := a / (4 : ℝ) ^ ρ
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨A, hA, hgoodA⟩ := hgood t ht
  obtain ⟨B, hB, hmesh⟩ := LevinGrid.eventually_good_mesh_radii hE hδ hδ1
  refine ⟨max B (2 * A), hB.trans_le (le_max_left _ _), ?_⟩
  intro R hR w hw
  have hBR : B ≤ R := (le_max_left _ _).trans hR
  have hAR : 2 * A ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 < R := hB.trans_le hBR
  obtain ⟨r, hrlo, hrhi, hrE⟩ := hmesh R hBR ‖w‖ hw
  have hrA : A ≤ r := by nlinarith [hw.1]
  have hr0 : 0 < r := hA.trans_le hrA
  let v : Direction := normalizedDirection w
  let s : ℝ := r / R
  have hslo : ‖w‖ < s := (lt_div_iff₀ hR0).2 hrlo
  have hshi : s < ‖w‖ + δ := (div_lt_iff₀ hR0).2 hrhi
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs4 : s ≤ 4 := by linarith [hw.2]
  have hRs : R * s = r := by dsimp [s]; field_simp
  let q : ℂ := rayPoint s v
  have hqn : ‖q‖ = s := norm_rayPoint hs0.le v
  have hqv : normalizedDirection q = v := normalizedDirection_rayPoint hs0 v
  have hqnear : ‖q - w‖ ≤ δ := by
    have hwrepr : (‖w‖ : ℂ) * (v : ℂ) = w := rayPoint_normalizedDirection w
    have heq : q - w = ((s - ‖w‖ : ℝ) : ℂ) * (v : ℂ) := by
      dsimp [q, rayPoint]
      rw [Complex.ofReal_sub, sub_mul, hwrepr]
    rw [heq, norm_mul, v.property, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hslo.le)]
    linarith
  have hqphysical : (R : ℂ) * q = rayPoint r v := by
    rw [← rayPoint_scaled_normalizedDirection R q, hqn, hqv, hRs]
  have hgr := hgoodA r hrA hrE v
  refine ⟨q, hqnear, ?_, ?_, ?_⟩
  · rw [hqn]
    exact ⟨by linarith [hw.1], hs4⟩
  · rw [hqphysical]
    exact hgr.1
  · rw [scaled_error_identity f ρ h hR0 (by rw [hqn]; exact hs0),
      hqn, hqv, hRs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le ρ)]
    have hsp : s ^ ρ ≤ (4 : ℝ) ^ ρ := Real.rpow_le_rpow hs0.le hs4 hρ
    calc
      s ^ ρ * |normalizedLog f ρ r v - h v| ≤ (4 : ℝ) ^ ρ * t :=
        mul_le_mul hsp hgr.2.le (abs_nonneg _) (by positivity)
      _ = a := by dsimp [t]; field_simp

/-- Uniform upper bounds and nearby regular centers, with a common scale
threshold suitable for every center of a finite annular grid. -/
theorem exists_scaled_bounds {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hreg : RadialRegular f ρ h)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      (∀ w : ℂ, ‖w‖ ∈ Icc (1 / 4 : ℝ) 4 →
        ‖f ((R : ℂ) * w)‖ ≤ Real.exp (R ^ ρ * (homogeneousIndicator ρ h w + a))) ∧
      (∀ w : ℂ, ‖w‖ ∈ Icc (1 / 2 : ℝ) 3 →
        ∃ q : ℂ, ‖q - w‖ ≤ δ ∧ ‖q‖ ∈ Icc (1 / 4 : ℝ) 4 ∧
          f ((R : ℂ) * q) ≠ 0 ∧
          |Real.log ‖f ((R : ℂ) * q)‖ / R ^ ρ - homogeneousIndicator ρ h q| ≤ a) := by
  obtain ⟨A, hA, hupper⟩ := eventually_scaled_upper_bound hf hρ htype hreg ha
  obtain ⟨B, _, hcenters⟩ := eventually_scaled_good_centers hρ.le hreg ha hδ hδ1
  refine ⟨max A B, hA.trans_le (le_max_left _ _), ?_⟩
  intro R hR
  exact ⟨hupper R ((le_max_left _ _).trans hR), hcenters R ((le_max_right _ _).trans hR)⟩

end LevinScaledBounds

#print axioms LevinScaledBounds.rayPoint_scaled_normalizedDirection
#print axioms LevinScaledBounds.normalizedDirection_rayPoint
#print axioms LevinScaledBounds.scaled_error_identity
#print axioms LevinScaledBounds.eventually_scaled_upper_bound

#print axioms LevinScaledBounds.eventually_scaled_good_centers
#print axioms LevinScaledBounds.exists_scaled_bounds
