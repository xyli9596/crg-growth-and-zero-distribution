import LevinIndicator

/-! Recover the unrestricted upper indicator bound from radial regularity by
Poisson localization at nearby good radii. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Metric Real Complex
open scoped Topology
open LevinGrowth
namespace LevinIndicatorUpper

/-- A fixed proportional window simultaneously controls the Poisson tail and
the rescaling of the growth normalization, even when the limiting value is negative. -/
theorem exists_ratio_window (ρ a B δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ b : ℝ, 1 < b ∧ ∀ t : ℝ, 1 < t → t < b →
      1 - 1 / t ≤ δ / 2 ∧
      t ^ ρ * (a + ε / 2 + 8 * B * (1 - 1 / t) / δ ^ 2) < a + ε := by
  let F := fun t : ℝ => t ^ ρ * (a + ε / 2 + 8 * B * (1 - 1 / t) / δ ^ 2)
  have hF : ContinuousAt F 1 := by dsimp [F]; fun_prop (disch := norm_num)
  have hQ : ContinuousAt (fun t : ℝ => 1 - 1 / t) 1 := by fun_prop (disch := norm_num)
  have hFlim : ∀ᶠ t in 𝓝 (1 : ℝ), F t < a + ε :=
    hF.eventually (gt_mem_nhds (by simp [F]; linarith))
  have hQlim : ∀ᶠ t in 𝓝 (1 : ℝ), 1 - 1 / t < δ / 2 :=
    hQ.eventually (gt_mem_nhds (by simpa using (half_pos hδ)))
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp (hFlim.and hQlim)
  refine ⟨1 + d, by linarith, fun t ht htb => ?_⟩
  have htball : t ∈ ball (1 : ℝ) d := by
    rw [mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < t - 1)]
    linarith
  exact ⟨(hball htball).2.le, (hball htball).1⟩

/-- Poisson's upper inequality after scaling a good circle to the unit circle
and normalizing its logarithmic modulus. -/
theorem scaled_poisson_upper {f : ℂ → ℂ} {S ρ q : ℝ} {v : ℂ}
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) (hS : 0 < S)
    (hq : 0 ≤ q) (hq1 : q < 1) (hv : ‖v‖ = 1)
    (hboundary : ∀ z ∈ sphere (0 : ℂ) 1, f ((S : ℂ) * z) ≠ 0)
    (hfv : f ((S : ℂ) * ((q : ℂ) * v)) ≠ 0) :
    Real.log ‖f ((S : ℂ) * ((q : ℂ) * v))‖ / S ^ ρ ≤
      Real.circleAverage (fun z => poissonKernel 0 ((q : ℂ) * v) z *
        (Real.log ‖f ((S : ℂ) * z)‖ / S ^ ρ)) 0 1 := by
  let F : ℂ → ℂ := fun z => f ((S : ℂ) * z)
  have hF : Differentiable ℂ F := hf.comp (by fun_prop)
  have hFA : AnalyticOnNhd ℂ F (closedBall 0 1) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF).mono (subset_univ _)
  have hw : (q : ℂ) * v ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    simpa [hv, Real.norm_of_nonneg hq] using hq1
  have h := LevinPoisson.log_norm_le_poisson_average (f := F) (S := 1) (by norm_num)
    hFA (by simpa [F] using hf0) hboundary hw hfv
  have hp : 0 < S ^ ρ := Real.rpow_pos_of_pos hS _
  apply (div_le_div_of_nonneg_right h hp.le).trans_eq
  change Real.circleAverage (fun z => poissonKernel 0 ((q : ℂ) * v) z * Real.log ‖F z‖) 0 1 / S ^ ρ = _
  symm
  calc
    _ = Real.circleAverage (fun z => (S ^ ρ)⁻¹ •
        (poissonKernel 0 ((q : ℂ) * v) z * Real.log ‖F z‖)) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z _
      dsimp [F]
      ring
    _ = (S ^ ρ)⁻¹ • Real.circleAverage
        (fun z => poissonKernel 0 ((q : ℂ) * v) z * Real.log ‖F z‖) 0 1 :=
      Real.circleAverage_fun_smul
    _ = _ := by simp only [smul_eq_mul]; ring

/-- A single ratio window works for all limiting values in a fixed bounded interval. -/
theorem exists_uniform_ratio_window (ρ M B δ ε : ℝ) (_hM : 0 ≤ M)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ b : ℝ, 1 < b ∧ ∀ t : ℝ, 1 < t → t < b →
      1 - 1 / t ≤ δ / 2 ∧ ∀ a : ℝ, |a| ≤ M →
      t ^ ρ * (a + ε / 2 + 8 * B * (1 - 1 / t) / δ ^ 2) < a + ε := by
  let F := fun t : ℝ =>
    t ^ ρ * (ε / 2 + 8 * B * (1 - 1 / t) / δ ^ 2) + |t ^ ρ - 1| * M
  have hF : ContinuousAt F 1 := by dsimp [F]; fun_prop (disch := norm_num)
  have hQ : ContinuousAt (fun t : ℝ => 1 - 1 / t) 1 := by
    fun_prop (disch := norm_num)
  have hFlim : ∀ᶠ t in 𝓝 (1 : ℝ), F t < ε :=
    hF.eventually (gt_mem_nhds (by simp [F]; linarith))
  have hQlim : ∀ᶠ t in 𝓝 (1 : ℝ), 1 - 1 / t < δ / 2 :=
    hQ.eventually (gt_mem_nhds (by simpa using half_pos hδ))
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp (hFlim.and hQlim)
  refine ⟨1 + d, by linarith, fun t ht htb => ?_⟩
  have htball : t ∈ ball (1 : ℝ) d := by
    rw [mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < t - 1)]
    linarith
  refine ⟨(hball htball).2.le, fun a ha => ?_⟩
  have hprod : (t ^ ρ - 1) * a ≤ |t ^ ρ - 1| * M := by
    calc
      _ ≤ |(t ^ ρ - 1) * a| := le_abs_self _
      _ = |t ^ ρ - 1| * |a| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
  have hFt := (hball htball).1
  dsimp [F] at hFt
  nlinarith

/-- Radial regularity gives the unrestricted normalized upper bound uniformly
in direction. The Poisson argument fills every omitted radius. -/
theorem uniform_upper_bounds {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hreg : RadialRegular f ρ h) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in atTop, ∀ ζ : Direction,
      extendedNormalizedLog f ρ r ζ ≤ (h ζ + ε : EReal) := by
  rcases hreg with ⟨hh, E, _hEm, hEz, hlim⟩
  obtain ⟨M, hMpos, hM⟩ := (isCompact_range hh).isBounded.exists_pos_norm_le
  have hMabs (ζ : Direction) : |h ζ| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM (h ζ) (mem_range_self ζ)
  intro ε hε
  obtain ⟨δ, hδ, hδnear⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hh)
    (ε / 4) (by positivity)
  obtain ⟨R₀, hR₀, hgood⟩ := hlim (ε / 4) (by positivity)
  let B := 2 * M + ε / 4
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨b, hb, hwindow⟩ := exists_uniform_ratio_window ρ M B δ ε hMpos.le hδ hε
  obtain ⟨R₁, hR₁, hradius⟩ :=
    LevinIndicator.eventually_exists_good_radius hEz (a := 1) (by norm_num) hb
  filter_upwards [eventually_ge_atTop (max R₀ R₁)] with r hr
  have hr₀ : R₀ ≤ r := (le_max_left _ _).trans hr
  have hr₁ : R₁ ≤ r := (le_max_right _ _).trans hr
  have hrpos : 0 < r := hR₀.trans_le hr₀
  obtain ⟨S, hrS, hSb, hSE⟩ := hradius r hr₁
  simp only [one_mul] at hrS
  have hS : 0 < S := hrpos.trans hrS
  have hSR₀ : R₀ ≤ S := hr₀.trans hrS.le
  have hboundary : ∀ z ∈ sphere (0 : ℂ) 1, f ((S : ℂ) * z) ≠ 0 := by
    intro z hz
    exact (hgood S hSR₀ hSE ⟨z, mem_sphere_zero_iff_norm.mp hz⟩).1
  let u : ℂ → ℝ := fun z => Real.log ‖f ((S : ℂ) * z)‖ / S ^ ρ
  have hu : CircleIntegrable u 0 1 := by
    have hc : ContinuousOn (fun z : ℂ => Real.log ‖f ((S : ℂ) * z)‖)
        (sphere (0 : ℂ) 1) := by
      apply ContinuousOn.log
      · exact (hf.continuous.comp (by fun_prop)).norm.continuousOn
      · intro z hz
        exact norm_ne_zero_iff.mpr (hboundary z hz)
    exact (hc.div_const (S ^ ρ)).circleIntegrable (by norm_num)
  have ht : 1 < S / r := (lt_div_iff₀ hrpos).mpr (by simpa using hrS)
  have htb : S / r < b := (div_lt_iff₀ hrpos).mpr hSb
  have hwin := hwindow (S / r) ht htb
  have hq : 0 ≤ r / S := (div_pos hrpos hS).le
  have hq1 : r / S < 1 := (div_lt_one hS).mpr hrS
  have hqeq : 1 / (S / r) = r / S := by field_simp
  rw [hqeq] at hwin
  intro ζ
  by_cases hfr : f (rayPoint r ζ) = 0
  · simp [extendedNormalizedLog, hfr]
  have hzscale : (S : ℂ) * ((↑(r / S) : ℂ) * (ζ : ℂ)) = rayPoint r ζ := by
    have hSc : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
    simp only [rayPoint, Complex.ofReal_div]
    field_simp [hSc]
  have hupper := scaled_poisson_upper (ρ := ρ) hf hf0 hS hq hq1 ζ.property
    hboundary (by simpa only [hzscale] using hfr)
  rw [hzscale] at hupper
  have hbound : ∀ z ∈ sphere (0 : ℂ) 1, u z ≤ h ζ + B := by
    intro z hz
    let η : Direction := ⟨z, mem_sphere_zero_iff_norm.mp hz⟩
    have he := (abs_lt.mp (hgood S hSR₀ hSE η).2).2
    have hη := (abs_le.mp (hMabs η)).2
    have hζ := (abs_le.mp (hMabs ζ)).1
    change normalizedLog f ρ S η ≤ h ζ + B
    dsimp [B]
    linarith
  have hnear : ∀ z ∈ sphere (0 : ℂ) 1, ‖z - (ζ : ℂ)‖ < δ →
      u z ≤ h ζ + ε / 2 := by
    intro z hz hdist
    let η : Direction := ⟨z, mem_sphere_zero_iff_norm.mp hz⟩
    have he := (abs_lt.mp (hgood S hSR₀ hSE η).2).2
    have hηζ : dist η ζ < δ := by simpa only [Subtype.dist_eq, dist_eq_norm] using hdist
    have hhnear := hδnear hηζ
    rw [Real.dist_eq] at hhnear
    have hhupper := (abs_lt.mp hhnear).2
    change normalizedLog f ρ S η ≤ h ζ + ε / 2
    linarith
  have haverage := LevinPoisson.poisson_average_local_upper hq hq1 hδ hwin.1
    ζ.property (by positivity : 0 ≤ ε / 2) hB hu hbound hnear
  have hnormalized := hupper.trans haverage
  have hSpow : 0 < S ^ ρ := Real.rpow_pos_of_pos hS _
  have hrpow : 0 < r ^ ρ := Real.rpow_pos_of_pos hrpos _
  have hscale : normalizedLog f ρ r ζ =
      (S / r) ^ ρ * (Real.log ‖f (rayPoint r ζ)‖ / S ^ ρ) := by
    rw [Real.div_rpow hS.le hrpos.le]
    dsimp [normalizedLog]
    field_simp
  have hfinal : normalizedLog f ρ r ζ < h ζ + ε := by
    rw [hscale]
    exact (mul_le_mul_of_nonneg_left hnormalized
      (Real.rpow_nonneg (by positivity) _)).trans_lt (hwin.2 (h ζ) (hMabs ζ))
  simpa only [extendedNormalizedLog, if_neg hfr, EReal.coe_add] using
    (EReal.coe_le_coe_iff.mpr hfinal.le)

#print axioms exists_ratio_window
#print axioms scaled_poisson_upper
#print axioms exists_uniform_ratio_window
#print axioms uniform_upper_bounds
end LevinIndicatorUpper
