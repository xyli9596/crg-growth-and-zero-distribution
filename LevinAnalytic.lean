import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Tactic

/-!
Analytic ingredients for Levin's equicontinuity argument. These statements derive
zero counting and Harnack estimates from genuine holomorphy/harmonicity hypotheses.
They do not assume or prove the small-density exceptional-set equicontinuity theorem.
-/
set_option autoImplicit false

open Set Metric Real Complex InnerProductSpace
namespace CRGLevinAnalytic

/-- Jensen's inequality gives a zero-count estimate from a concrete exponential
bound, with multiplicities represented by the analytic divisor. -/
theorem zero_count_exp_bound {f : ℂ → ℂ} {c : ℂ} {r A : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A)
    (hf : AnalyticOnNhd ℂ f (closedBall c (2 * r))) (hc : f c ≠ 0)
    (hbound : ∀ z ∈ sphere c (2 * r), ‖f z‖ ≤ Real.exp A) :
    (∑ᶠ u, MeromorphicOn.divisor f (closedBall c r) u : ℤ) ≤
      (A - Real.log ‖f c‖) / Real.log 2 := by
  have hfa : AnalyticOnNhd ℂ f (closedBall c |2 * r|) := by
    simpa [abs_of_pos (by positivity : 0 < 2 * r)] using hf
  have h := hfa.sum_divisor_le (r := r) (R := 2 * r)
    (M := Real.exp A) (by simpa [abs_of_pos hr])
    (by simp only [abs_of_pos hr, abs_of_pos (by positivity : 0 < 2 * r)]; linarith)
    (by simpa using Real.one_le_exp hA) hc
    (by simpa [abs_of_pos (by positivity : 0 < 2 * r)] using hbound)
  have he : Real.exp A ≠ 0 := (Real.exp_pos A).ne'
  have hn : ‖f c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [abs_of_pos hr] at h
  have hd : 2 * r / r = 2 := by field_simp
  simpa only [Real.log_div he hn, Real.log_exp, hd] using h

/-- A finite-type bound immediately gives the expected polynomial bound on the
number of zeros. No zero-density hypothesis is assumed. -/
theorem zero_count_finite_type {f : ℂ → ℂ} {c : ℂ} {r C ρ : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f (closedBall c (2 * r))) (hc : f c = 1)
    (hbound : ∀ z ∈ sphere c (2 * r), ‖f z‖ ≤ Real.exp (C * (2 * r) ^ ρ)) :
    (∑ᶠ u, MeromorphicOn.divisor f (closedBall c r) u : ℤ) ≤
      (C * (2 * r) ^ ρ) / Real.log 2 := by
  have h := zero_count_exp_bound hr (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
    hf (by simp [hc]) hbound
  simpa [hc] using h

/-- Harnack's upper bound on a disk, proved using the Poisson formula and its
kernel estimate. Nonnegativity is required only on the boundary. -/
theorem harmonic_harnack_upper {u : ℂ → ℝ} {c w : ℂ} {R : ℝ}
    (hu : HarmonicOnNhd u (closedBall c R)) (hw : w ∈ ball c R)
    (hpos : ∀ z ∈ sphere c R, 0 ≤ u z) :
    u w ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * u c := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hui : CircleIntegrable u c R :=
    (show ContinuousOn u (sphere c |R|) by
      simpa [abs_of_pos hR] using hu.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  let K : ℝ := (R + ‖w - c‖) / (R - ‖w - c‖)
  have hki : CircleIntegrable ((Complex.re ∘ herglotzRieszKernel c w) • u) c R := by
    apply hui.continuousOn_smul
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hw)
  have hm := Real.circleAverage_mono hki (hui.const_smul (a := K)) (fun z hz => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (re_herglotzRieszKernel_le
      (by simpa [abs_of_pos hR] using hz) hw) (hpos z (by simpa [abs_of_pos hR] using hz)))
  rw [hu.circleAverage_re_herglotzRieszKernel_smul hw,
    Real.circleAverage_smul] at hm
  have hmean : Real.circleAverage u c R = u c :=
    (show HarmonicOnNhd u (closedBall c |R|) by simpa [abs_of_pos hR] using hu).circleAverage_eq
  simpa only [smul_eq_mul, hmean] using hm

/-- The complementary lower Harnack bound. -/
theorem harmonic_harnack_lower {u : ℂ → ℝ} {c w : ℂ} {R : ℝ}
    (hu : HarmonicOnNhd u (closedBall c R)) (hw : w ∈ ball c R)
    (hpos : ∀ z ∈ sphere c R, 0 ≤ u z) :
    (R - ‖w - c‖) / (R + ‖w - c‖) * u c ≤ u w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hui : CircleIntegrable u c R :=
    (show ContinuousOn u (sphere c |R|) by
      simpa [abs_of_pos hR] using hu.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  let K : ℝ := (R - ‖w - c‖) / (R + ‖w - c‖)
  have hki : CircleIntegrable ((Complex.re ∘ herglotzRieszKernel c w) • u) c R := by
    apply hui.continuousOn_smul
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hw)
  have hm := Real.circleAverage_mono (hui.const_smul (a := K)) hki (fun z hz => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (le_re_herglotzRieszKernel
      (by simpa [abs_of_pos hR] using hz) hw) (hpos z (by simpa [abs_of_pos hR] using hz)))
  rw [hu.circleAverage_re_herglotzRieszKernel_smul hw,
    Real.circleAverage_smul] at hm
  have hmean : Real.circleAverage u c R = u c :=
    (show HarmonicOnNhd u (closedBall c |R|) by simpa [abs_of_pos hR] using hu).circleAverage_eq
  simpa only [smul_eq_mul, hmean] using hm

/-- Harnack's comparison between two arbitrary interior points. This removes the
artificial requirement that the normalization point be the center of the disk. -/
theorem harmonic_harnack_two_points {u : ℂ → ℝ} {c v w : ℂ} {R : ℝ}
    (hu : HarmonicOnNhd u (closedBall c R)) (hv : v ∈ ball c R)
    (hw : w ∈ ball c R) (hpos : ∀ z ∈ sphere c R, 0 ≤ u z) :
    u w ≤ ((R + ‖w - c‖) / (R - ‖w - c‖)) *
      ((R + ‖v - c‖) / (R - ‖v - c‖)) * u v := by
  have hR := pos_of_mem_ball hw
  have hvR : ‖v - c‖ < R := mem_ball_iff_norm.mp hv
  have hwR : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hup := harmonic_harnack_upper hu hw hpos
  have hlo := harmonic_harnack_lower hu hv hpos
  have hcv : u c ≤ (R + ‖v - c‖) / (R - ‖v - c‖) * u v := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (sub_pos.mpr hvR)]
    have ht : (R - ‖v - c‖) * u c ≤ u v * (R + ‖v - c‖) := by
      rwa [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hlo
    nlinarith [ht]
  calc
    u w ≤ _ := hup
    _ ≤ ((R + ‖w - c‖) / (R - ‖w - c‖)) *
        ((R + ‖v - c‖) / (R - ‖v - c‖) * u v) :=
      mul_le_mul_of_nonneg_left hcv (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

/-- A zero-free holomorphic function bounded above has a lower logarithmic bound
inside the disk controlled by its actual value at the center. -/
theorem log_norm_lower_bound {f : ℂ → ℂ} {c w : ℂ} {R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hnz : ∀ z ∈ closedBall c R, f z ≠ 0) (hw : w ∈ ball c R)
    (hbound : ∀ z ∈ sphere c R, Real.log ‖f z‖ ≤ M) :
    M - (R + ‖w - c‖) / (R - ‖w - c‖) * (M - Real.log ‖f c‖)
      ≤ Real.log ‖f w‖ := by
  have hlog : HarmonicOnNhd (fun z => Real.log ‖f z‖) (closedBall c R) :=
    fun z hz => (hf z hz).harmonicAt_log_norm (hnz z hz)
  have h := harmonic_harnack_upper ((harmonicOnNhd_const M).sub hlog) hw
    (fun z hz => sub_nonneg.mpr (hbound z hz))
  dsimp at h
  linarith

/-- Levin's zero-free disk estimate with an arbitrary normalization point. -/
theorem log_norm_lower_bound_from_point {f : ℂ → ℂ} {c v w : ℂ} {R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hnz : ∀ z ∈ closedBall c R, f z ≠ 0) (hv : v ∈ ball c R)
    (hw : w ∈ ball c R)
    (hbound : ∀ z ∈ sphere c R, Real.log ‖f z‖ ≤ M) :
    M - ((R + ‖w - c‖) / (R - ‖w - c‖)) *
      ((R + ‖v - c‖) / (R - ‖v - c‖)) * (M - Real.log ‖f v‖)
      ≤ Real.log ‖f w‖ := by
  have hlog : HarmonicOnNhd (fun z => Real.log ‖f z‖) (closedBall c R) :=
    fun z hz => (hf z hz).harmonicAt_log_norm (hnz z hz)
  have h := harmonic_harnack_two_points ((harmonicOnNhd_const M).sub hlog) hv hw
    (fun z hz => sub_nonneg.mpr (hbound z hz))
  dsimp at h
  linarith

/-- A quantitative oscillation bound for the actual Poisson kernel on the inner
half disk. The dependence is linear in the distance between the evaluation points. -/
theorem poisson_kernel_half_disk_bound {c z v w : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : z ∈ sphere c R)
    (hv : v ∈ closedBall c (R / 2)) (hw : w ∈ closedBall c (R / 2)) :
    |(herglotzRieszKernel c v z).re - (herglotzRieszKernel c w z).re| ≤
      8 / R * ‖v - w‖ := by
  have hzR : ‖z - c‖ = R := mem_sphere_iff_norm.mp hz
  have hvR : ‖v - c‖ ≤ R / 2 := mem_closedBall_iff_norm.mp hv
  have hwR : ‖w - c‖ ≤ R / 2 := mem_closedBall_iff_norm.mp hw
  have hnv : R / 2 ≤ ‖(z - c) - (v - c)‖ := by
    have h := norm_sub_norm_le (z - c) (v - c)
    rw [hzR] at h
    linarith
  have hnw : R / 2 ≤ ‖(z - c) - (w - c)‖ := by
    have h := norm_sub_norm_le (z - c) (w - c)
    rw [hzR] at h
    linarith
  have hne_v : (z - c) - (v - c) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hnv)
  have hne_w : (z - c) - (w - c) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hnw)
  have heq : herglotzRieszKernel c v z - herglotzRieszKernel c w z =
      2 * (z - c) * (v - w) / (((z - c) - (v - c)) * ((z - c) - (w - c))) := by
    simp only [herglotzRieszKernel_def]
    field_simp
    ring
  calc
    _ = |(herglotzRieszKernel c v z - herglotzRieszKernel c w z).re| := by rw [sub_re]
    _ ≤ ‖herglotzRieszKernel c v z - herglotzRieszKernel c w z‖ := abs_re_le_norm _
    _ = 2 * R * ‖v - w‖ /
        (‖(z - c) - (v - c)‖ * ‖(z - c) - (w - c)‖) := by
      rw [heq, norm_div, norm_mul, norm_mul, norm_mul, hzR]
      norm_num
    _ ≤ (2 * R * ‖v - w‖) / ((R / 2) * (R / 2)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul hnv hnw (by positivity) (norm_nonneg _)
    _ = _ := by field_simp; ring

/-- The Poisson formula gives a Lipschitz bound for every real harmonic function
bounded on the outer circle, without assuming equicontinuity as an input. -/
theorem harmonic_half_disk_oscillation {u : ℂ → ℝ} {c v w : ℂ} {R M : ℝ}
    (hR : 0 < R) (hu : HarmonicOnNhd u (closedBall c R))
    (hv : v ∈ closedBall c (R / 2)) (hw : w ∈ closedBall c (R / 2))
    (hbound : ∀ z ∈ sphere c R, |u z| ≤ M) :
    |u v - u w| ≤ (8 * M / R) * ‖v - w‖ := by
  have hvi : v ∈ ball c R := by
    rw [mem_ball_iff_norm]
    have h := mem_closedBall_iff_norm.mp hv
    linarith
  have hwi : w ∈ ball c R := by
    rw [mem_ball_iff_norm]
    have h := mem_closedBall_iff_norm.mp hw
    linarith
  have hui : CircleIntegrable u c R :=
    (show ContinuousOn u (sphere c |R|) by
      simpa [abs_of_pos hR] using hu.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  have hki (x : ℂ) (hx : x ∈ ball c R) :
      CircleIntegrable ((Complex.re ∘ herglotzRieszKernel c x) • u) c R := by
    apply hui.continuousOn_smul
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hx)
  rw [← hu.circleAverage_re_herglotzRieszKernel_smul hvi,
    ← hu.circleAverage_re_herglotzRieszKernel_smul hwi,
    ← Real.circleAverage_sub (hki v hvi) (hki w hwi)]
  apply Real.abs_circleAverage_le_circleAverage_abs.trans
  apply Real.circleAverage_mono_on_of_le_circle ((hki v hvi).sub (hki w hwi)).abs
  intro z hz
  have hz' : z ∈ sphere c R := by simpa [abs_of_pos hR] using hz
  change |(herglotzRieszKernel c v z).re * u z -
    (herglotzRieszKernel c w z).re * u z| ≤ _
  rw [← sub_mul, abs_mul]
  calc
    _ ≤ (8 / R * ‖v - w‖) * M := mul_le_mul
      (poisson_kernel_half_disk_bound hR hz' hv hw) (hbound z hz')
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Consequently the logarithmic modulus of a zero-free analytic function has
the same quantitative oscillation bound when its boundary logarithm is bounded. -/
theorem log_norm_half_disk_oscillation {f : ℂ → ℂ} {c v w : ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hnz : ∀ z ∈ closedBall c R, f z ≠ 0)
    (hv : v ∈ closedBall c (R / 2)) (hw : w ∈ closedBall c (R / 2))
    (hbound : ∀ z ∈ sphere c R, |Real.log ‖f z‖| ≤ M) :
    |Real.log ‖f v‖ - Real.log ‖f w‖| ≤ (8 * M / R) * ‖v - w‖ := by
  exact harmonic_half_disk_oscillation hR
    (fun z hz => (hf z hz).harmonicAt_log_norm (hnz z hz)) hv hw hbound

/-- A one-sided logarithmic growth bound and one non-small value imply a genuine
interior oscillation estimate for a zero-free analytic function. In particular,
no equicontinuity or lower bound at other points is hidden in the assumptions. -/
theorem log_norm_quarter_disk_oscillation {f : ℂ → ℂ} {c v w : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hnz : ∀ z ∈ closedBall c R, f z ≠ 0)
    (hv : v ∈ closedBall c (R / 4)) (hw : w ∈ closedBall c (R / 4))
    (hbound : ∀ z ∈ closedBall c R, Real.log ‖f z‖ ≤ M)
    (hcenter : -M ≤ Real.log ‖f c‖) :
    |Real.log ‖f v‖ - Real.log ‖f w‖| ≤ (80 * M / R) * ‖v - w‖ := by
  have hm : ∀ z ∈ sphere c (R / 2), |Real.log ‖f z‖| ≤ 5 * M := by
    intro z hz
    have hzR : ‖z - c‖ = R / 2 := mem_sphere_iff_norm.mp hz
    have hzi : z ∈ ball c R := by rw [mem_ball_iff_norm, hzR]; linarith
    have hlo := log_norm_lower_bound hf hnz hzi
      (fun x hx => hbound x (sphere_subset_closedBall hx))
    have hratio : (R + ‖z - c‖) / (R - ‖z - c‖) = 3 := by
      rw [hzR]
      field_simp
      ring
    rw [hratio] at hlo
    have hup := hbound z (ball_subset_closedBall hzi)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hhalf : closedBall c (R / 2) ⊆ closedBall c R :=
    closedBall_subset_closedBall (by linarith)
  have hquarter : (R / 2) / 2 = R / 4 := by ring
  have hv' : v ∈ closedBall c ((R / 2) / 2) := by simpa only [hquarter] using hv
  have hw' : w ∈ closedBall c ((R / 2) / 2) := by simpa only [hquarter] using hw
  have h := log_norm_half_disk_oscillation (by positivity : 0 < R / 2)
    (hf.mono hhalf) (fun z hz => hnz z (hhalf hz)) hv' hw' hm
  have heq : 8 * (5 * M) / (R / 2) = 80 * M / R := by ring
  simpa only [heq] using h

/-- At a growing radius the normalization by `r^ρ` cancels the harmonic
oscillation scale. This is a uniform Lipschitz estimate on the unit disk for the
zero-free factor that remains after the local zeros have been removed. -/
theorem normalized_log_norm_oscillation {f : ℂ → ℂ} {v w : ℂ} {r A ρ : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (4 * r)))
    (hnz : ∀ z ∈ closedBall 0 (4 * r), f z ≠ 0)
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hbound : ∀ z ∈ closedBall 0 (4 * r), Real.log ‖f z‖ ≤ A * r ^ ρ)
    (hcenter : -(A * r ^ ρ) ≤ Real.log ‖f 0‖) :
    |Real.log ‖f ((r : ℂ) * v)‖ / r ^ ρ - Real.log ‖f ((r : ℂ) * w)‖ / r ^ ρ|
      ≤ 20 * A * ‖v - w‖ := by
  have hpow : 0 < r ^ ρ := Real.rpow_pos_of_pos hr _
  have hv' : (r : ℂ) * v ∈ closedBall 0 ((4 * r) / 4) := by
    rw [mem_closedBall_iff_norm, sub_zero, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hw' : (r : ℂ) * w ∈ closedBall 0 ((4 * r) / 4) := by
    rw [mem_closedBall_iff_norm, sub_zero, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have h := log_norm_quarter_disk_oscillation (by positivity : 0 < 4 * r)
    (mul_nonneg hA hpow.le) hf hnz hv' hw' hbound hcenter
  have hd : ‖(r : ℂ) * v - (r : ℂ) * w‖ = r * ‖v - w‖ := by
    rw [← mul_sub, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [hd] at h
  rw [← sub_div, abs_div, abs_of_pos hpow]
  apply (div_le_iff₀ hpow).mpr
  calc
    _ ≤ _ := h
    _ = _ := by field_simp; ring

#print axioms zero_count_exp_bound
#print axioms zero_count_finite_type
#print axioms harmonic_harnack_upper
#print axioms harmonic_harnack_lower
#print axioms harmonic_harnack_two_points
#print axioms log_norm_lower_bound
#print axioms log_norm_lower_bound_from_point
#print axioms poisson_kernel_half_disk_bound
#print axioms harmonic_half_disk_oscillation
#print axioms log_norm_half_disk_oscillation
#print axioms log_norm_quarter_disk_oscillation
#print axioms normalized_log_norm_oscillation
end CRGLevinAnalytic
