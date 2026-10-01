import LevinFactorization
import LevinAnalytic
import Mathlib.Analysis.Complex.AbsMax

/-! Poisson upper bounds for logarithmic moduli with zeros.
The finite Blaschke factor is constructed from the actual analytic divisor. -/
noncomputable section
open Set Metric Complex MeasureTheory InnerProductSpace
namespace LevinPoisson

/-- The actual finite Blaschke factor has modulus at most one inside its disk. -/
theorem norm_finiteBlaschke_le_one {f : ℂ → ℂ} {S : ℝ} (hS : 0 < S)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) {z : ℂ} (hz : z ∈ closedBall 0 S) :
    ‖LevinFactorization.finiteBlaschke f S z‖ ≤ 1 := by
  have ha := LevinFactorization.analyticOnNhd_finiteBlaschke hf
  have hd : DiffContOnCl ℂ (LevinFactorization.finiteBlaschke f S) (ball 0 S) := by
    apply DifferentiableOn.diffContOnCl
    simpa [closure_ball (0 : ℂ) hS.ne'] using ha.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) S)) hd
  · intro w hw
    have hw' : w ∈ sphere (0 : ℂ) S := by
      simpa [frontier_ball (0 : ℂ) hS.ne'] using hw
    exact (LevinFactorization.norm_finiteBlaschke_on_sphere hf hw').le
  · simpa [closure_ball (0 : ℂ) hS.ne'] using hz

/-- Poisson's upper inequality for log modulus, including functions with zeros.
At a zero the mathematical extended logarithm is minus infinity; the real-valued
statement is therefore restricted to a nonzero evaluation point. -/
theorem log_norm_le_poisson_average {f : ℂ → ℂ} {S : ℝ} (hS : 0 < S)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (hf0 : f 0 ≠ 0)
    (hboundary : ∀ z ∈ sphere 0 S, f z ≠ 0)
    {w : ℂ} (hw : w ∈ ball 0 S) (hfw : f w ≠ 0) :
    Real.log ‖f w‖ ≤
      Real.circleAverage (fun z => poissonKernel 0 w z * Real.log ‖f z‖) 0 S := by
  obtain ⟨g, _, hg, hgnz, hprod, hbdy⟩ :=
    LevinFactorization.exists_zero_free_factorization hS hf hf0 hboundary
  have hnorm : ‖f w‖ ≤ ‖g w‖ := by
    rw [hprod w (ball_subset_closedBall hw), norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_finiteBlaschke_le_one hS hf
      (ball_subset_closedBall hw))
  have hlog : Real.log ‖f w‖ ≤ Real.log ‖g w‖ :=
    Real.log_le_log (norm_pos_iff.mpr hfw) hnorm
  have hhar : HarmonicOnNhd (fun z => Real.log ‖g z‖) (closedBall 0 S) :=
    fun z hz => (hg z hz).harmonicAt_log_norm (hgnz z hz)
  apply hlog.trans_eq
  rw [← hhar.circleAverage_poissonKernel_smul hw]
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hz' : z ∈ sphere (0 : ℂ) S := by simpa [abs_of_pos hS] using hz
  simp only [smul_eq_mul, Pi.mul_apply, hbdy z hz']

#print axioms norm_finiteBlaschke_le_one
#print axioms log_norm_le_poisson_average

/-- Positivity of the Poisson kernel on the outer circle. -/
theorem poissonKernel_nonneg {S : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 S) (hz : z ∈ sphere 0 S) :
    0 ≤ poissonKernel 0 w z := by
  have hS := pos_of_mem_ball hw
  have hw' : ‖w‖ < S := mem_ball_zero_iff.mp hw
  have hz' : ‖z‖ = S := mem_sphere_zero_iff_norm.mp hz
  simp only [poissonKernel_def, sub_zero, hz']
  exact div_nonneg (by nlinarith [norm_nonneg w]) (sq_nonneg _)

/-- Away from its limiting boundary point, the Poisson kernel tends uniformly
to zero. This estimate retains angular information absent from a maximum norm. -/
theorem poissonKernel_far_bound {q δ : ℝ} {v z : ℂ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hδ : 0 < δ) (hclose : 1 - q ≤ δ / 2)
    (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) (hfar : δ ≤ ‖z - v‖) :
    poissonKernel 0 ((q : ℂ) * v) z ≤ 8 * (1 - q) / δ ^ 2 := by
  have hqv : ‖(q : ℂ) * v‖ = q := by
    simp [hv, Real.norm_of_nonneg hq]
  have hvq : ‖v - (q : ℂ) * v‖ = 1 - q := by
    rw [← one_sub_mul]
    rw [norm_mul, hv, mul_one]
    rw [show (1 : ℂ) - (q : ℂ) = ((1 - q : ℝ) : ℂ) by push_cast; rfl]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - q)]
  have htri : ‖z - v‖ ≤ ‖z - (q : ℂ) * v‖ + ‖(q : ℂ) * v - v‖ := by
    simpa only [dist_eq_norm] using dist_triangle z ((q : ℂ) * v) v
  have hreverse : ‖(q : ℂ) * v - v‖ = 1 - q := by
    rw [norm_sub_rev]; exact hvq
  rw [hreverse] at htri
  have hden : δ / 2 ≤ ‖z - (q : ℂ) * v‖ := by linarith
  have hdenpos : 0 < ‖z - (q : ℂ) * v‖ := lt_of_lt_of_le (by positivity) hden
  simp only [poissonKernel_def, sub_zero, hz, hqv, one_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hdenpos)).mpr
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hsq : δ ^ 2 / 4 ≤ ‖z - (q : ℂ) * v‖ ^ 2 := by nlinarith
  have hmul : 8 * (1 - q) * (δ ^ 2 / 4) ≤
      8 * (1 - q) * ‖z - (q : ℂ) * v‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  apply (mul_le_mul_iff_of_pos_right hδsq).mp
  calc
    (1 - q ^ 2) * δ ^ 2 ≤ (2 * (1 - q)) * δ ^ 2 := by
      nlinarith [sq_nonneg (1 - q)]
    _ ≤ 8 * (1 - q) * ‖z - (q : ℂ) * v‖ ^ 2 := by nlinarith [hmul]
    _ = (8 * (1 - q) / δ ^ 2 * ‖z - (q : ℂ) * v‖ ^ 2) * δ ^ 2 := by
      field_simp

#print axioms poissonKernel_nonneg
#print axioms poissonKernel_far_bound

/-- Quantitative localization of the Poisson average near a boundary direction.
Only a small arc needs the sharp bound; the remainder has vanishing kernel mass. -/
theorem poisson_average_local_upper {u : ℂ → ℝ} {q δ a ε B : ℝ} {v : ℂ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hδ : 0 < δ) (hclose : 1 - q ≤ δ / 2)
    (hv : ‖v‖ = 1) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hu : CircleIntegrable u 0 1)
    (hbound : ∀ z ∈ sphere 0 1, u z ≤ a + B)
    (hnear : ∀ z ∈ sphere 0 1, ‖z - v‖ < δ → u z ≤ a + ε) :
    Real.circleAverage (fun z => poissonKernel 0 ((q : ℂ) * v) z * u z) 0 1 ≤
      a + ε + 8 * B * (1 - q) / δ ^ 2 := by
  let K := poissonKernel 0 ((q : ℂ) * v)
  let C := 8 * B * (1 - q) / δ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hw : (q : ℂ) * v ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    simpa [hv, Real.norm_of_nonneg hq] using hq1
  have hK : ContinuousOn K (sphere 0 |(1 : ℝ)|) := by
    dsimp [K]
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hw)
  have hKu : CircleIntegrable (fun z => K z * u z) 0 1 := by
    convert hu.continuousOn_smul hK using 1
    ext z
    rfl
  have hKa : CircleIntegrable (fun z => K z * (a + ε)) 0 1 := by
    convert (circleIntegrable_const (a + ε) 0 1).continuousOn_smul hK using 1
    ext z
    rfl
  have hKC : CircleIntegrable (fun z => K z * (a + ε) + C) 0 1 :=
    hKa.add (circleIntegrable_const C 0 1)
  have hpoint : ∀ z ∈ sphere (0 : ℂ) |(1 : ℝ)|,
      K z * u z ≤ K z * (a + ε) + C := by
    intro z hz
    have hz' : z ∈ sphere (0 : ℂ) 1 := by simpa using hz
    have hKpos : 0 ≤ K z := poissonKernel_nonneg hw hz'
    by_cases hdist : ‖z - v‖ < δ
    · exact (mul_le_mul_of_nonneg_left (hnear z hz' hdist) hKpos).trans
        (le_add_of_nonneg_right hC)
    · have hfar := poissonKernel_far_bound hq hq1 hδ hclose hv
        (mem_sphere_zero_iff_norm.mp hz') (le_of_not_gt hdist)
      have hKB : K z * B ≤ C := by
        have h := mul_le_mul_of_nonneg_right hfar hB
        calc
          K z * B ≤ (8 * (1 - q) / δ ^ 2) * B := h
          _ = C := by dsimp [C]; ring
      have huBound := mul_le_mul_of_nonneg_left (hbound z hz') hKpos
      have heps := mul_nonneg hKpos hε
      nlinarith
  have h := Real.circleAverage_mono hKu hKC hpoint
  have hmean : Real.circleAverage (fun z => K z * (a + ε)) 0 1 = a + ε := by
    convert
      (harmonicOnNhd_const (a + ε) :
        HarmonicOnNhd (fun _ : ℂ => a + ε) (closedBall 0 1)).circleAverage_poissonKernel_smul hw using 1
    congr 1
  rw [Real.circleAverage_fun_add hKa (circleIntegrable_const C 0 1), hmean,
    Real.circleAverage_const] at h
  exact h

#print axioms poisson_average_local_upper
end LevinPoisson
