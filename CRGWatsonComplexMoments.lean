import CRGWatsonMoments
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CRGWatson

/-- The improper complex monomial moment in a right-half-plane parameter. -/
def complexPowerMoment (m j : ℕ) (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t : ℂ) ^ j * Complex.exp (-s * (t : ℂ) ^ m)

theorem norm_powerMoment_integrand {m j : ℕ} {t : ℝ} (ht : 0 ≤ t) (s : ℂ) :
    ‖(t : ℂ) ^ j * Complex.exp (-s * (t : ℂ) ^ m)‖ =
      t ^ j * Real.exp (-s.re * t ^ m) := by
  rw [norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
    ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem integrable_complexPowerMoment {m : ℕ} (hm : 0 < m) (j : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ j * Complex.exp (-s * (t : ℂ) ^ m)) (Ioi 0) := by
  apply (integrable_realPowerMoment hm j hs).mono'
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      (t : ℂ) ^ j * Complex.exp (-s * (t : ℂ) ^ m))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact (norm_powerMoment_integrand (mem_Ioi.mp ht).le s).le

theorem hasDerivAt_complexPowerMoment {m : ℕ} (hm : 0 < m) (j : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (complexPowerMoment m j) (-complexPowerMoment m (j + m) s) s := by
  let F : ℂ → ℝ → ℂ := fun z t => (t : ℂ) ^ j * Complex.exp (-z * (t : ℂ) ^ m)
  let F' : ℂ → ℝ → ℂ := fun z t => -((t : ℂ) ^ (j + m) * Complex.exp (-z * (t : ℂ) ^ m))
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := F) (F' := F')
    (s := Metric.ball s (s.re / 2))
    (bound := fun t => t ^ (j + m) * Real.exp (-(s.re / 2) * t ^ m))
    (Metric.ball_mem_nhds s (by positivity))
    (by filter_upwards with z
        exact (by fun_prop : Continuous (F z)).aestronglyMeasurable)
    (integrable_complexPowerMoment hm j hs)
    (by exact (by fun_prop : Continuous (F' s)).aestronglyMeasurable)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      intro z hz
      have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
      have hnorm : ‖z - s‖ < s.re / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
      have hre := Complex.abs_re_le_norm (z - s)
      have hzre : s.re / 2 ≤ z.re := by
        rw [Complex.sub_re] at hre
        have hneg := neg_le_abs (z.re - s.re)
        linarith
      dsimp [F']
      rw [norm_neg, norm_powerMoment_integrand ht0 z]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [pow_nonneg ht0 m]))
        (pow_nonneg ht0 (j + m)))
    (integrable_realPowerMoment hm (j + m) (by positivity))
    (by
      filter_upwards with t
      intro z _
      dsimp [F, F']
      simpa only [id_eq, Pi.neg_apply, pow_add, neg_mul, mul_neg, mul_one, one_mul,
        mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id z).neg.mul_const ((t : ℂ) ^ m)).cexp.const_mul ((t : ℂ) ^ j)))
  change HasDerivAt (fun z => ∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ j * Complex.exp (-z * (t : ℂ) ^ m))
    (-(∫ t : ℝ in Ioi 0, (t : ℂ) ^ (j + m) * Complex.exp (-s * (t : ℂ) ^ m))) s
  simpa only [F, F', MeasureTheory.integral_neg] using hresult.2

theorem analyticOnNhd_complexPowerMoment {m : ℕ} (hm : 0 < m) (j : ℕ) :
    AnalyticOnNhd ℂ (complexPowerMoment m j) {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    exact (hasDerivAt_complexPowerMoment hm j hs).differentiableAt.differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

/-- Along positive real parameters, the complex monomial moment equals the
positive Gamma coefficient times its principal complex power. -/
theorem complexPowerMoment_gamma_ofReal {m : ℕ} (hm : 0 < m) (j : ℕ)
    {A : ℝ} (hA : 0 < A) :
    complexPowerMoment m j (A : ℂ) =
      (A : ℂ) ^ (-((((j : ℝ) + 1) / (m : ℝ)) : ℂ)) *
        ((1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ)) : ℝ) := by
  have hcast : complexPowerMoment m j (A : ℂ) = (realPowerMoment m j A : ℂ) := by
    unfold complexPowerMoment realPowerMoment
    calc
      _ = ∫ t : ℝ in Ioi 0, ((t ^ j * Real.exp (-A * t ^ m) : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp, Complex.ofReal_neg]
      _ = _ := integral_complex_ofReal
  rw [hcast, realPowerMoment_gamma hm j hA]
  have he : -((j : ℝ) + 1) / (m : ℝ) = -(((j : ℝ) + 1) / (m : ℝ)) := by ring
  rw [he]
  simp only [Complex.ofReal_mul, Complex.ofReal_cpow hA.le, Complex.ofReal_neg]
  push_cast
  ring

/-- Gamma evaluation on the entire right half-plane, obtained by analytic
continuation from the real-ray integral rather than assumed as Watson data. -/
theorem complexPowerMoment_gamma {m : ℕ} (hm : 0 < m) (j : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    complexPowerMoment m j s =
      s ^ (-((((j : ℝ) + 1) / (m : ℝ)) : ℂ)) *
        ((1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ)) : ℝ) := by
  let G : ℂ → ℂ := fun z =>
    z ^ (-((((j : ℝ) + 1) / (m : ℝ)) : ℂ)) *
      ((1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ)) : ℝ)
  have hG : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.re} := by
    intro z hz
    exact (analyticAt_id.cpow analyticAt_const (by exact Or.inl hz)).mul
      analyticAt_const
  let seq : ℕ → ℂ := fun n => 1 + 1 / ((n : ℂ) + 1)
  have ht : Tendsto seq atTop (𝓝 (1 : ℂ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
  have hneq : ∀ n : ℕ, seq n ≠ 1 := by
    intro n
    dsimp [seq]
    have hd : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    simpa only [add_eq_left] using (one_div_ne_zero hd)
  have htp : Tendsto seq atTop (𝓝[≠] (1 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Filter.Eventually.of_forall (fun n => hneq n)⟩
  have hseq : ∀ n : ℕ, complexPowerMoment m j (seq n) = G (seq n) := by
    intro n
    have hA : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by positivity
    simpa only [seq, G, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast] using complexPowerMoment_gamma_ofReal hm j hA
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), complexPowerMoment m j z = G z :=
    htp.frequently (Filter.Eventually.of_forall hseq).frequently
  exact (analyticOnNhd_complexPowerMoment hm j).eqOn_of_preconnected_of_frequently_eq hG
    (convex_halfSpace_re_gt 0).isPreconnected (by simp) hfreq hs

/-- Complex moment tails satisfy the real exponential bound solely by the
norm of the complex exponential. -/
theorem complexPowerMoment_tail_bound {m : ℕ} (hm : 0 < m) (j : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t : ℝ in Ioi 1, (t : ℂ) ^ j * Complex.exp (-s * (t : ℂ) ^ m)‖ ≤
      Real.exp (-s.re / 2) * ((s.re / 2) ^ (-((j : ℝ) + 1) / (m : ℝ)) *
        (1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ))) := by
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 :=
    fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht))
  calc
    _ ≤ ∫ t : ℝ in Ioi 1, t ^ j * Real.exp (-s.re * t ^ m) := by
      apply MeasureTheory.norm_integral_le_of_norm_le
        ((integrable_realPowerMoment hm j hs).mono_set hsub)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact (norm_powerMoment_integrand (mem_Ioi.mp (hsub ht)).le s).le
    _ ≤ _ := powerMoment_tail_bound hm j hs

/-- Every finite complex moment has the Gamma leading term and an explicit
exponentially small truncation error. -/
theorem truncated_complexPowerMoment_bound {m : ℕ} (hm : 0 < m) (j : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    ‖(∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ j * Complex.exp (-s * (t : ℂ) ^ m)) -
      (s ^ (-((((j : ℝ) + 1) / (m : ℝ)) : ℂ)) *
        ((1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ)) : ℝ))‖ ≤
      Real.exp (-s.re / 2) * ((s.re / 2) ^ (-((j : ℝ) + 1) / (m : ℝ)) *
        (1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ))) := by
  have hi := integrable_complexPowerMoment hm j hs
  have hi1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ j * Complex.exp (-s * (t : ℂ) ^ m))
      (Ioi 1) := hi.mono_set (fun t ht =>
        mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht)))
  have heq := intervalIntegral.integral_interval_add_Ioi hi hi1
  have hgamma := complexPowerMoment_gamma hm j hs
  unfold complexPowerMoment at hgamma
  rw [← hgamma]
  have hdiff : (∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ j * Complex.exp (-s * (t : ℂ) ^ m)) -
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ j * Complex.exp (-s * (t : ℂ) ^ m)) =
      -(∫ t : ℝ in Ioi 1, (t : ℂ) ^ j * Complex.exp (-s * (t : ℂ) ^ m)) := by
    rw [← heq]
    abel
  rw [hdiff, norm_neg]
  exact complexPowerMoment_tail_bound hm j hs

#print axioms hasDerivAt_complexPowerMoment
#print axioms complexPowerMoment_gamma_ofReal
#print axioms complexPowerMoment_gamma
#print axioms complexPowerMoment_tail_bound
#print axioms truncated_complexPowerMoment_bound
end CRGWatson
