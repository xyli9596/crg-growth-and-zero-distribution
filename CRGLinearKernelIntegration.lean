import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! Exact endpoint identities for the integral coefficients in manuscript
Corollary 5.2. The derivatives here are derivatives of the actual weight;
the remainder is an actual interval integral, not an assumed asymptotic. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace CRGLinearKernelIntegration

def kernel (w : ℝ → ℂ) (a b : ℝ) (ζ : ℂ) : ℂ :=
  ∫ t in a..b, w t * Complex.exp (ζ * (t : ℂ))

def endpoint (w : ℝ → ℂ) (a b : ℝ) (ζ : ℂ) : ℂ :=
  w b * Complex.exp (ζ * (b : ℂ)) - w a * Complex.exp (ζ * (a : ℂ))

theorem integration_by_parts {w w' : ℝ → ℂ} {a b : ℝ} {ζ : ℂ}
    (hζ : ζ ≠ 0) (hw : ContinuousOn w [[a,b]])
    (hw' : ContinuousOn w' [[a,b]])
    (hd : ∀ t ∈ [[a,b]], HasDerivAt w (w' t) t) :
    kernel w a b ζ = endpoint w a b ζ / ζ - kernel w' a b ζ / ζ := by
  let v : ℝ → ℂ := fun t => Complex.exp (ζ * (t : ℂ)) / ζ
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hdv : ∀ t : ℝ, HasDerivAt v (Complex.exp (ζ * (t : ℂ))) t := by
    intro t
    dsimp [v]
    simpa [hζ] using (((Complex.ofRealCLM.hasDerivAt).const_mul ζ).cexp.div_const ζ)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hw hv.continuousOn (fun t ht => hd t (mem_Icc_of_Ioo ht))
    (fun t _ => hdv t) hw'.intervalIntegrable
    (by exact (show Continuous (fun t : ℝ => Complex.exp (ζ * (t : ℂ))) by
      fun_prop).intervalIntegrable a b)
  simpa only [kernel, endpoint, v, ← mul_div_assoc, intervalIntegral.integral_div,
    sub_div] using hi

/-- Any finite number of integrations by parts, including its exact remainder. -/
theorem iterated_integration_by_parts {u : ℕ → ℝ → ℂ} {a b : ℝ} {ζ : ℂ}
    (hζ : ζ ≠ 0) (hu : ∀ j, ContinuousOn (u j) [[a,b]])
    (hd : ∀ j t, t ∈ [[a,b]] → HasDerivAt (u j) (u (j+1) t) t) (N : ℕ) :
    kernel (u 0) a b ζ =
      (∑ j ∈ Finset.range N, (-1 : ℂ)^j / ζ^(j+1) * endpoint (u j) a b ζ) +
      (-1 : ℂ)^N / ζ^N * kernel (u N) a b ζ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ]
    rw [integration_by_parts hζ (hu N) (hu (N+1)) (hd N)]
    simp only [add_assoc]
    congr 1
    simp only [pow_succ]
    field_simp [hζ]
    ring

theorem real_exponential_integral {c a b : ℝ} (hc : c ≠ 0) :
    (∫ t in a..b, Real.exp (c*t)) = (Real.exp (c*b)-Real.exp (c*a))/c := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (c*t)/c) (Real.exp (c*t)) t := by
    intro t
    simpa [hc] using (((hasDerivAt_id t).const_mul c).exp.div_const c)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (show IntervalIntegrable (fun t => Real.exp (c*t)) volume a b from
      (show Continuous (fun t : ℝ => Real.exp (c*t)) by fun_prop).intervalIntegrable a b)
  simpa [sub_div] using hi

/-- The extra inverse power comes from integration of the exponential, rather
than from a bound of its maximum over the interval. -/
theorem norm_kernel_le {w : ℝ → ℂ} {a b M : ℝ} {ζ : ℂ}
    (hab : a ≤ b) (hM : 0 ≤ M) (hbound : ∀ t ∈ Icc a b, ‖w t‖ ≤ M)
    (hre : ζ.re ≠ 0) :
    ‖kernel w a b ζ‖ ≤
      M * (‖Complex.exp (ζ*(b:ℂ))‖ + ‖Complex.exp (ζ*(a:ℂ))‖) / |ζ.re| := by
  have hi : ‖kernel w a b ζ‖ ≤ ∫ t in a..b, M * Real.exp (ζ.re*t) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · filter_upwards with t
      intro ht
      simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right (hbound t ⟨le_of_lt ht.1,ht.2⟩)
        (Real.exp_pos _).le
    · exact (show Continuous (fun t : ℝ => M * Real.exp (ζ.re*t)) by
        fun_prop).intervalIntegrable a b
  have hexp : (∫ t in a..b, Real.exp (ζ.re*t)) ≤
      (Real.exp (ζ.re*b)+Real.exp (ζ.re*a))/|ζ.re| := by
    rw [real_exponential_integral hre]
    calc
      (Real.exp (ζ.re*b)-Real.exp (ζ.re*a))/ζ.re
          ≤ |(Real.exp (ζ.re*b)-Real.exp (ζ.re*a))/ζ.re| := le_abs_self _
      _ = |Real.exp (ζ.re*b)-Real.exp (ζ.re*a)|/|ζ.re| := abs_div _ _
      _ ≤ (Real.exp (ζ.re*b)+Real.exp (ζ.re*a))/|ζ.re| := by
        apply div_le_div_of_nonneg_right _ (abs_nonneg _)
        simpa only [sub_zero, zero_sub, abs_neg,
          abs_of_pos (Real.exp_pos _)] using
          abs_sub_le (Real.exp (ζ.re*b)) 0 (Real.exp (ζ.re*a))
  rw [intervalIntegral.integral_const_mul] at hi
  apply hi.trans
  simpa only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, mul_div_assoc] using mul_le_mul_of_nonneg_left hexp hM

theorem norm_exact_remainder_le {u : ℕ → ℝ → ℂ} {a b M : ℝ} {ζ : ℂ}
    (hab : a ≤ b) (hM : 0 ≤ M) (N : ℕ)
    (hbound : ∀ t ∈ Icc a b, ‖u N t‖ ≤ M) (hre : ζ.re ≠ 0) :
    ‖(-1 : ℂ)^N / ζ^N * kernel (u N) a b ζ‖ ≤
      M * (‖Complex.exp (ζ*(b:ℂ))‖ + ‖Complex.exp (ζ*(a:ℂ))‖) /
        (‖ζ‖^N * |ζ.re|) := by
  simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow]
  have hi := norm_kernel_le hab hM hbound hre
  have hj := mul_le_mul_of_nonneg_left hi (show 0 ≤ 1 / ‖ζ‖^N by positivity)
  refine hj.trans_eq ?_
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

#print axioms integration_by_parts
#print axioms iterated_integration_by_parts
#print axioms real_exponential_integral
#print axioms norm_kernel_le
#print axioms norm_exact_remainder_le
end CRGLinearKernelIntegration
