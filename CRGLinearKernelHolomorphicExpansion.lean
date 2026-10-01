import CRGLinearKernelExpansion
import CRGLinearKernelEntire

/-! Endpoint expansions stated with the complex derivatives of the
holomorphic weights appearing in manuscript Corollary 5.2. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace CRGLinearKernelHolomorphicExpansion
open CRGLinearKernelIntegration CRGLinearKernelEntire

def jet (w : ℂ → ℂ) (j : ℕ) (t : ℝ) : ℂ := iteratedDeriv j w (t:ℂ)

def endpointSum (w : ℂ → ℂ) (a b : ℝ) (ζ : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, (-1 : ℂ)^j / ζ^(j+1) * endpoint (jet w j) a b ζ

theorem jet_derivative {w : ℂ → ℂ} {a b : ℝ}
    (hw : AnalyticOnNhd ℂ w (Complex.ofReal '' [[a,b]]))
    (j : ℕ) (t : ℝ) (ht : t ∈ [[a,b]]) :
    HasDerivAt (jet w j) (jet w (j+1) t) t := by
  have hj : AnalyticOnNhd ℂ (iteratedDeriv j w) (Complex.ofReal '' [[a,b]]) := by
    simpa only [iteratedDeriv_eq_iterate] using hw.iterated_deriv j
  have hh := ((hj (t:ℂ) ⟨t,ht,rfl⟩).differentiableAt.hasDerivAt.hasFDerivAt).restrictScalars ℝ
  have hc := (hh.comp t (Complex.ofRealCLM.hasFDerivAt)).hasDerivAt
  convert hc using 1 <;> first | rfl | simp [jet,iteratedDeriv_succ,Function.comp_def,ContinuousLinearMap.restrictScalars]

theorem jet_continuous {w : ℂ → ℂ} {a b : ℝ}
    (hw : AnalyticOnNhd ℂ w (Complex.ofReal '' [[a,b]])) (j : ℕ) :
    ContinuousOn (jet w j) [[a,b]] :=
  fun t ht => (jet_derivative hw j t ht).continuousAt.continuousWithinAt

theorem expansion_exact {w : ℂ → ℂ} {a b : ℝ} {ζ : ℂ}
    (hw : AnalyticOnNhd ℂ w (Complex.ofReal '' [[a,b]])) (hζ : ζ ≠ 0) (N : ℕ) :
    kernel (fun t => w (t:ℂ)) a b ζ - endpointSum w a b ζ N =
      (-1 : ℂ)^N / ζ^N * kernel (jet w N) a b ζ := by
  have hi := iterated_integration_by_parts (u := jet w) hζ
    (jet_continuous hw) (jet_derivative hw) N
  have hzero : jet w 0 = fun t : ℝ => w (t:ℂ) := by
    funext t
    exact congrFun (iteratedDeriv_zero (f := w)) (t:ℂ)
  rw [hzero] at hi
  have hi' : kernel (fun t => w (t:ℂ)) a b ζ = endpointSum w a b ζ N +
      (-1 : ℂ)^N / ζ^N * kernel (jet w N) a b ζ := by
    simpa only [endpointSum] using hi
  rw [hi']
  abel

theorem expansion_bound {w : ℂ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hw : AnalyticOnNhd ℂ w (Complex.ofReal '' [[a,b]])) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ : ℂ, ∀ c : ℝ,
      ζ ≠ 0 → 0 < c → c * ‖ζ‖ ≤ |ζ.re| →
      ‖kernel (fun t => w (t:ℂ)) a b ζ - endpointSum w a b ζ N‖ ≤
        C / c * (‖Complex.exp (ζ*(b:ℂ))‖ + ‖Complex.exp (ζ*(a:ℂ))‖) /
          ‖ζ‖^(N+1) := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa only [uIcc_of_le hab] using jet_continuous hw N)
  let C : ℝ := max M 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ t ∈ Icc a b, ‖jet w N t‖ ≤ C := by
    intro t ht
    exact (hM t ht).trans (by dsimp [C]; linarith [le_max_left M 0])
  refine ⟨C,hC,?_⟩
  intro ζ c hζ hc hgap
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hre : ζ.re ≠ 0 := by
    intro hz
    simp only [hz,abs_zero] at hgap
    exact (not_le_of_gt (mul_pos hc hn)) hgap
  rw [expansion_exact hw hζ N]
  have hr := norm_exact_remainder_le (u := jet w) hab hC.le N hbound hre
  have hden : c * ‖ζ‖^(N+1) ≤ ‖ζ‖^N * |ζ.re| := by
    rw [pow_succ]
    calc
      c * (‖ζ‖^N * ‖ζ‖) = ‖ζ‖^N * (c*‖ζ‖) := by ring
      _ ≤ ‖ζ‖^N * |ζ.re| := mul_le_mul_of_nonneg_left hgap (by positivity)
  refine hr.trans ?_
  have hh := div_le_div_of_nonneg_left
    (show 0 ≤ C * (‖Complex.exp (ζ*(b:ℂ))‖ + ‖Complex.exp (ζ*(a:ℂ))‖) by positivity)
    (show 0 < c * ‖ζ‖^(N+1) by positivity) hden
  refine hh.trans_eq ?_
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The parameter substitution in the manuscript, with a constant uniform in z. -/
theorem linearKernel_expansion_bound {w : ℂ → ℂ} {a b : ℝ} {α : ℂ}
    (hab : a ≤ b) (hw : AnalyticOnNhd ℂ w (Complex.ofReal '' [[a,b]]))
    (hα : α ≠ 0) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ∀ c : ℝ,
      z ≠ 0 → 0 < c → c * ‖α*z‖ ≤ |(α*z).re| →
      ‖linearKernel (fun t => w (t:ℂ)) a b α z - endpointSum w a b (α*z) N‖ ≤
        C / c * (‖Complex.exp ((α*z)*(b:ℂ))‖ + ‖Complex.exp ((α*z)*(a:ℂ))‖) /
          ‖z‖^(N+1) := by
  obtain ⟨C,hC,hbound⟩ := expansion_bound hab hw N
  refine ⟨C/‖α‖^(N+1),by positivity,?_⟩
  intro z c hz hc hgap
  have hb := hbound (α*z) c (mul_ne_zero hα hz) hc hgap
  dsimp [linearKernel]
  refine hb.trans_eq ?_
  simp only [norm_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

#print axioms jet_derivative
#print axioms jet_continuous
#print axioms expansion_exact
#print axioms expansion_bound
#print axioms linearKernel_expansion_bound
end CRGLinearKernelHolomorphicExpansion
