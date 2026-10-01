import CRGLinearKernelSubdivision

/-! Canonical supporting lines for the linear-kernel coefficients. Rescaling
uses the actual orientation of each interval, so opposite slopes on the
same line are combined with the correct real integration density. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval BigOperators
namespace CRGLinearKernelLines
open CRGLinearKernelIntegration CRGLinearKernelEntire

/-- A line through zero is represented by its slope with real part one,
or by the imaginary axis. -/
def line (α : ℂ) : ℂ := if α.re = 0 then Complex.I else
  1 + (α.im / α.re : ℝ) * Complex.I

def scale (α : ℂ) : ℝ := if α.re = 0 then α.im else α.re

theorem scale_ne_zero {α : ℂ} (hα : α ≠ 0) : scale α ≠ 0 := by
  unfold scale
  split_ifs with h
  · intro hi
    apply hα
    exact Complex.ext h hi
  · exact h

theorem slope_eq_scale_line (α : ℂ) : α = (scale α : ℂ) * line α := by
  unfold scale line
  split_ifs with h
  · apply Complex.ext <;> simp [h]
  · apply Complex.ext
    · simp
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero, zero_add, mul_one]
      exact (mul_div_cancel₀ α.im h).symm

theorem line_ne_zero (α : ℂ) : line α ≠ 0 := by
  unfold line
  split_ifs with h
  · exact Complex.I_ne_zero
  · intro he
    have hr := congrArg Complex.re he
    simp at hr

def lower (a b c : ℝ) : ℝ := min (c*a) (c*b)
def upper (a b c : ℝ) : ℝ := max (c*a) (c*b)
def density (w : ℝ → ℂ) (c : ℝ) (t : ℝ) : ℂ := ((|c|⁻¹ : ℝ) : ℂ) * w (t/c)

theorem lower_lt_upper {a b c : ℝ} (hab : a < b) (hc : c ≠ 0) :
    lower a b c < upper a b c := by
  unfold lower upper
  apply min_lt_max.mpr
  simpa only [mul_comm c] using (mul_left_inj' hc).not.mpr hab.ne

theorem rescale_mem {a b c t : ℝ} (hab : a ≤ b) (hc : c ≠ 0)
    (ht : t ∈ Icc (lower a b c) (upper a b c)) : t/c ∈ Icc a b := by
  rcases hc.lt_or_gt with hneg | hpos
  · have hmul : c*b ≤ c*a := mul_le_mul_of_nonpos_left hab hneg.le
    simp only [lower, upper, min_eq_right hmul, max_eq_left hmul] at ht
    constructor
    · exact (le_div_iff_of_neg hneg).mpr (by simpa [mul_comm] using ht.2)
    · exact (div_le_iff_of_neg hneg).mpr (by simpa [mul_comm] using ht.1)
  · have hmul : c*a ≤ c*b := mul_le_mul_of_nonneg_left hab hpos.le
    simp only [lower, upper, min_eq_left hmul, max_eq_right hmul] at ht
    constructor
    · exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm] using ht.1)
    · exact (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using ht.2)

theorem density_analytic {w : ℝ → ℂ} {a b c : ℝ}
    (hab : a ≤ b) (hc : c ≠ 0) (hw : AnalyticOnNhd ℝ w (Icc a b)) :
    AnalyticOnNhd ℝ (density w c) (Icc (lower a b c) (upper a b c)) := by
  intro t ht
  apply AnalyticAt.mul analyticAt_const
  exact (hw (t/c) (rescale_mem hab hc ht)).comp (f := fun x : ℝ=>x/c) (x := t)
    (show AnalyticAt ℝ (fun x : ℝ=>x/c) t from analyticAt_id.div_const)

/-- Exact oriented change of variables to the canonical line parameter. -/
theorem kernel_rescale (w : ℝ → ℂ) {a b c : ℝ} (hab : a ≤ b) (hc : c ≠ 0)
    (ζ : ℂ) :
    kernel w a b ((c:ℂ)*ζ) =
      kernel (density w c) (lower a b c) (upper a b c) ζ := by
  have hi := intervalIntegral.integral_comp_mul_left
    (f := fun t : ℝ => w (t/c) * Complex.exp (ζ * (t:ℂ))) (a := a) (b := b) hc
  have hleft : (fun t : ℝ => w (c*t/c) * Complex.exp (ζ * ((c*t:ℝ):ℂ))) =
      fun t : ℝ => w t * Complex.exp (((c:ℂ)*ζ)*(t:ℂ)) := by
    funext t
    rw [mul_div_cancel_left₀ t hc, Complex.ofReal_mul]
    congr 2
    ring
  rw [hleft] at hi
  change kernel w a b ((c:ℂ)*ζ) = _ at hi
  rw [hi]
  unfold density lower upper kernel
  dsimp only
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  rcases hc.lt_or_gt with hneg | hpos
  · have hmul : c*b ≤ c*a := mul_le_mul_of_nonpos_left hab hneg.le
    rw [min_eq_right hmul,max_eq_left hmul,abs_of_neg hneg]
    conv_rhs => rw [intervalIntegral.integral_symm]
    simp only [Algebra.smul_def,Complex.ofReal_inv,inv_neg,Complex.ofReal_neg,Complex.coe_algebraMap]
    ring

  · have hmul : c*a ≤ c*b := mul_le_mul_of_nonneg_left hab hpos.le
    rw [min_eq_left hmul,max_eq_right hmul,abs_of_pos hpos]
    simp only [Algebra.smul_def,Complex.ofReal_inv,Complex.coe_algebraMap]

/-- Every original slope produces an actual analytic density on its canonical
supporting line, including a slope whose real scaling is negative. -/
theorem linearKernel_on_line (w : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    {α : ℂ} (hα : α ≠ 0) (z : ℂ) :
    linearKernel w a b α z =
      kernel (density w (scale α)) (lower a b (scale α)) (upper a b (scale α))
        (line α * z) := by
  unfold linearKernel
  conv_lhs => rw [slope_eq_scale_line α, mul_assoc]
  exact kernel_rescale w hab (scale_ne_zero hα) (line α*z)

#print axioms scale_ne_zero
#print axioms slope_eq_scale_line
#print axioms line_ne_zero
#print axioms lower_lt_upper
#print axioms density_analytic
#print axioms kernel_rescale
#print axioms linearKernel_on_line
end CRGLinearKernelLines
