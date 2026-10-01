import CRGLinearKernelIntegration
import CRGPolynomialKernelEntire

/-! The actual finite-interval integrals in Corollary 5.2 are entire. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CRGLinearKernelEntire
open CRGLinearKernelIntegration CRGPolynomialKernel

theorem kernel_affine (w : ℝ → ℂ) (a b : ℝ) (ζ : ℂ) :
    kernel w a b ζ = ((b-a : ℝ) : ℂ) *
      laplaceIntegral (fun t => w (a+(b-a)*t))
        (fun t => ((a+(b-a)*t : ℝ) : ℂ)) ζ := by
  have hi := intervalIntegral.smul_integral_comp_add_mul
    (f := fun t : ℝ => w t * Complex.exp (ζ*(t:ℂ)))
    (a := 0) (b := 1) (b-a) a
  simpa [kernel,laplaceIntegral,Algebra.smul_def] using hi.symm

theorem differentiable_kernel {w : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hw : ContinuousOn w (Icc a b)) :
    Differentiable ℂ (kernel w a b) := by
  have hmaps : MapsTo (fun t : ℝ => a+(b-a)*t) (Icc 0 1) (Icc a b) := by
    intro t ht
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hab) ht.1]
    · nlinarith [mul_le_mul_of_nonneg_left ht.2 (sub_nonneg.mpr hab)]
  have hw' : ContinuousOn (fun t : ℝ => w (a+(b-a)*t)) (Icc 0 1) :=
    hw.comp (by fun_prop) hmaps
  have hb' : ContinuousOn (fun t : ℝ => ((a+(b-a)*t : ℝ) : ℂ)) (Icc 0 1) := by
    fun_prop
  have heq : kernel w a b = fun ζ : ℂ => ((b-a : ℝ) : ℂ) *
      laplaceIntegral (fun t => w (a+(b-a)*t))
        (fun t => ((a+(b-a)*t : ℝ) : ℂ)) ζ := by
    funext ζ
    exact kernel_affine w a b ζ
  rw [heq]
  exact (differentiable_laplaceIntegral hw' hb').const_mul _

def linearKernel (w : ℝ → ℂ) (a b : ℝ) (α z : ℂ) : ℂ :=
  kernel w a b (α*z)

theorem differentiable_linearKernel {w : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hw : ContinuousOn w (Icc a b)) (α : ℂ) :
    Differentiable ℂ (linearKernel w a b α) :=
  (differentiable_kernel hab hw).comp ((differentiable_id).const_mul α)

#print axioms kernel_affine
#print axioms differentiable_kernel
#print axioms differentiable_linearKernel
end CRGLinearKernelEntire
