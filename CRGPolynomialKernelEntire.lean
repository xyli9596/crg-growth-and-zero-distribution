import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory Polynomial
open scoped Topology
namespace CRGPolynomialKernel

/-- The finite Laplace integral used by the polynomial kernels in Corollary 5.3. -/
def laplaceIntegral (w b : ℝ → ℂ) (lam : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..1, w t * Complex.exp (lam * b t)

theorem continuousOn_integrand {w b : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (hb : ContinuousOn b (Icc 0 1)) (lam : ℂ) :
    ContinuousOn (fun t => w t * Complex.exp (lam * b t)) (Icc 0 1) :=
  hw.mul (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hb))

theorem laplaceIntegral_integrable {w b : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (hb : ContinuousOn b (Icc 0 1)) (lam : ℂ) :
    IntervalIntegrable (fun t => w t * Complex.exp (lam * b t)) volume 0 1 :=
  (continuousOn_integrand hw hb lam).intervalIntegrable_of_Icc zero_le_one

theorem hasDerivAt_laplaceIntegral {w b : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (hb : ContinuousOn b (Icc 0 1)) (lam : ℂ) :
    HasDerivAt (laplaceIntegral w b)
      (laplaceIntegral (fun t => w t * b t) b lam) lam := by
  let S : Set (ℂ × ℝ) := Metric.closedBall lam 1 ×ˢ Icc 0 1
  have hS : IsCompact S := (isCompact_closedBall lam 1).prod isCompact_Icc
  have hwS : ContinuousOn (fun x : ℂ × ℝ => w x.2) S :=
    hw.comp continuousOn_snd (fun x hx => hx.2)
  have hbS : ContinuousOn (fun x : ℂ × ℝ => b x.2) S :=
    hb.comp continuousOn_snd (fun x hx => hx.2)
  have hF'S : ContinuousOn
      (fun x : ℂ × ℝ => w x.2 * b x.2 * Complex.exp (x.1 * b x.2)) S :=
    (hwS.mul hbS).mul
      (Complex.continuous_exp.comp_continuousOn (continuousOn_fst.mul hbS))
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hF'S
  have hresult := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => w t * Complex.exp (z * b t))
    (F' := fun z t => w t * b t * Complex.exp (z * b t))
    (s := Metric.ball lam 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds lam zero_lt_one)
    (by
      filter_upwards with z
      simpa only [uIoc_of_le zero_le_one, Pi.mul_apply] using
        ((continuousOn_integrand hw hb z).mono Ioc_subset_Icc_self).aestronglyMeasurable
          (μ := volume) measurableSet_Ioc)
    (laplaceIntegral_integrable hw hb lam)
    (by
      simpa only [uIoc_of_le zero_le_one, Pi.mul_apply] using
        ((continuousOn_integrand (hw.mul hb) hb lam).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc)
    (by
      filter_upwards with t
      intro ht z hz
      rw [uIoc_of_le zero_le_one] at ht
      exact hC (z, t) ⟨Metric.ball_subset_closedBall hz, Ioc_subset_Icc_self ht⟩)
    (intervalIntegrable_const)
    (by
      filter_upwards with t
      intro _ z _
      simpa only [id_eq, one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id z).mul_const (b t)).cexp.const_mul (w t))
  exact hresult.2

theorem differentiable_laplaceIntegral {w b : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (hb : ContinuousOn b (Icc 0 1)) :
    Differentiable ℂ (laplaceIntegral w b) :=
  fun lam => (hasDerivAt_laplaceIntegral hw hb lam).differentiableAt

/-- Corollary 5.3's actual integral, with a polynomial in the complex variable. -/
def polynomialKernel (w : ℝ → ℂ) (Q : Polynomial ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..1, w t * Complex.exp (Q.eval z * (t : ℂ) ^ m)

theorem polynomialKernel_eq_laplaceIntegral (w : ℝ → ℂ) (Q : Polynomial ℂ)
    (m : ℕ) (z : ℂ) :
    polynomialKernel w Q m z = laplaceIntegral w (fun t => (t : ℂ) ^ m) (Q.eval z) := rfl

/-- The integral is entire even for merely continuous weights. -/
theorem differentiable_polynomialKernel {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (Q : Polynomial ℂ) (m : ℕ) :
    Differentiable ℂ (polynomialKernel w Q m) := by
  change Differentiable ℂ ((laplaceIntegral w (fun t => (t : ℂ) ^ m)) ∘ fun z => Q.eval z)
  exact (differentiable_laplaceIntegral hw (by fun_prop)).comp Q.differentiable

#print axioms hasDerivAt_laplaceIntegral
#print axioms differentiable_polynomialKernel
end CRGPolynomialKernel
