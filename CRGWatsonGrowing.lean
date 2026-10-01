import CRGPolynomialKernelEntire
import CRGLinearKernelExpansion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CRGWatson

/-- The normalized part of the growing kernel away from the endpoint is
exponentially small, with a bound uniform in the whole right half-plane. -/
theorem normalized_initial_kernel_bound {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (m : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ lam : ℂ, 0 ≤ lam.re →
      ‖Complex.exp (-lam) *
        (∫ t : ℝ in (0 : ℝ)..δ, w t * Complex.exp (lam * (t : ℂ) ^ m))‖ ≤
        B * δ * Real.exp (-lam.re * (1 - δ ^ m)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hwB : ∀ t ∈ Icc 0 1, ‖w t‖ ≤ B := fun t ht =>
    (hC t ht).trans (le_max_left _ _)
  refine ⟨B, hB, fun lam hlam => ?_⟩
  have hi : ‖∫ t : ℝ in (0 : ℝ)..δ, w t * Complex.exp (lam * (t : ℂ) ^ m)‖ ≤
      (B * Real.exp (lam.re * δ ^ m)) * δ := by
    have hbound : ∀ t ∈ uIoc 0 δ,
        ‖w t * Complex.exp (lam * (t : ℂ) ^ m)‖ ≤ B * Real.exp (lam.re * δ ^ m) := by
      intro t ht
      rw [uIoc_of_le hδ0] at ht
      rw [norm_mul, Complex.norm_exp, ← Complex.ofReal_pow]
      have hre : (lam * ((t ^ m : ℝ) : ℂ)).re = lam.re * t ^ m := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [hre]
      have hpow : t ^ m ≤ δ ^ m := pow_le_pow_left₀ ht.1.le ht.2 _
      exact mul_le_mul (hwB t ⟨ht.1.le, ht.2.trans hδ1⟩)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpow hlam))
        (Real.exp_nonneg _) hB
    simpa only [sub_zero, abs_of_nonneg hδ0] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [norm_mul, Complex.norm_exp, Complex.neg_re]
  calc
    _ ≤ Real.exp (-lam.re) * ((B * Real.exp (lam.re * δ ^ m)) * δ) :=
      mul_le_mul_of_nonneg_left hi (Real.exp_nonneg _)
    _ = _ := by
      rw [show -lam.re * (1 - δ ^ m) = -lam.re + lam.re * δ ^ m by ring,
        Real.exp_add]
      ring

/-- The same initial-endpoint estimate holds for singular integrable densities;
this is what the substitution `u=t^m` requires. -/
theorem normalized_initial_density_bound {v : ℝ → ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hv : IntervalIntegrable v volume 0 δ) (lam : ℂ) (hlam : 0 ≤ lam.re) :
    ‖Complex.exp (-lam) * CRGLinearKernelIntegration.kernel v 0 δ lam‖ ≤
      (∫ t : ℝ in (0 : ℝ)..δ, ‖v t‖) * Real.exp (-lam.re * (1 - δ)) := by
  have hmajor := hv.norm.mul_const (Real.exp (lam.re * δ))
  have hi : ‖CRGLinearKernelIntegration.kernel v 0 δ lam‖ ≤
      ∫ t : ℝ in (0 : ℝ)..δ, ‖v t‖ * Real.exp (lam.re * δ) := by
    unfold CRGLinearKernelIntegration.kernel
    apply intervalIntegral.norm_integral_le_of_norm_le hδ _ hmajor
    filter_upwards with t
    intro ht
    rw [norm_mul, Complex.norm_exp]
    have hre : (lam * (t : ℂ)).re = lam.re * t := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hre]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hlam)) (norm_nonneg _)
  rw [intervalIntegral.integral_mul_const] at hi
  rw [norm_mul, Complex.norm_exp, Complex.neg_re]
  calc
    _ ≤ Real.exp (-lam.re) * ((∫ t : ℝ in (0 : ℝ)..δ, ‖v t‖) *
        Real.exp (lam.re * δ)) := mul_le_mul_of_nonneg_left hi (Real.exp_nonneg _)
    _ = _ := by
      rw [show -lam.re * (1 - δ) = -lam.re + lam.re * δ by ring, Real.exp_add]
      ring

#print axioms normalized_initial_kernel_bound
#print axioms normalized_initial_density_bound
end CRGWatson
