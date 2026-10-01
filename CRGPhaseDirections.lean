import WasowPhaseOrdering
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Actual exceptional directions of nonzero complex monomials. The bad
directions form a countable set on the full argument line, hence a null set.
This applies to integer and fractional powers with fixed branches. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace CRGPhaseDirections

def leadingReal (a : ℂ) (d θ : ℝ) : ℝ :=
  (a * Complex.exp (((d*θ : ℝ) : ℂ) * Complex.I)).re

theorem leadingReal_eq_cos (a : ℂ) (d θ : ℝ) :
    leadingReal a d θ = ‖a‖ * Real.cos (a.arg + d*θ) := by
  unfold leadingReal
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I a]
  rw [mul_assoc, ← Complex.exp_add]
  have h : (a.arg : ℂ)*Complex.I + ((d*θ : ℝ) : ℂ)*Complex.I =
      ((a.arg+d*θ : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [h]
  simp [Complex.mul_re, Complex.exp_re, Complex.mul_im]

theorem leadingReal_zero_countable {a : ℂ} {d : ℝ} (ha : a ≠ 0) (hd : d ≠ 0) :
    {θ : ℝ | leadingReal a d θ = 0}.Countable := by
  apply (Set.countable_range (fun k : ℤ => (((2*(k : ℝ)+1)*Real.pi/2)-a.arg)/d)).mono
  intro θ hθ
  rw [mem_ofPred_eq, leadingReal_eq_cos] at hθ
  have hc : Real.cos (a.arg+d*θ) = 0 :=
    (mul_eq_zero.mp hθ).resolve_left (norm_ne_zero_iff.mpr ha)
  obtain ⟨k,hk⟩ := Real.cos_eq_zero_iff.mp hc
  refine ⟨k,?_⟩
  apply (div_eq_iff hd).mpr
  linarith

theorem leadingReal_ae_ne_zero {a : ℂ} {d : ℝ} (ha : a ≠ 0) (hd : d ≠ 0) :
    ∀ᵐ θ : ℝ, leadingReal a d θ ≠ 0 := by
  apply ae_iff.mpr
  simpa only [not_not] using
    (leadingReal_zero_countable ha hd).measure_zero (volume : Measure ℝ)

#print axioms leadingReal_eq_cos
#print axioms leadingReal_zero_countable
#print axioms leadingReal_ae_ne_zero
end CRGPhaseDirections
