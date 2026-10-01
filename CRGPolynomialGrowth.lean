import WasowPolynomialPhase
import Mathlib.Analysis.Complex.Liouville

/-! Polynomial global growth of an entire function forces an actual polynomial.
Cauchy's derivative estimate lowers the exponent; induction integrates the
resulting polynomial and fixes the remaining constant by Liouville. -/
set_option autoImplicit false
noncomputable section
open Set Metric Polynomial
namespace CRGPolynomialGrowth

theorem derivative_growth {f : ℂ→ℂ} (hf : Differentiable ℂ f)
    (N : ℕ) {C : ℝ} (hC : 0≤C)
    (h : ∀z, ‖f z‖≤C*(1+‖z‖)^(N+1)) :
    ∀z, ‖deriv f z‖≤(C*2^(N+1))*(1+‖z‖)^N := by
  intro z
  let R := 1+‖z‖
  have hR : 0<R := by dsimp [R]; positivity
  have hb : ∀w∈sphere z R, ‖f w‖≤C*(2*R)^(N+1) := by
    intro w hw
    have hw' : ‖w-z‖=R := by simpa only [mem_sphere, dist_eq_norm] using hw
    have hn : 1+‖w‖≤2*R := by
      have hh := norm_add_le (w-z) z
      rw [sub_add_cancel] at hh
      rw [hw'] at hh
      dsimp [R] at *
      linarith
    exact (h w).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hn _) hC)
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hf.diffContOnCl hb
  have he : C*(2*R)^(N+1)/R = (C*2^(N+1))*R^N := by
    rw [mul_pow, pow_succ R]
    field_simp
  simpa only [he, R] using hc

theorem exists_polynomial_of_growth {f : ℂ→ℂ} (hf : Differentiable ℂ f)
    (N : ℕ) {C : ℝ} (hC : 0≤C)
    (h : ∀z, ‖f z‖≤C*(1+‖z‖)^N) :
    ∃P : Polynomial ℂ, ∀z, f z=P.eval z := by
  induction N generalizing f C with
  | zero =>
    have hb : Bornology.IsBounded (range f) := by
      apply (isBounded_iff_forall_norm_le).mpr
      refine ⟨C,?_⟩
      rintro _ ⟨z,rfl⟩
      simpa using h z
    obtain ⟨c,hc⟩ := hf.exists_const_forall_eq_of_bounded hb
    exact ⟨Polynomial.C c,by simpa using hc⟩
  | succ N ih =>
    have hd : Differentiable ℂ (deriv f) := by
      intro z
      exact (hf.analyticAt z).deriv.differentiableAt
    obtain ⟨P,hP⟩ := ih hd (mul_nonneg hC (by positivity)) (derivative_growth hf N hC h)
    let Q := WasowPolynomialPhase.zeroConstantPrimitive P
    have hQ : Q.derivative=P := WasowPolynomialPhase.derivative_zeroConstantPrimitive P
    have hg : Differentiable ℂ (fun z => f z-Q.eval z) := hf.sub Q.differentiable
    have hder : ∀z, deriv (fun z => f z-Q.eval z) z=0 := by
      intro z
      change deriv (f - fun z => Q.eval z) z=0
      rw [((hf z).hasDerivAt.sub (Q.hasDerivAt z)).deriv, hQ, hP z, sub_self]
    have hconst := is_const_of_deriv_eq_zero hg hder
    refine ⟨Q+Polynomial.C (f 0-Q.eval 0),?_⟩
    intro z
    have hh := hconst z 0
    simp only [eval_add, eval_C]
    linear_combination hh

#print axioms derivative_growth
#print axioms exists_polynomial_of_growth
end CRGPolynomialGrowth
