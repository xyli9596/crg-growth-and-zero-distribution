import CRGLinearKernelLines

/-! Distinct canonical supporting lines cannot share a nonzero endpoint.
The endpoint zero is kept separately by the monic equation coefficient. -/
set_option autoImplicit false
noncomputable section
namespace CRGLinearKernelLineGeometry
open CRGLinearKernelLines

theorem line_normalized (α : ℂ) : line α=Complex.I ∨ (line α).re=1 := by
  unfold line
  split_ifs with h
  · exact Or.inl rfl
  · right
    simp

/-- Only the origin can be an endpoint on two different supporting lines. -/
theorem line_eq_of_nonzero_intersection {α β : ℂ} {s t : ℝ}
    (he : line α*(s:ℂ)=line β*(t:ℂ)) (hne : line α*(s:ℂ)≠0) : line α=line β := by
  rcases line_normalized α with hα | hα <;>
    rcases line_normalized β with hβ | hβ
  · rw [hα,hβ]
  · have ht : t=0 := by
      have hr := congrArg Complex.re he
      simpa only [hα,Complex.mul_re,Complex.I_re,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,zero_mul,sub_zero,hβ,one_mul] using hr.symm
    rw [ht,Complex.ofReal_zero,mul_zero] at he
    exact (hne he).elim
  · have hs : s=0 := by
      have hr := congrArg Complex.re he
      simpa only [hβ,Complex.mul_re,Complex.I_re,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,zero_mul,sub_zero,hα,one_mul] using hr
    exact (hne (by rw [hs,Complex.ofReal_zero,mul_zero])).elim
  · have hst : s=t := by
      have hr := congrArg Complex.re he
      simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,sub_zero,hα,hβ,one_mul] using hr
    have hs : (s:ℂ)≠0 := by
      intro hs
      exact hne (by rw [hs,mul_zero])
    rw [← hst] at he
    exact mul_right_cancel₀ hs he

#print axioms line_eq_of_nonzero_intersection
end CRGLinearKernelLineGeometry
