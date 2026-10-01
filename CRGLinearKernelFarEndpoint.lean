import CRGLinearKernelLineEndpoints
import CRGWatsonExpansion
import CRGAsymptoticCoefficientQuotient
import CRGPuiseuxCoordinates

/-! A cell strictly inside a chosen endpoint is exponentially flat after
normalization. This proves that deletion of zero outer cells exposes the
true endpoint series of a complete supporting-line packet. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology Interval
namespace CRGLinearKernelFarEndpoint
open CRGLinearKernelIntegration CRGPuiseuxCoordinates CRGAsymptoticCoefficientQuotient

/-- An actual continuous interval density has the expected exponential
bound uniformly in the entire right half-plane. -/
theorem normalized_upper_kernel_bound {v : ℝ → ℂ} {a b : ℝ}
    (hab : a≤b) (hv : ContinuousOn v (Icc a b)) :
    ∃ M : ℝ,0≤M ∧ ∀ ζ : ℂ,∀ B : ℝ,0≤ζ.re →
      ‖Complex.exp (-(ζ*(B:ℂ)))*kernel v a b ζ‖ ≤
        M*(b-a)*Real.exp (-ζ.re*(B-b)) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  let M : ℝ := max C 0
  have hM : 0≤M := le_max_right _ _
  have hbound : ∀ t ∈ Icc a b,‖v t‖≤M := fun t ht=>(hC t ht).trans (le_max_left _ _)
  refine ⟨M,hM,fun ζ B hζ=>?_⟩
  have hi : ‖kernel v a b ζ‖ ≤ (M*Real.exp (ζ.re*b))*(b-a) := by
    unfold kernel
    have hb : ∀ t ∈ uIoc a b,‖v t*Complex.exp (ζ*(t:ℂ))‖≤M*Real.exp (ζ.re*b) := by
      intro t ht
      rw [uIoc_of_le hab] at ht
      simp only [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,mul_zero,sub_zero]
      exact mul_le_mul (hbound t ⟨ht.1.le,ht.2⟩)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hζ)) (Real.exp_nonneg _) hM
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [norm_mul,Complex.norm_exp]
  have hre : (-(ζ*(B:ℂ))).re=-ζ.re*B := by simp
  rw [hre]
  calc
    _ ≤ Real.exp (-ζ.re*B)*((M*Real.exp (ζ.re*b))*(b-a)) :=
      mul_le_mul_of_nonneg_left hi (Real.exp_nonneg _)
    _ = _ := by
      rw [show -ζ.re*(B-b)=-ζ.re*B+ζ.re*b by ring,Real.exp_add]
      ring

/-- Every inner upper endpoint is flat relative to a strictly larger one,
with the actual parameter α/x and an arbitrary angular filter. -/
theorem normalized_far_upper_kernel_flat {v : ℝ → ℂ} {a b B : ℝ} {α : ℂ}
    (hab : a≤b) (hB : b<B) (hv : ContinuousOn v (Icc a b)) (hα : α≠0)
    {l : Filter ℂ} (hx : ∀ᶠ x in l,x≠0)
    (hs : Tendsto (fun x=>‖α*originalPoint 1 x‖) l atTop)
    {c : ℝ} (hc : 0<c)
    (hcone : ∀ᶠ x in l,c*‖α*originalPoint 1 x‖≤(α*originalPoint 1 x).re) :
    Flat l (fun x=>Complex.exp (-(α*originalPoint 1 x*(B:ℂ)))*
      kernel v a b (α*originalPoint 1 x)) := by
  obtain ⟨M,hM,hbound⟩ := normalized_upper_kernel_bound hab hv
  intro N
  have hgap : 0<B-b := sub_pos.mpr hB
  obtain ⟨K,hK,R,hR,hflat⟩ := CRGWatson.exponential_flat_bound
    (mul_pos hc hgap) (-(N:ℝ))
  apply IsBigO.of_bound (M*(b-a)*K/‖α‖^N)
  filter_upwards [hx,hcone,hs.eventually (eventually_ge_atTop R)] with x hx hcone hlarge
  have hnα : ‖α‖≠0 := norm_ne_zero_iff.mpr hα
  have hnx : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
  have hζpos : 0<‖α*originalPoint 1 x‖ := by
    have hh : 1≤‖α*originalPoint 1 x‖ := hR.trans hlarge
    linarith
  have hn : ‖α*originalPoint 1 x‖=‖α‖/‖x‖ := by
    simp only [originalPoint,zpow_neg,zpow_natCast,pow_one,norm_mul,norm_inv,div_eq_mul_inv]
  have hre : 0≤(α*originalPoint 1 x).re :=
    (mul_nonneg hc.le (norm_nonneg _)).trans hcone
  have he := hflat _ hlarge
  rw [Real.rpow_neg hζpos.le,Real.rpow_natCast] at he
  have hcoef : 0≤M*(b-a) := mul_nonneg hM (sub_nonneg.mpr hab)
  change ‖Complex.exp (-(α*originalPoint 1 x*(B:ℂ)))*kernel v a b (α*originalPoint 1 x)‖≤_
  calc
    _ ≤ M*(b-a)*Real.exp (-(α*originalPoint 1 x).re*(B-b)) := hbound _ B hre
    _ ≤ M*(b-a)*Real.exp (-(c*(B-b))*‖α*originalPoint 1 x‖) := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hcone hgap.le]
    _ ≤ M*(b-a)*(K/‖α*originalPoint 1 x‖^N) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [div_eq_mul_inv] using he) hcoef
    _ = _ := by
      rw [hn,div_pow]
      simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg x) N)]
      field_simp

#print axioms normalized_upper_kernel_bound
#print axioms normalized_far_upper_kernel_flat
end CRGLinearKernelFarEndpoint
