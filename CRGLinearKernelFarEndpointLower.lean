import CRGLinearKernelFarEndpoint
import CRGLinearKernelSourceExpansion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace CRGLinearKernelFarEndpointLower
open CRGLinearKernelIntegration CRGLinearKernelSourceExpansion
open CRGPuiseuxCoordinates CRGAsymptoticCoefficientQuotient CRGLinearKernelFarEndpoint

/-- An inner lower endpoint is exponentially flat relative to a strictly
smaller chosen endpoint in the left half-plane. -/
theorem normalized_far_lower_kernel_flat {v : ℝ → ℂ} {a b B : ℝ} {α : ℂ}
    (hab : a≤b) (hB : B<a) (hv : ContinuousOn v (Icc a b)) (hα : α≠0)
    {l : Filter ℂ} (hx : ∀ᶠ x in l,x≠0)
    (hs : Tendsto (fun x=>‖α*originalPoint 1 x‖) l atTop)
    {c : ℝ} (hc : 0<c)
    (hcone : ∀ᶠ x in l,c*‖α*originalPoint 1 x‖≤-(α*originalPoint 1 x).re) :
    Flat l (fun x=>Complex.exp (-(α*originalPoint 1 x*(B:ℂ)))*
      kernel v a b (α*originalPoint 1 x)) := by
  have hv' : ContinuousOn (fun t=>v (-t)) (Icc (-b) (-a)) :=
    hv.comp (by fun_prop) (by intro t ht;constructor <;> linarith [ht.1,ht.2])
  have hs' : Tendsto (fun x=>‖(-α)*originalPoint 1 x‖) l atTop := by
    simpa only [neg_mul,norm_neg] using hs
  have hc' : ∀ᶠ x in l,c*‖(-α)*originalPoint 1 x‖≤((-α)*originalPoint 1 x).re := by
    simpa only [neg_mul,norm_neg,Complex.neg_re] using hcone
  have hflat := normalized_far_upper_kernel_flat (v := fun t=>v (-t))
    (a := -b) (b := -a) (B := -B) (α := -α) (by linarith) (by linarith)
    hv' (neg_ne_zero.mpr hα) hx hs' hc hc'
  intro N
  apply (hflat N).congr_left
  intro x
  rw [neg_mul,←kernel_reflection v a b (α*originalPoint 1 x)]
  congr 2
  simp only [Complex.ofReal_neg]
  ring

#print axioms normalized_far_lower_kernel_flat
end CRGLinearKernelFarEndpointLower
