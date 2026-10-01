import CRGLinearKernelEntire
import CRGPolynomialKernelNonvanishing
import CRGPuiseuxCoordinates

/-! A fixed nonzero all-order endpoint series for an actual analytic
finite-interval weight. It is constructed by an exact affine change of
variables and the proved uniform Watson expansion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology Interval
namespace CRGLinearKernelSourceExpansion
open CRGLinearKernelIntegration CRGLinearKernelEntire CRGPolynomialKernel
open CRGWatson CRGPuiseuxCoordinates CRGAsymptoticCoefficientQuotient

def affineWeight (v : ℝ → ℂ) (a b : ℝ) (t : ℝ) : ℂ :=
  ((b-a:ℝ):ℂ)*v (a+(b-a)*t)

theorem affineWeight_analytic {v : ℝ → ℂ} {a b : ℝ} (hab : a≤b)
    (hv : AnalyticOnNhd ℝ v (Icc a b)) :
    AnalyticOnNhd ℝ (affineWeight v a b) (Icc 0 1) := by
  intro t ht
  have hx : a+(b-a)*t∈Icc a b := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) ht.1,
      mul_le_mul_of_nonneg_left ht.2 (sub_nonneg.mpr hab)]
  have hc : AnalyticAt ℝ (fun x : ℝ=>a+(b-a)*x) t := by fun_prop
  exact analyticAt_const.mul ((hv _ hx).comp (f:=fun x : ℝ=>a+(b-a)*x) hc)

theorem affineWeight_nonzero {v : ℝ → ℂ} {a b : ℝ} (hab : a<b)
    (hv : ¬EqOn v 0 (Ioc a b)) : ¬EqOn (affineWeight v a b) 0 (Ioc 0 1) := by
  intro hz
  apply hv
  intro x hx
  have hL : 0<b-a := sub_pos.mpr hab
  have ht : (x-a)/(b-a)∈Ioc (0:ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr hx.1) hL
    · exact (div_le_one hL).mpr (by linarith [hx.2])
  have he : a+(b-a)*((x-a)/(b-a))=x := by field_simp;ring
  have hh := hz ht
  change ((b-a:ℝ):ℂ)*v (a+(b-a)*((x-a)/(b-a)))=0 at hh
  rw [he] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast hL.ne')

theorem kernel_affine_phase (v : ℝ → ℂ) (a b : ℝ) (ζ : ℂ) :
    kernel v a b ζ=Complex.exp (ζ*(a:ℂ))*
      laplaceIntegral (affineWeight v a b) (fun t=>(t:ℂ)) (ζ*((b-a:ℝ):ℂ)) := by
  rw [kernel_affine]
  unfold laplaceIntegral affineWeight
  rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  have he : ζ*((a+(b-a)*t:ℝ):ℂ)=ζ*(a:ℂ)+(ζ*((b-a:ℝ):ℂ))*(t:ℂ) := by
    push_cast
    ring
  rw [he,Complex.exp_add]
  ring

theorem normalized_kernel_affine (v : ℝ → ℂ) (a b : ℝ) (ζ : ℂ) :
    Complex.exp (-(ζ*(b:ℂ)))*kernel v a b ζ=
      Complex.exp (-(ζ*((b-a:ℝ):ℂ)))*
        laplaceIntegral (affineWeight v a b) (fun t=>(t:ℂ)) (ζ*((b-a:ℝ):ℂ)) := by
  rw [kernel_affine_phase,←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring

theorem kernel_reflection (v : ℝ → ℂ) (a b : ℝ) (ζ : ℂ) :
    kernel v a b ζ=kernel (fun t=>v (-t)) (-b) (-a) (-ζ) := by
  unfold kernel
  have hh := intervalIntegral.integral_comp_neg
    (f:=fun t : ℝ=>v t*Complex.exp (ζ*(t:ℂ))) (a:=-b) (b:=-a)
  simp only [neg_neg] at hh
  rw [←hh]
  apply intervalIntegral.integral_congr
  intro t _
  simp

theorem reflectedWeight_analytic {v : ℝ → ℂ} {a b : ℝ}
    (hv : AnalyticOnNhd ℝ v (Icc a b)) :
    AnalyticOnNhd ℝ (fun t=>v (-t)) (Icc (-b) (-a)) := by
  intro t ht
  have hx : -t∈Icc a b := by constructor <;> linarith [ht.1,ht.2]
  exact (hv (-t) hx).comp (f:=fun t : ℝ=>-t) (by fun_prop)

theorem reflectedWeight_nonzero {v : ℝ → ℂ} {a b : ℝ}
    (hv : ¬EqOn v 0 (Ioo a b)) :
    ¬EqOn (fun t=>v (-t)) 0 (Ioc (-b) (-a)) := by
  intro hz
  apply hv
  intro t ht
  have hx : -t∈Ioc (-b) (-a) := by constructor <;> linarith [ht.1,ht.2]
  simpa using hz hx

theorem exists_upper_completeExpansion {v : ℝ → ℂ} {a b : ℝ} {α : ℂ}
    (hab : a<b) (hα : α≠0) (hv : AnalyticOnNhd ℝ v (Icc a b))
    (hvn : ¬EqOn v 0 (Ioc a b)) :
    ∃A : PowerSeries ℂ,A≠0 ∧ PowerSeries.constantCoeff A=0 ∧
      ∀l : Filter ℂ,l≤𝓝 (0:ℂ) → (∀ᶠx in l,x≠0) →
      Tendsto (fun x=>‖α*originalPoint 1 x‖) l atTop →
      ∀c : ℝ,0<c → (∀ᶠx in l,c*‖α*originalPoint 1 x‖≤(α*originalPoint 1 x).re) →
      CompleteExpansion l (fun x=>Complex.exp (-(α*originalPoint 1 x*(b:ℂ)))*
        kernel v a b (α*originalPoint 1 x)) A := by
  let L : ℝ := b-a
  have hL : 0<L := sub_pos.mpr hab
  have hLC : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
  let g : ℂ → ℂ := fun x=>x/(α*(L:ℂ))
  have hg : AnalyticAt ℂ g 0 := by exact analyticAt_id.div_const
  have hg0 : g 0=0 := by simp [g]
  have horder : analyticOrderAt g 0≠⊤ := by
    intro hz
    have hz0 : g =ᶠ[𝓝 (0:ℂ)] (fun _=>0) := analyticOrderAt_eq_top.mp hz
    have he := hz0.deriv_eq
    have hd : deriv g 0=(α*(L:ℂ))⁻¹ := by
      simpa only [g,id_eq,one_div] using ((hasDerivAt_id (0:ℂ)).div_const (α*(L:ℂ))).deriv
    have hz' : deriv g 0=0 := by simpa using he
    exact (inv_ne_zero (mul_ne_zero hα hLC)) (hd.symm.trans hz')
  have hwa := affineWeight_analytic hab.le hv
  obtain ⟨A,hA,hA0,hAe⟩ := exists_nonzero_density_growing_completeExpansion
    (hwa.continuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1))
    (hwa.mono Ioc_subset_Icc_self) (affineWeight_nonzero hab hvn) hg hg0 horder
  refine ⟨A,hA,hA0,?_⟩
  intro l hl hx hs c hc hcone
  let s : ℂ → ℂ := fun x=>(α*originalPoint 1 x)*(L:ℂ)
  have hsn : Tendsto (fun x=>‖s x‖) l atTop := by
    have hh := hs.const_mul_atTop hL
    simpa only [s,norm_mul,Complex.norm_real,Real.norm_of_nonneg hL.le,mul_comm] using hh
  have hsc : ∀ᶠx in l,c*‖s x‖≤(s x).re := by
    filter_upwards [hcone] with x hx
    dsimp [s]
    calc
      _ = L*(c*‖α*originalPoint 1 x‖) := by
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hL.le]
        ring
      _ ≤ L*(α*originalPoint 1 x).re := mul_le_mul_of_nonneg_left hx hL.le
      _ = _ := by simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero];ring
  have hginv : ∀ᶠx in l,g x=(s x)⁻¹ := by
    filter_upwards [hx] with x hx
    simp only [g,s,originalPoint,zpow_neg,zpow_natCast,pow_one]
    field_simp
  have hh := hAe l hl s hsn c hc hsc hginv
  intro N
  apply (hh N).congr_left
  intro x
  congr 1
  exact (normalized_kernel_affine v a b (α*originalPoint 1 x)).symm

theorem exists_lower_completeExpansion {v : ℝ → ℂ} {a b : ℝ} {α : ℂ}
    (hab : a<b) (hα : α≠0) (hv : AnalyticOnNhd ℝ v (Icc a b))
    (hvn : ¬EqOn v 0 (Ioo a b)) :
    ∃A : PowerSeries ℂ,A≠0 ∧ PowerSeries.constantCoeff A=0 ∧
      ∀l : Filter ℂ,l≤𝓝 (0:ℂ) → (∀ᶠx in l,x≠0) →
      Tendsto (fun x=>‖α*originalPoint 1 x‖) l atTop →
      ∀c : ℝ,0<c → (∀ᶠx in l,c*‖α*originalPoint 1 x‖≤-(α*originalPoint 1 x).re) →
      CompleteExpansion l (fun x=>Complex.exp (-(α*originalPoint 1 x*(a:ℂ)))*
        kernel v a b (α*originalPoint 1 x)) A := by
  obtain ⟨A,hA,hA0,hAe⟩ := exists_upper_completeExpansion
    (v:=fun t=>v (-t)) (a:=-b) (b:=-a) (α:=-α)
    (by linarith) (neg_ne_zero.mpr hα) (reflectedWeight_analytic hv)
    (reflectedWeight_nonzero hvn)
  refine ⟨A,hA,hA0,?_⟩
  intro l hl hx hs c hc hcone
  have hs' : Tendsto (fun x=>‖-α*originalPoint 1 x‖) l atTop := by
    simpa only [neg_mul,norm_neg] using hs
  have hc' : ∀ᶠx in l,c*‖-α*originalPoint 1 x‖≤(-α*originalPoint 1 x).re := by
    simpa only [neg_mul,norm_neg,Complex.neg_re] using hcone
  have hh := hAe l hl hx hs' c hc hc'
  intro N
  apply (hh N).congr_left
  intro x
  dsimp only
  rw [neg_mul,←kernel_reflection]
  simp only [neg_mul,Complex.ofReal_neg,mul_neg,neg_neg]

#print axioms affineWeight_analytic
#print axioms affineWeight_nonzero
#print axioms kernel_affine_phase
#print axioms normalized_kernel_affine
#print axioms kernel_reflection
#print axioms reflectedWeight_analytic
#print axioms reflectedWeight_nonzero
#print axioms exists_upper_completeExpansion
#print axioms exists_lower_completeExpansion
end CRGLinearKernelSourceExpansion
