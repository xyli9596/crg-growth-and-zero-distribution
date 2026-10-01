import CRGLinearKernelFarEndpointLower
import CRGAsymptoticCoefficientScalarAlgebra

/-! Fixed complete endpoint expansions of the actual supporting-line
packets. Zero component densities have zero formal series; at least one
component is nonzero by the genuinely surviving extreme cell. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology Interval BigOperators
namespace CRGLinearKernelPacketExpansion
open CRGLinearKernel CRGLinearKernelIntegration CRGLinearKernelLines
open CRGLinearKernelLinePackets CRGLinearKernelLineEndpoints
open CRGLinearKernelSubdivision CRGLinearKernelActiveCells
open CRGLinearKernelSourceExpansion CRGPuiseuxCoordinates
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientScalarAlgebra
open CRGLinearKernelFarEndpoint CRGLinearKernelFarEndpointLower
variable {n : ℕ}

theorem line_ne_zero_of_mem (D : CoefficientData n) {q : ℂ} (hq : q ∈ activeLines D) : q≠0 := by
  have hq' := ((mem_activeLines D q).mp hq).1
  obtain ⟨ell,_,he⟩ := Finset.mem_image.mp hq'
  rw [←he]
  exact line_ne_zero _

theorem kernel_zero_of_eqOn_Ioo {v : ℝ → ℂ} {a b : ℝ} (hab : a≤b)
    (hz : EqOn v 0 (Ioo a b)) (ζ : ℂ) : kernel v a b ζ=0 := by
  unfold kernel
  have hh : (∫t in a..b,v t*Complex.exp (ζ*(t:ℂ)))=∫t in a..b,(0:ℂ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro t ht
    simp only [hz ht,Pi.zero_apply,zero_mul]
  rw [hh]
  simp

/-- Single-cell upper expansions, including genuine zero component
weights; the latter require no nonzero-series assumption. -/
theorem exists_upper_or_zero_series {v : ℝ → ℂ} {a b : ℝ} {α : ℂ}
    (hab : a<b) (hα : α≠0) (hv : AnalyticOnNhd ℝ v (Icc a b)) :
    ∃A : PowerSeries ℂ,PowerSeries.constantCoeff A=0 ∧
      (¬EqOn v 0 (Ioc a b) → A≠0) ∧
      ∀l : Filter ℂ,l≤𝓝 (0:ℂ) → (∀ᶠx in l,x≠0) →
      Tendsto (fun x=>‖α*originalPoint 1 x‖) l atTop →
      ∀c : ℝ,0<c → (∀ᶠx in l,c*‖α*originalPoint 1 x‖≤(α*originalPoint 1 x).re) →
      CompleteExpansion l (fun x=>Complex.exp (-(α*originalPoint 1 x*(b:ℂ)))*
        kernel v a b (α*originalPoint 1 x)) A := by
  by_cases hz : EqOn v 0 (Ioc a b)
  · refine ⟨0,by simp,fun hn=>(hn hz).elim,?_⟩
    intro l hl _hx _hs c _hc _hcone
    have he : (fun x=>Complex.exp (-(α*originalPoint 1 x*(b:ℂ)))*
        kernel v a b (α*originalPoint 1 x))=(fun _=>0) := by
      funext x
      rw [kernel_zero_of_eqOn_Ioo hab.le (hz.mono Ioo_subset_Ioc_self),mul_zero]
    rw [he]
    simpa only [map_zero] using completeExpansion_const hl (0:ℂ)
  · obtain ⟨A,hA,hA0,hAe⟩ := exists_upper_completeExpansion hab hα hv hz
    exact ⟨A,hA0,fun _=>hA,hAe⟩

/-- Corresponding single-cell lower expansions. -/
theorem exists_lower_or_zero_series {v : ℝ → ℂ} {a b : ℝ} {α : ℂ}
    (hab : a<b) (hα : α≠0) (hv : AnalyticOnNhd ℝ v (Icc a b)) :
    ∃A : PowerSeries ℂ,PowerSeries.constantCoeff A=0 ∧
      (¬EqOn v 0 (Ioo a b) → A≠0) ∧
      ∀l : Filter ℂ,l≤𝓝 (0:ℂ) → (∀ᶠx in l,x≠0) →
      Tendsto (fun x=>‖α*originalPoint 1 x‖) l atTop →
      ∀c : ℝ,0<c → (∀ᶠx in l,c*‖α*originalPoint 1 x‖≤-(α*originalPoint 1 x).re) →
      CompleteExpansion l (fun x=>Complex.exp (-(α*originalPoint 1 x*(a:ℂ)))*
        kernel v a b (α*originalPoint 1 x)) A := by
  by_cases hz : EqOn v 0 (Ioo a b)
  · refine ⟨0,by simp,fun hn=>(hn hz).elim,?_⟩
    intro l hl _hx _hs c _hc _hcone
    have he : (fun x=>Complex.exp (-(α*originalPoint 1 x*(a:ℂ)))*
        kernel v a b (α*originalPoint 1 x))=(fun _=>0) := by
      funext x
      rw [kernel_zero_of_eqOn_Ioo hab.le hz,mul_zero]
    rw [he]
    simpa only [map_zero] using completeExpansion_const hl (0:ℂ)
  · obtain ⟨A,hA,hA0,hAe⟩ := exists_lower_completeExpansion hab hα hv hz
    exact ⟨A,hA0,fun _=>hA,hAe⟩

/-- The upper endpoint of a whole supporting-line packet has a fixed
nonzero vector expansion. Every other surviving cell contributes flat zero. -/
theorem exists_upper_packet_expansion (D : CoefficientData n) {q : ℂ}
    (hq : q ∈ activeLines D) :
    ∃A : Fin n → PowerSeries ℂ,(∃k,A k≠0) ∧ (∀k,PowerSeries.constantCoeff (A k)=0) ∧
      ∀l : Filter ℂ,l≤𝓝 (0:ℂ) → (∀ᶠx in l,x≠0) →
      Tendsto (fun x=>‖q*originalPoint 1 x‖) l atTop →
      ∀c : ℝ,0<c → (∀ᶠx in l,c*‖q*originalPoint 1 x‖≤(q*originalPoint 1 x).re) →
      ∀k,CompleteExpansion l (fun x=>Complex.exp (-(q*originalPoint 1 x*(upperEnd D q:ℂ)))*
        packet D q k (originalPoint 1 x)) (A k) := by
  classical
  have hα := line_ne_zero_of_mem D hq
  have hs : ∀k : Fin n,∃A : PowerSeries ℂ,PowerSeries.constantCoeff A=0 ∧
      (¬EqOn (upperDensity D q k) 0 (Ioc ((subdivision D).node (upperCell D q)) (upperEnd D q)) → A≠0) ∧
      ∀l : Filter ℂ,l≤𝓝 (0:ℂ) → (∀ᶠx in l,x≠0) →
      Tendsto (fun x=>‖q*originalPoint 1 x‖) l atTop →
      ∀c : ℝ,0<c → (∀ᶠx in l,c*‖q*originalPoint 1 x‖≤(q*originalPoint 1 x).re) →
      CompleteExpansion l (fun x=>Complex.exp (-(q*originalPoint 1 x*(upperEnd D q:ℂ)))*
        kernel (upperDensity D q k) ((subdivision D).node (upperCell D q)) (upperEnd D q)
          (q*originalPoint 1 x)) A := fun k=>exists_upper_or_zero_series
            (upper_cell_interval_positive D hq) hα (cellWeight_analytic D q k _)
  choose A hA0 hAn hAe using hs
  refine ⟨A,?_,hA0,?_⟩
  · obtain ⟨k,t,ht,hne⟩ := upperDensity_nonzero D hq
    exact ⟨k,hAn k (fun hz=>hne (hz ⟨ht.1,ht.2.le⟩))⟩
  · intro l hl hx hnorm c hc hcone k
    let F : ℕ → ℂ → ℂ := fun i x=>Complex.exp (-(q*originalPoint 1 x*(upperEnd D q:ℂ)))*
      kernel (cellWeight D q k i) ((subdivision D).node i) ((subdivision D).node (i+1))
        (q*originalPoint 1 x)
    let B : ℕ → PowerSeries ℂ := fun i=>if i=upperCell D q then A k else 0
    have hF : ∀i∈survivingCells D q,CompleteExpansion l (F i) (B i) := by
      intro i hi
      by_cases he : i=upperCell D q
      · subst i
        simpa only [F,B,if_pos rfl,upperDensity,upperEnd] using hAe k l hl hx hnorm c hc hcone
      · have hicount := ((mem_cells_iff (subdivision D) (cellWeight D q) i).mp hi).1
        have hb := normalized_far_upper_kernel_flat
          ((subdivision D).increasing i (i+1) (Nat.lt_succ_self i) (Nat.succ_le_of_lt hicount)).le
          (other_upperEnd_lt D hq hi he) (cellWeight_analytic D q k i).continuousOn
          hα hx hnorm hc hcone
        simpa only [F,B,if_neg he] using (flat_iff_zero_expansion _ _).mp hb
    have hsum := completeExpansion_sum (survivingCells D q) hF
    have hB : (∑ i∈survivingCells D q,B i)=A k := by
      simp only [B,Finset.sum_ite_eq',if_pos (upperCell_mem D hq)]
    rw [hB] at hsum
    intro N
    apply (hsum N).congr_left
    intro x
    congr 1
    simp only [F,packet,Finset.mul_sum]

/-- The lower endpoint has the analogous fixed nonzero vector expansion. -/
theorem exists_lower_packet_expansion (D : CoefficientData n) {q : ℂ}
    (hq : q ∈ activeLines D) :
    ∃A : Fin n → PowerSeries ℂ,(∃k,A k≠0) ∧ (∀k,PowerSeries.constantCoeff (A k)=0) ∧
      ∀l : Filter ℂ,l≤𝓝 (0:ℂ) → (∀ᶠx in l,x≠0) →
      Tendsto (fun x=>‖q*originalPoint 1 x‖) l atTop →
      ∀c : ℝ,0<c → (∀ᶠx in l,c*‖q*originalPoint 1 x‖≤-(q*originalPoint 1 x).re) →
      ∀k,CompleteExpansion l (fun x=>Complex.exp (-(q*originalPoint 1 x*(lowerEnd D q:ℂ)))*
        packet D q k (originalPoint 1 x)) (A k) := by
  classical
  have hα := line_ne_zero_of_mem D hq
  have hs : ∀k : Fin n,∃A : PowerSeries ℂ,PowerSeries.constantCoeff A=0 ∧
      (¬EqOn (lowerDensity D q k) 0 (Ioo (lowerEnd D q) ((subdivision D).node (lowerCell D q+1))) → A≠0) ∧
      ∀l : Filter ℂ,l≤𝓝 (0:ℂ) → (∀ᶠx in l,x≠0) →
      Tendsto (fun x=>‖q*originalPoint 1 x‖) l atTop →
      ∀c : ℝ,0<c → (∀ᶠx in l,c*‖q*originalPoint 1 x‖≤-(q*originalPoint 1 x).re) →
      CompleteExpansion l (fun x=>Complex.exp (-(q*originalPoint 1 x*(lowerEnd D q:ℂ)))*
        kernel (lowerDensity D q k) (lowerEnd D q) ((subdivision D).node (lowerCell D q+1))
          (q*originalPoint 1 x)) A := fun k=>exists_lower_or_zero_series
            (lower_cell_interval_positive D hq) hα (cellWeight_analytic D q k _)
  choose A hA0 hAn hAe using hs
  refine ⟨A,?_,hA0,?_⟩
  · obtain ⟨k,t,ht,hne⟩ := lowerDensity_nonzero D hq
    exact ⟨k,hAn k (fun hz=>hne (hz ht))⟩
  · intro l hl hx hnorm c hc hcone k
    let F : ℕ → ℂ → ℂ := fun i x=>Complex.exp (-(q*originalPoint 1 x*(lowerEnd D q:ℂ)))*
      kernel (cellWeight D q k i) ((subdivision D).node i) ((subdivision D).node (i+1))
        (q*originalPoint 1 x)
    let B : ℕ → PowerSeries ℂ := fun i=>if i=lowerCell D q then A k else 0
    have hF : ∀i∈survivingCells D q,CompleteExpansion l (F i) (B i) := by
      intro i hi
      by_cases he : i=lowerCell D q
      · subst i
        simpa only [F,B,if_pos rfl,lowerDensity,lowerEnd] using hAe k l hl hx hnorm c hc hcone
      · have hicount := ((mem_cells_iff (subdivision D) (cellWeight D q) i).mp hi).1
        have hb := normalized_far_lower_kernel_flat
          ((subdivision D).increasing i (i+1) (Nat.lt_succ_self i) (Nat.succ_le_of_lt hicount)).le
          (lowerEnd_lt_other D hq hi he) (cellWeight_analytic D q k i).continuousOn
          hα hx hnorm hc hcone
        simpa only [F,B,if_neg he] using (flat_iff_zero_expansion _ _).mp hb
    have hsum := completeExpansion_sum (survivingCells D q) hF
    have hB : (∑ i∈survivingCells D q,B i)=A k := by
      simp only [B,Finset.sum_ite_eq',if_pos (lowerCell_mem D hq)]
    rw [hB] at hsum
    intro N
    apply (hsum N).congr_left
    intro x
    congr 1
    simp only [F,packet,Finset.mul_sum]

#print axioms exists_upper_or_zero_series
#print axioms exists_lower_or_zero_series
#print axioms exists_upper_packet_expansion
#print axioms exists_lower_packet_expansion
end CRGLinearKernelPacketExpansion
