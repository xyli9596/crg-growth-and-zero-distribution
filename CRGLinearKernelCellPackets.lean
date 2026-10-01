import CRGPuiseuxLinearKernelCells
import CRGLinearKernelPacketExpansion
import CRGExponentialCoefficientGroups

/-! A fixed sign cell selects one genuine endpoint expansion per actual
supporting line. The monic top coefficient is retained through zero packet
components and the coefficient identity is exact. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set Polynomial Asymptotics
open scoped Topology BigOperators
namespace CRGLinearKernelCellPackets
open CRGNormalFormGoal CRGLinearKernel CRGPuiseuxLinearKernelCells
open CRGLinearKernelLineEndpoints CRGLinearKernelLinePackets CRGLinearKernelPacketExpansion
open CRGExponentialCoefficientGroups CRGPuiseuxMonic CRGPuiseuxCoordinates
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientRayTail
open CRGAsymptoticCoefficientScalarAlgebra WasowGlobalRayData WasowLaurentRayEquation
variable {n : ℕ} {D : CoefficientData n}

def kernel (D : CoefficientData n) (q : LineIndex D) : Fin (n+1) → ℂ → ℂ :=
  Fin.lastCases (fun _=>0) (packet D q.val)

def amplitude (C : Cell D) (q : LineIndex D) (j : Fin (n+1)) (x : ℂ) : ℂ :=
  Complex.exp (-((C.phase q).eval (originalPoint 1 x)))*kernel D q j (originalPoint 1 x)

@[simp] theorem kernel_last (D : CoefficientData n) (q : LineIndex D) (z : ℂ) :
    kernel D q (Fin.last n) z=0 := by simp [kernel]

@[simp] theorem kernel_castSucc (D : CoefficientData n) (q : LineIndex D) (j : Fin n) (z : ℂ) :
    kernel D q j.castSucc z=packet D q.val j z := by simp [kernel]

theorem amplitude_last (C : Cell D) (q : LineIndex D) :
    amplitude C q (Fin.last n)=(fun _ : ℂ=>0) := by
  funext x
  simp only [amplitude,kernel_last,mul_zero]

theorem amplitude_castSucc (C : Cell D) (q : LineIndex D) (j : Fin n) :
    amplitude C q j.castSucc=(fun x : ℂ=>
      Complex.exp (-(q.val*originalPoint 1 x*(C.endpoint q:ℂ)))*packet D q.val j (originalPoint 1 x)) := by
  funext x
  simp only [amplitude,kernel_castSucc,Cell.phase_eval]

theorem amplitude_exp (C : Cell D) (q : LineIndex D) (j : Fin (n+1)) (x : ℂ) :
    amplitude C q j x*Complex.exp ((C.phase q).eval (originalPoint 1 x))=
      kernel D q j (originalPoint 1 x) := by
  have he : Complex.exp (-((C.phase q).eval (originalPoint 1 x)))*
      Complex.exp ((C.phase q).eval (originalPoint 1 x))=1 := by
    rw [←Complex.exp_add,neg_add_cancel,Complex.exp_zero]
  dsimp only [amplitude]
  calc
    _ =(Complex.exp (-((C.phase q).eval (originalPoint 1 x)))*
      Complex.exp ((C.phase q).eval (originalPoint 1 x)))*kernel D q j (originalPoint 1 x) := by ring
    _ =_ := by rw [he,one_mul]

theorem coefficient_representation (C : Cell D) (E : MonicGroups D.exponential)
    (j : Fin (n+1)) (x : ℂ) :
    fullCoefficient D.coefficient j (originalPoint 1 x)=
      (∑q∈E.exponents,Complex.exp (q.eval (originalPoint 1 x))*(E.coeff q j).eval (originalPoint 1 x))+
        ∑q : LineIndex D,amplitude C q j x*Complex.exp ((C.phase q).eval (originalPoint 1 x)) := by
  classical
  simp_rw [amplitude_exp]
  rw [←E.representation]
  induction j using Fin.lastCases with
  | last => simp only [fullCoefficient_last,kernel_last,Finset.sum_const_zero,add_zero]
  | cast j =>
    simp only [fullCoefficient_castSucc,kernel_castSucc]
    have hs : (∑q : LineIndex D,packet D q.val j (originalPoint 1 x))=
        ∑q∈activeLines D,packet D q j (originalPoint 1 x) :=
      Finset.sum_coe_sort (activeLines D) (fun q : ℂ=>packet D q j (originalPoint 1 x))
    rw [hs]
    exact coefficient_eq_active_packets D j (originalPoint 1 x)

/-- The selected fixed endpoint series is nonzero in at least one lower
coefficient; every packet has zero monic top component. -/
theorem exists_packet_series (C : Cell D) (q : LineIndex D) :
    ∃A : Fin (n+1) → PowerSeries ℂ,
      (∃j,A j≠0) ∧ (∀j,PowerSeries.constantCoeff (A j)=0) ∧ A (Fin.last n)=0 ∧
      ∀θ∈C.angles,∀j : Fin (n+1),CompleteExpansion (rayFilter (direction θ)) (amplitude C q j) (A j) := by
  classical
  have hlocal (θ : ℝ) : rayFilter (direction θ)≤𝓝 (0:ℂ) :=
    (rayFilter_le_punctured (direction_ne_zero _)).trans nhdsWithin_le_nhds
  have hnon (θ : ℝ) : ∀ᶠx in rayFilter (direction θ),x≠0 :=
    (show ∀ᶠx : ℂ in 𝓝[≠] (0:ℂ),x≠0 from self_mem_nhdsWithin).filter_mono
      (rayFilter_le_punctured (direction_ne_zero _))
  by_cases hup : C.upper q=true
  · obtain ⟨B,hBn,hB0,hBe⟩ := exists_upper_packet_expansion D q.property
    let A : Fin (n+1) → PowerSeries ℂ := Fin.lastCases 0 B
    refine ⟨A,?_,?_,by simp [A],?_⟩
    · obtain ⟨j,hj⟩ := hBn
      exact ⟨j.castSucc,by simpa only [A,Fin.lastCases_castSucc] using hj⟩
    · intro j
      induction j using Fin.lastCases with
      | last => simp only [A,Fin.lastCases_last,map_zero]
      | cast j => simpa only [A,Fin.lastCases_castSucc] using hB0 j
    · intro θ hθ j
      induction j using Fin.lastCases with
      | last =>
        rw [amplitude_last]
        simp only [A,Fin.lastCases_last]
        simpa only [map_zero] using completeExpansion_const (hlocal θ) (0:ℂ)
      | cast j =>
        obtain ⟨c,hc,hcone⟩ := C.upper_cone q hup θ hθ
        rw [amplitude_castSucc]
        simp only [Cell.endpoint,hup,ite_true,A,Fin.lastCases_castSucc]
        exact
          hBe (rayFilter (direction θ)) (hlocal θ) (hnon θ) (C.norm_escape q θ hθ) c hc hcone j
  · have hlow : C.upper q=false := Bool.eq_false_iff.mpr hup
    obtain ⟨B,hBn,hB0,hBe⟩ := exists_lower_packet_expansion D q.property
    let A : Fin (n+1) → PowerSeries ℂ := Fin.lastCases 0 B
    refine ⟨A,?_,?_,by simp [A],?_⟩
    · obtain ⟨j,hj⟩ := hBn
      exact ⟨j.castSucc,by simpa only [A,Fin.lastCases_castSucc] using hj⟩
    · intro j
      induction j using Fin.lastCases with
      | last => simp only [A,Fin.lastCases_last,map_zero]
      | cast j => simpa only [A,Fin.lastCases_castSucc] using hB0 j
    · intro θ hθ j
      induction j using Fin.lastCases with
      | last =>
        rw [amplitude_last]
        simp only [A,Fin.lastCases_last]
        simpa only [map_zero] using completeExpansion_const (hlocal θ) (0:ℂ)
      | cast j =>
        obtain ⟨c,hc,hcone⟩ := C.lower_cone q hlow θ hθ
        rw [amplitude_castSucc]
        simp only [Cell.endpoint,hlow,ite_false,A,Fin.lastCases_castSucc]
        exact
          hBe (rayFilter (direction θ)) (hlocal θ) (hnon θ) (C.norm_escape q θ hθ) c hc hcone j

theorem exists_all_packet_series (C : Cell D) :
    ∃A : LineIndex D → Fin (n+1) → PowerSeries ℂ,
      (∀q,∃j,A q j≠0) ∧ (∀q j,PowerSeries.constantCoeff (A q j)=0) ∧
        (∀q,A q (Fin.last n)=0) ∧
      ∀θ∈C.angles,∀q j,CompleteExpansion (rayFilter (direction θ)) (amplitude C q j) (A q j) := by
  choose A hAn hA0 hAt hAe using exists_packet_series C
  exact ⟨A,hAn,hA0,hAt,fun θ hθ q j=>hAe q θ hθ j⟩

#print axioms coefficient_representation
#print axioms exists_packet_series
#print axioms exists_all_packet_series
end CRGLinearKernelCellPackets
