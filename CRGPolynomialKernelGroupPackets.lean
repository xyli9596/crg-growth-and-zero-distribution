import CRGPolynomialKernelCellSeries
import CRGExponentialExpansionGroupsBuilder

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial Asymptotics
open scoped Topology BigOperators
namespace CRGPolynomialKernel
open CRGExponentialCoefficientGroups CRGPuiseuxMonic CRGExponentialExpansionSector
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientScalarAlgebra
open CRGAsymptoticCoefficientRayTail WasowGlobalRayData CRGPuiseuxCoordinates
variable {n : ℕ} {D : CoefficientData n}

def Cell.retainedPhases (C : Cell D) (E : MonicGroups D.exponential) : Finset (Polynomial ℂ) := by
  classical
  exact (C.phaseSet E).filter (C.active E)

theorem Cell.retainedPhases_nonempty (C : Cell D) (E : MonicGroups D.exponential) :
    (C.retainedPhases E).Nonempty := by
  classical
  exact ⟨0,Finset.mem_filter.mpr ⟨C.phaseSet_zero_mem E,Or.inl rfl⟩⟩

theorem Cell.inactive_amplitude_zero (C : Cell D) (E : MonicGroups D.exponential)
    (q : Polynomial ℂ) (hq : q∈C.phaseSet E) (hnq : q∉C.retainedPhases E)
    (j : Fin (n+1)) (x : ℂ) : C.amplitude E q j x=0 := by
  classical
  have hn : ¬C.active E q := by
    intro hn
    exact hnq (Finset.mem_filter.mpr ⟨hq,hn⟩)
  have hq0 : q≠0 := fun h=>hn (Or.inl h)
  have hP : C.polynomial E q j=0 := by
    by_contra hp
    exact hn (Or.inr ⟨j,Or.inl hp⟩)
  have hv : EqOn (C.density q j) 0 (Ioc 0 1) := by
    by_contra hv
    exact hn (Or.inr ⟨j,Or.inr hv⟩)
  simp only [Cell.amplitude,growingGroupAmplitude,hP,Polynomial.eval_zero,
    integral_zero_of_zero_density _ hv,mul_zero,add_zero,if_neg hq0]

theorem Cell.exists_exponential_groups (C : Cell D) (E : MonicGroups D.exponential) :
    ∃G : Groups (fullCoefficient D.coefficient),G.denominator=C.denominator ∧
      G.clearing=C.clearing E ∧ G.angles=C.angles := by
  classical
  obtain ⟨B,hBtop,hB⟩ := C.exists_decayingSeries
  have hsource : ∀q : Polynomial ℂ,∀j : Fin (n+1),∃A : PowerSeries ℂ,
      q∈C.phaseSet E →
        (((q=0 ∧ j=Fin.last n) ∨ (q≠0 ∧
          (C.polynomial E q j≠0 ∨ ¬EqOn (C.density q j) 0 (Ioc 0 1)))) → A≠0) ∧
        ∀θ∈C.angles,CompleteExpansion (rayFilter (direction (θ/C.denominator)))
          (fun x=>x^(C.clearing E)*C.amplitude E q j x) A := by
    intro q j
    by_cases hq : q∈C.phaseSet E
    · obtain ⟨A,hAn,hA⟩ := C.exists_component_series E B hBtop hB q hq j
      exact ⟨A,fun _=>⟨hAn,hA⟩⟩
    · exact ⟨0,fun h=>False.elim (hq h)⟩
  choose A hA using hsource
  apply CRGExponentialExpansionGroupsBuilder.exists_groups
    (fullCoefficient D.coefficient) C.denominator C.positive (C.clearing E) C.angles
    (C.phaseSet E) (C.retainedPhases E) (Finset.filter_subset _ _) (C.retainedPhases_nonempty E)
    (C.phaseSet_normalized E) (C.amplitude E) A
  · intro θ hθ j
    exact Eventually.of_forall (C.amplitude_representation E j)
  · exact C.inactive_amplitude_zero E
  · intro θ hθ q hq j
    exact (hA q j (Finset.mem_filter.mp hq).1).2 θ hθ
  · intro q hq
    have hs := (Finset.mem_filter.mp hq).1
    have ha := (Finset.mem_filter.mp hq).2
    rcases ha with hq0 | ⟨j,hjn⟩
    · exact ⟨Fin.last n,(hA q (Fin.last n) hs).1 (Or.inl ⟨hq0,rfl⟩)⟩
    · by_cases hq0 : q=0
      · exact ⟨Fin.last n,(hA q (Fin.last n) hs).1 (Or.inl ⟨hq0,rfl⟩)⟩
      · exact ⟨j,(hA q j hs).1 (Or.inr ⟨hq0,hjn⟩)⟩

#print axioms Cell.exists_exponential_groups
end CRGPolynomialKernel
