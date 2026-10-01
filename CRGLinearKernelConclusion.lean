import CRGLinearKernelCellPackets
import CRGLinearKernelGroupAssembly

/-! Corollary 5.2 for the actual linear-kernel source coefficients. All
supporting-line cancellations, endpoint choices, formal expansions and
finite phase families are constructed before the ODE solution is chosen. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial MeasureTheory
open scoped Topology BigOperators
namespace CRGLinearKernel
open CRGNormalFormGoal CRGExponentialCoefficients CRGExponentialCoefficientGroups
open CRGPuiseuxMonic CRGPuiseuxLinearKernelCells CRGLinearKernelCellPackets
open CRGExponentialExpansionSector CRGExponentialExpansionConclusion CRGPuiseuxProposition

theorem cell_exists_exponential_groups {n : ℕ} (D : CoefficientData n)
    (C : CRGPuiseuxLinearKernelCells.Cell D) (E : MonicGroups D.exponential) :
    ∃G : Groups (fullCoefficient D.coefficient),G.denominator=1 ∧
      G.clearing=CRGLinearKernelGroupAssembly.clearing E ∧ G.angles=C.angles := by
  obtain ⟨A,hAn,hA0,_hAt,hAe⟩ := exists_all_packet_series C
  exact CRGLinearKernelGroupAssembly.exists_groups_of_packets E
    (fullCoefficient D.coefficient) C.angles C.phase C.phase_normalized
    (fun i k hni he=>C.phase_injective_away_zero he hni) (amplitude C) A hA0 hAn
    (fun θ _hθ j=>Eventually.of_forall (fun x=>coefficient_representation C E j x)) hAe

def CoefficientData.exponentialGroups {n : ℕ} (D : CoefficientData n) :
    MonicGroups D.exponential := Classical.choice (exists_monic_groups D.exponential D.isExponential)

def CoefficientData.geometryCells {n : ℕ} (D : CoefficientData n) : AngularIndex D → CRGPuiseuxLinearKernelCells.Cell D :=
  Classical.choose (exists_finite_cells D)

def CoefficientData.sourceGroups {n : ℕ} (D : CoefficientData n) (C : AngularIndex D) :
    Groups (fullCoefficient D.coefficient) :=
  Classical.choose (cell_exists_exponential_groups D (D.geometryCells C) D.exponentialGroups)

theorem CoefficientData.sourceGroups_angles {n : ℕ} (D : CoefficientData n) (C : AngularIndex D) :
    (D.sourceGroups C).angles=(D.geometryCells C).angles :=
  (Classical.choose_spec (cell_exists_exponential_groups D (D.geometryCells C) D.exponentialGroups)).2.2

theorem CoefficientData.sourceGroups_cover {n : ℕ} (D : CoefficientData n) :
    ∀ᵐθ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),∃C : AngularIndex D,
      θ∈(D.sourceGroups C).angles := by
  have hc := (Classical.choose_spec (exists_finite_cells D)).2
  have hr : ∀ᵐθ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),θ∈Ioc 0 (2*Real.pi) :=
    ae_restrict_mem measurableSet_Ioc
  filter_upwards [ae_restrict_of_ae hc,hr] with θ hθ hw
  obtain ⟨C,hC⟩ := hθ (Ioc_subset_Icc_self hw)
  refine ⟨C,?_⟩
  rw [D.sourceGroups_angles C]
  simpa only [CoefficientData.geometryCells] using hC

/-- Full manuscript Corollary 5.2, from exponential-polynomial terms and
the actual finite integrals with nonzero slopes and holomorphic weights.
The finite Puiseux family depends only on these coefficient data. -/
theorem corollary_5_2 {n : ℕ} (D : CoefficientData n) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬∃P : Polynomial ℂ,∀z : ℂ,f z=P.eval z)
    (heq : SolvesMonicEquation n D.coefficient f) :
    ∃σ : ℚ,0<σ ∧ CRGOrder.IsOrder f (σ:ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ:ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ:ℝ) ∧
      PhaseComparison (sectors D.sourceGroups) f :=
  of_exponential_expansion_groups D.sourceGroups
    (fullCoefficient_differentiable D.coefficient D.differentiable_coefficient)
    D.sourceGroups_cover f hf hfinite htrans (full_equation D.coefficient f heq)

#print axioms cell_exists_exponential_groups
#print axioms CoefficientData.sourceGroups_cover
#print axioms corollary_5_2
end CRGLinearKernel
