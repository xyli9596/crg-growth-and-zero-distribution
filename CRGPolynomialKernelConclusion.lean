import CRGPolynomialKernelGroupPackets
import CRGPuiseuxPolynomialKernelCells

/-! Corollary 5.3 for the actual polynomial-kernel source class. Every
sector, formal series and finite phase family below is constructed from the
coefficient data, before a solution is chosen. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial MeasureTheory
open scoped Topology BigOperators
namespace CRGPolynomialKernel
open CRGExponentialCoefficients CRGExponentialCoefficientGroups CRGPuiseuxMonic
open CRGPuiseuxPolynomialKernelCells CRGExponentialExpansionSector
open CRGExponentialExpansionConclusion CRGPuiseuxProposition

def CoefficientData.exponentialGroups {n : ℕ} (D : CoefficientData n) :
    MonicGroups D.exponential := Classical.choice (exists_monic_groups D.exponential D.isExponential)

def CoefficientData.geometryCells {n : ℕ} (D : CoefficientData n) : AngularIndex D → Cell D :=
  Classical.choose (exists_finite_geometry_cells D)

def CoefficientData.sourceGroups {n : ℕ} (D : CoefficientData n) (C : AngularIndex D) :
    Groups (fullCoefficient D.coefficient) :=
  Classical.choose ((D.geometryCells C).exists_exponential_groups D.exponentialGroups)

theorem CoefficientData.sourceGroups_angles {n : ℕ} (D : CoefficientData n) (C : AngularIndex D) :
    (D.sourceGroups C).angles=(D.geometryCells C).angles :=
  (Classical.choose_spec ((D.geometryCells C).exists_exponential_groups D.exponentialGroups)).2.2

theorem CoefficientData.sourceGroups_cover {n : ℕ} (D : CoefficientData n) :
    ∀ᵐθ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),∃C : AngularIndex D,
      θ∈(D.sourceGroups C).angles := by
  have hc := (Classical.choose_spec (exists_finite_geometry_cells D)).2.2
  have hr : ∀ᵐθ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),θ∈Ioc 0 (2*Real.pi) :=
    ae_restrict_mem measurableSet_Ioc
  filter_upwards [ae_restrict_of_ae hc,hr] with θ hθ hw
  obtain ⟨C,hC⟩ := hθ (Ioc_subset_Icc_self hw)
  refine ⟨C,?_⟩
  rw [D.sourceGroups_angles C]
  simpa only [CoefficientData.geometryCells] using hC

/-- Full Corollary 5.3: the source assumptions are precisely exponential
polynomial terms, positive integer kernel powers, nonconstant polynomial
phases and holomorphic neighbourhood weights. The endpoint estimates,
ramification, grouping, pruning and coefficient sectors are all proved. -/
theorem corollary_5_3 {n : ℕ} (D : CoefficientData n) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬∃P : Polynomial ℂ,∀z : ℂ,f z=P.eval z)
    (heq : SolvesMonicEquation n D.coefficient f) :
    ∃σ : ℚ,0<σ ∧ CRGOrder.IsOrder f (σ:ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ:ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ:ℝ) ∧
      PhaseComparison (sectors D.sourceGroups) f :=
  of_exponential_expansion_groups D.sourceGroups
    (fullCoefficient_differentiable D.coefficient D.differentiable_coefficient)
    D.sourceGroups_cover f hf hfinite htrans (full_equation D.coefficient f heq)

#print axioms CoefficientData.sourceGroups_cover
#print axioms corollary_5_3
end CRGPolynomialKernel
