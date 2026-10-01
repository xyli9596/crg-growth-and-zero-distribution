import CRGExponentialExpansionSector
import CRGPuiseuxProposition

/-! Assembly of the coefficient constructions for Corollaries 5.2 and 5.3.
The source constructors must provide actual finite grouped expansions;
dominance, Puiseux normal forms, actual residual estimates and the analytic
growth conclusion are then constructed by the theorems below. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial MeasureTheory
open scoped Topology
namespace CRGExponentialExpansionConclusion
open CRGExponentialExpansionSector CRGPuiseuxProposition
variable {n : ℕ} {ι : Type*} [Fintype ι]
variable {a : Fin (n+1) → ℂ → ℂ}

abbrev SectorIndex (D : ι → Groups a) := (i : ι) × Fin (D i).count

def sectors (D : ι → Groups a) (i : SectorIndex D) : CRGPuiseuxSector.Sector a :=
  (D i.1).sector i.2

theorem ae_sector_cover (D : ι → Groups a)
    (hcover : ∀ᵐθ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),∃i : ι,θ∈(D i).angles) :
    ∀ᵐθ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),
      ∃i : SectorIndex D,θ∈(sectors D i).angles := by
  have hdom : ∀ᵐθ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),
      ∀i : ι,θ∈(D i).angles→∃ν : Fin (D i).count,θ∈((D i).sector ν).angles :=
    ae_restrict_of_ae (ae_all_iff.mpr (fun i=>(D i).ae_sector_cover))
  filter_upwards [hcover,hdom] with θ hθ hd
  obtain ⟨i,hi⟩ := hθ
  obtain ⟨ν,hν⟩ := hd i hi
  exact ⟨⟨i,ν⟩,hν⟩

theorem of_exponential_expansion_groups (D : ι → Groups a)
    (ha : ∀j,Differentiable ℂ (a j))
    (hcover : ∀ᵐθ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),∃i : ι,θ∈(D i).angles)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬∃P : Polynomial ℂ,∀z : ℂ,f z=P.eval z)
    (heq : ∀z : ℂ,∑j : Fin (n+1),a j z*iteratedDeriv j.val f z=0) :
    ∃σ : ℚ,0<σ ∧ CRGOrder.IsOrder f (σ:ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ:ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ:ℝ) ∧
      PhaseComparison (sectors D) f :=
  proposition_5_1 (sectors D) ha (ae_sector_cover D hcover) f hf hfinite htrans heq

#print axioms ae_sector_cover
#print axioms of_exponential_expansion_groups
end CRGExponentialExpansionConclusion
