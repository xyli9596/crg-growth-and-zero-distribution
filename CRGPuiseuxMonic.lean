import CRGExponentialExpansionConclusion

/-! The monic scalar equation used in the manuscript is represented by
retaining its top coefficient 1 among all coefficient expansions. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial MeasureTheory
open scoped Topology BigOperators
namespace CRGPuiseuxMonic
open CRGExponentialCoefficients CRGPuiseuxSector CRGPuiseuxProposition
variable {n : ℕ}

def fullCoefficient (a : Fin n → ℂ → ℂ) : Fin (n+1) → ℂ → ℂ :=
  Fin.lastCases (fun _=>1) a

@[simp] theorem fullCoefficient_last (a : Fin n → ℂ → ℂ) (z : ℂ) :
    fullCoefficient a (Fin.last n) z=1 := by simp [fullCoefficient]

@[simp] theorem fullCoefficient_castSucc (a : Fin n → ℂ → ℂ) (j : Fin n) (z : ℂ) :
    fullCoefficient a j.castSucc z=a j z := by simp [fullCoefficient]

theorem fullCoefficient_differentiable (a : Fin n → ℂ → ℂ)
    (ha : ∀j,Differentiable ℂ (a j)) : ∀j,Differentiable ℂ (fullCoefficient a j) := by
  intro j
  induction j using Fin.lastCases with
  | last => simpa only [fullCoefficient,Fin.lastCases_last] using differentiable_const (c:=(1:ℂ))
  | cast j => simpa only [fullCoefficient,Fin.lastCases_castSucc] using ha j

theorem full_equation (a : Fin n → ℂ → ℂ) (f : ℂ → ℂ)
    (heq : SolvesMonicEquation n a f) :
    ∀z : ℂ,∑j : Fin (n+1),fullCoefficient a j z*iteratedDeriv j.val f z=0 := by
  intro z
  rw [Fin.sum_univ_castSucc]
  simpa only [fullCoefficient_last,fullCoefficient_castSucc,Fin.val_last,
    Fin.val_castSucc,one_mul,add_comm] using heq z

theorem proposition_5_1_monic {ι : Type*} [Fintype ι] (a : Fin n → ℂ → ℂ)
    (S : ι → Sector (fullCoefficient a)) (ha : ∀j,Differentiable ℂ (a j))
    (hcover : ∀ᵐθ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),∃i : ι,θ∈(S i).angles)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬∃P : Polynomial ℂ,∀z : ℂ,f z=P.eval z)
    (heq : SolvesMonicEquation n a f) :
    ∃σ : ℚ,0<σ ∧ CRGOrder.IsOrder f (σ:ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ:ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ:ℝ) ∧
      PhaseComparison S f :=
  proposition_5_1 S (fullCoefficient_differentiable a ha) hcover f hf hfinite htrans
    (full_equation a f heq)

#print axioms fullCoefficient_differentiable
#print axioms full_equation
#print axioms proposition_5_1_monic
end CRGPuiseuxMonic
