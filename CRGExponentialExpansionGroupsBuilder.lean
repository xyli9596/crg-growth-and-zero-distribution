import CRGExponentialExpansionSector
import Mathlib.Data.Fintype.EquivFin

/-! Exact deletion of zero amplitude groups and indexing the retained
normalized phase polynomials by one finite type. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial Asymptotics
open scoped Topology BigOperators
namespace CRGExponentialExpansionGroupsBuilder
open CRGNormalFormGoal CRGPuiseuxCoordinates CRGExponentialExpansionSector
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientRayTail
open WasowGlobalRayData WasowLaurentRayEquation
variable {n : ℕ}

theorem exists_groups
    (a : Fin (n+1) → ℂ → ℂ) (p : ℕ) (hp : 0<p) (h : ℕ) (angles : Set ℝ)
    (S T : Finset (Polynomial ℂ)) (hTS : T⊆S) (hT : T.Nonempty)
    (hphase : ∀q∈S,q.coeff 0=0)
    (amp : Polynomial ℂ → Fin (n+1) → ℂ → ℂ)
    (B : Polynomial ℂ → Fin (n+1) → PowerSeries ℂ)
    (hrep : ∀θ∈angles,∀j : Fin (n+1),∀ᶠx in rayFilter (direction (θ/p)),
      a j (originalPoint p x)=∑q∈S,amp q j x*Complex.exp (q.eval (originalPoint p x)))
    (hzero : ∀q∈S,q∉T → ∀j : Fin (n+1),∀x : ℂ,amp q j x=0)
    (hexp : ∀θ∈angles,∀q∈T,∀j : Fin (n+1),CompleteExpansion
      (rayFilter (direction (θ/p))) (fun x=>x^h*amp q j x) (B q j))
    (hhead : ∀q∈T,∃j : Fin (n+1),B q j≠0) :
    ∃D : Groups a,D.denominator=p ∧ D.clearing=h ∧ D.angles=angles := by
  classical
  let e := T.equivFin
  let phase : Fin T.card → Polynomial ℂ := fun i=>(e.symm i).val
  have hmem (i : Fin T.card) : phase i∈T := (e.symm i).property
  have hsum (j : Fin (n+1)) (x : ℂ) :
      (∑q∈S,amp q j x*Complex.exp (q.eval (originalPoint p x)))=
        ∑i : Fin T.card,amp (phase i) j x*Complex.exp ((phase i).eval (originalPoint p x)) := by
    have hST : (∑q∈S,amp q j x*Complex.exp (q.eval (originalPoint p x)))=
        ∑q∈T,amp q j x*Complex.exp (q.eval (originalPoint p x)) := by
      symm
      apply Finset.sum_subset hTS
      intro q hq hqt
      rw [hzero q hq hqt j x,zero_mul]
    rw [hST,←Finset.sum_coe_sort T]
    exact Equiv.sum_comp e.symm (fun q : T=>amp q.val j x*Complex.exp (q.val.eval (originalPoint p x))) |>.symm
  refine ⟨{
    denominator := p
    positive := hp
    clearing := h
    angles := angles
    count := T.card
    count_positive := Finset.card_pos.mpr hT
    phase := phase
    phase_normalized := fun i=>hphase (phase i) (hTS (hmem i))
    phase_injective := ?_
    amplitude := fun i=>amp (phase i)
    series := fun i=>B (phase i)
    some_nonzero := fun i=>hhead (phase i) (hmem i)
    representation := ?_
    expansion := fun θ hθ i j=>hexp θ hθ (phase i) (hmem i) j},rfl,rfl,rfl⟩
  · intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  · intro θ hθ j
    filter_upwards [hrep θ hθ j] with x hx
    exact hx.trans (hsum j x)

#print axioms exists_groups
end CRGExponentialExpansionGroupsBuilder
