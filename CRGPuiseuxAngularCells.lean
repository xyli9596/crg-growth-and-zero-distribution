import CRGIndicatorPartition
import CRGExponentialDominance
import Mathlib.Topology.Order.IntermediateValue

/-! Finite open angular cells from the actual leading-polynomial zero
directions. Their endpoints and signs depend only on the coefficient phases. -/
set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CRGPuiseuxAngularCells
open CRGPhaseDirections CRGIndicatorPartition

def Cell (cuts : Finset ℝ) :=
  {ab : cuts × cuts // ab.1.val<ab.2.val ∧
    Disjoint (Ioo ab.1.val ab.2.val) (cuts : Set ℝ)}

instance (cuts : Finset ℝ) : Fintype (Cell cuts) := by
  classical
  unfold Cell
  infer_instance

def Cell.left {cuts : Finset ℝ} (C : Cell cuts) : ℝ := C.val.1.val
def Cell.right {cuts : Finset ℝ} (C : Cell cuts) : ℝ := C.val.2.val
def Cell.angles {cuts : Finset ℝ} (C : Cell cuts) : Set ℝ := Ioo C.left C.right

theorem Cell.nonempty {cuts : Finset ℝ} (C : Cell cuts) : C.angles.Nonempty :=
  nonempty_Ioo.mpr C.property.1

theorem Cell.preconnected {cuts : Finset ℝ} (C : Cell cuts) : IsPreconnected C.angles :=
  isPreconnected_Ioo

theorem Cell.avoid {cuts : Finset ℝ} (C : Cell cuts) {θ : ℝ} (hθ : θ∈C.angles) : θ∉cuts :=
  fun hc => Set.disjoint_left.mp C.property.2 hθ hc

/-- Every point away from the finite cuts lies in an actual adjacent open
interval whose two endpoints are cuts. -/
theorem exists_cell (cuts : Finset ℝ) {a b θ : ℝ}
    (ha : a∈cuts) (hb : b∈cuts) (hθ : θ∈Icc a b) (hcut : θ∉cuts) :
    ∃C : Cell cuts,θ∈C.angles := by
  classical
  let L := cuts.filter (fun x=>x<θ)
  let U := cuts.filter (fun x=>θ<x)
  have hal : a<θ := lt_of_le_of_ne hθ.1 (by intro he;apply hcut;simpa only [←he] using ha)
  have hub : θ<b := lt_of_le_of_ne hθ.2 (by intro he;apply hcut;simpa only [he] using hb)
  have hL : L.Nonempty := ⟨a,by simp [L,ha,hal]⟩
  have hU : U.Nonempty := ⟨b,by simp [U,hb,hub]⟩
  let l := L.max' hL
  let u := U.min' hU
  have hlmem := Finset.mem_filter.mp (Finset.max'_mem L hL)
  have humem := Finset.mem_filter.mp (Finset.min'_mem U hU)
  have havoid : Disjoint (Ioo l u) (cuts : Set ℝ) := by
    apply Set.disjoint_left.mpr
    intro x hx hxc
    change x∈cuts at hxc
    have hxθ : x≠θ := by intro he;apply hcut;simpa only [he] using hxc
    rcases lt_or_gt_of_ne hxθ with hxt|htx
    · have hxl : x≤l := Finset.le_max' L x (by simp [L,hxc,hxt])
      exact (not_le.mpr hx.1) hxl
    · have hux : u≤x := Finset.min'_le U x (by simp [U,hxc,htx])
      exact (not_le.mpr hx.2) hux
  exact ⟨⟨(⟨l,hlmem.1⟩,⟨u,humem.1⟩),hlmem.2.trans humem.2,havoid⟩,hlmem.2,humem.2⟩

theorem ae_exists_cell (cuts : Finset ℝ) {a b : ℝ} (ha : a∈cuts) (hb : b∈cuts) :
    ∀ᵐθ : ℝ,θ∈Icc a b → ∃C : Cell cuts,θ∈C.angles := by
  have hnot : ∀ᵐθ : ℝ,θ∉(cuts : Set ℝ) := by
    apply ae_iff.mpr
    simpa only [not_not,Set.setOf_mem_eq] using cuts.finite_toSet.measure_zero volume
  filter_upwards [hnot] with θ hθ
  change θ∉cuts at hθ
  exact fun hw => exists_cell cuts ha hb hw hθ

theorem sign_constant_on_preconnected {S : Set ℝ} (hS : IsPreconnected S)
    (hne : S.Nonempty) (f : ℝ → ℝ) (hf : ContinuousOn f S)
    (hz : ∀θ∈S,f θ≠0) :
    (∀θ∈S,0<f θ) ∨ (∀θ∈S,f θ<0) := by
  obtain ⟨θ₀,hθ₀⟩ := hne
  rcases lt_or_gt_of_ne (hz θ₀ hθ₀) with hneg|hpos
  · right
    intro θ hθ
    by_contra hn
    have hp : 0<f θ := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (hz θ hθ))
    obtain ⟨x,hx,hzero⟩ := hS.intermediate_value hθ₀ hθ hf ⟨hneg.le,hp.le⟩
    exact hz x hx hzero
  · left
    intro θ hθ
    by_contra hn
    have hm : f θ<0 := lt_of_le_of_ne (le_of_not_gt hn) (hz θ hθ)
    obtain ⟨x,hx,hzero⟩ := hS.intermediate_value hθ hθ₀ hf ⟨hm.le,hpos.le⟩
    exact hz x hx hzero

def phaseCuts {ι : Type*} (Q : ι → Polynomial ℂ) : Set ℝ :=
  insert 0 (insert (2*Real.pi) (⋃i,{θ : ℝ | θ∈Icc 0 (2*Real.pi) ∧
    leadingReal (Q i).leadingCoeff (Q i).natDegree θ=0}))

theorem phaseCuts_finite {ι : Type*} [Fintype ι] (Q : ι → Polynomial ℂ)
    (hQ : ∀i,0<(Q i).natDegree) : (phaseCuts Q).Finite := by
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.finite_iUnion
  intro i
  have hne : Q i≠0 := by intro he;simpa only [he,Polynomial.natDegree_zero,lt_self_iff_false] using hQ i
  exact leadingReal_zero_finite (Polynomial.leadingCoeff_ne_zero.mpr hne)
    (by exact_mod_cast hQ i)

def phaseCutFinset {ι : Type*} [Fintype ι] (Q : ι → Polynomial ℂ)
    (hQ : ∀i,0<(Q i).natDegree) : Finset ℝ := (phaseCuts_finite Q hQ).toFinset

theorem mem_phaseCutFinset {ι : Type*} [Fintype ι] (Q : ι → Polynomial ℂ)
    (hQ : ∀i,0<(Q i).natDegree) (θ : ℝ) : θ∈phaseCutFinset Q hQ ↔ θ∈phaseCuts Q :=
  Set.Finite.mem_toFinset _

theorem phaseCuts_subset {ι : Type*} (Q : ι → Polynomial ℂ) :
    phaseCuts Q ⊆ Icc 0 (2*Real.pi) := by
  intro θ hθ
  rcases hθ with hθ|hθ
  · subst θ;exact ⟨le_rfl,by positivity⟩
  rcases hθ with hθ|hθ
  · subst θ;exact ⟨by positivity,le_rfl⟩
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hθ
    exact hi.1

theorem phaseCell_subset {ι : Type*} [Fintype ι] (Q : ι → Polynomial ℂ)
    (hQ : ∀i,0<(Q i).natDegree) (C : Cell (phaseCutFinset Q hQ)) :
    C.angles ⊆ Icc 0 (2*Real.pi) := by
  have hl := phaseCuts_subset Q ((mem_phaseCutFinset Q hQ _).mp C.val.1.property)
  have hr := phaseCuts_subset Q ((mem_phaseCutFinset Q hQ _).mp C.val.2.property)
  intro θ hθ
  exact ⟨hl.1.trans hθ.1.le,hθ.2.le.trans hr.2⟩

theorem leading_sign_on_cell {ι : Type*} [Fintype ι] (Q : ι → Polynomial ℂ)
    (hQ : ∀i,0<(Q i).natDegree) (C : Cell (phaseCutFinset Q hQ)) (i : ι) :
    (∀θ∈C.angles,0<leadingReal (Q i).leadingCoeff (Q i).natDegree θ) ∨
    (∀θ∈C.angles,leadingReal (Q i).leadingCoeff (Q i).natDegree θ<0) := by
  apply sign_constant_on_preconnected C.preconnected C.nonempty _
    (CRGIndicatorAlternatives.continuous_leadingReal _ _).continuousOn
  intro θ hθ hz
  apply C.avoid hθ
  apply (mem_phaseCutFinset Q hQ θ).mpr
  exact Or.inr (Or.inr (mem_iUnion.mpr ⟨i,phaseCell_subset Q hQ C hθ,hz⟩))

theorem ae_phase_cell {ι : Type*} [Fintype ι] (Q : ι → Polynomial ℂ)
    (hQ : ∀i,0<(Q i).natDegree) :
    ∀ᵐθ : ℝ,θ∈Icc 0 (2*Real.pi) → ∃C : Cell (phaseCutFinset Q hQ),θ∈C.angles := by
  apply ae_exists_cell
  · exact (mem_phaseCutFinset Q hQ 0).mpr (Or.inl rfl)
  · exact (mem_phaseCutFinset Q hQ _).mpr (Or.inr (Or.inl rfl))

#print axioms exists_cell
#print axioms ae_exists_cell
#print axioms sign_constant_on_preconnected
#print axioms phaseCuts_finite
#print axioms leading_sign_on_cell
#print axioms ae_phase_cell
end CRGPuiseuxAngularCells
