import CRGIndicatorAlternatives
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Connected.TotallyDisconnected

/-! Finite collision directions and rigidity of continuous finite indicator
alternatives on intervals. These are the actual topological steps in the
first assertion of Corollary 3.6. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace CRGIndicatorPartition
open CRGPhaseDirections

/-- A nonzero leading monomial has only finitely many zeros on a bounded
argument interval. This strengthens the earlier countability statement. -/
theorem leadingReal_zero_finite {c : ℂ} {ρ a b : ℝ} (hc : c ≠ 0) (hρ : 0 < ρ) :
    {θ : ℝ | θ ∈ Icc a b ∧ leadingReal c ρ θ = 0}.Finite := by
  let L : ℝ := (c.arg + ρ * a) / Real.pi - 1 / 2
  let U : ℝ := (c.arg + ρ * b) / Real.pi - 1 / 2
  apply ((Set.finite_Icc (⌈L⌉ : ℤ) (⌊U⌋ : ℤ)).image
    (fun k : ℤ => (((2 * (k : ℝ) + 1) * Real.pi / 2) - c.arg) / ρ)).subset
  intro θ hθ
  have hz : Real.cos (c.arg + ρ * θ) = 0 := by
    have hh := hθ.2
    rw [leadingReal_eq_cos] at hh
    exact (mul_eq_zero.mp hh).resolve_left (norm_ne_zero_iff.mpr hc)
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hz
  have heq : (k : ℝ) = (c.arg + ρ * θ) / Real.pi - 1 / 2 := by
    apply (eq_sub_iff_add_eq).2
    apply (eq_div_iff Real.pi_ne_zero).2
    nlinarith [hk]
  refine ⟨k, ⟨?_, ?_⟩, ?_⟩
  · apply Int.ceil_le.mpr
    rw [heq]
    dsimp [L]
    exact sub_le_sub_right (div_le_div_of_nonneg_right
      (by nlinarith [hθ.1.1]) Real.pi_pos.le) _
  · apply Int.le_floor.mpr
    rw [heq]
    dsimp [U]
    exact sub_le_sub_right (div_le_div_of_nonneg_right
      (by nlinarith [hθ.1.2]) Real.pi_pos.le) _
  · apply (div_eq_iff hρ.ne').2
    nlinarith [hk]

theorem leadingReal_sub (c d : ℂ) (ρ θ : ℝ) :
    leadingReal c ρ θ - leadingReal d ρ θ = leadingReal (c-d) ρ θ := by
  simp only [leadingReal, sub_mul, Complex.sub_re]

/-- Equality directions for two distinct coefficient alternatives are finite. -/
theorem equality_directions_finite {c d : ℂ} {ρ a b : ℝ}
    (hcd : c ≠ d) (hρ : 0 < ρ) :
    {θ : ℝ | θ ∈ Icc a b ∧ leadingReal c ρ θ = leadingReal d ρ θ}.Finite := by
  simpa only [← leadingReal_sub, sub_eq_zero] using
    (leadingReal_zero_finite (sub_ne_zero.mpr hcd) hρ (a := a) (b := b))

/-- Continuity cannot switch between finitely many pairwise separated
continuous alternatives on a preconnected set. -/
theorem one_alternative_on_preconnected {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    {S : Set X} (hS : IsPreconnected S) (hne : S.Nonempty)
    (h : X → ℝ) (φ : ι → X → ℝ) (hh : ContinuousOn h S)
    (hφ : ∀ i, ContinuousOn (φ i) S)
    (halt : ∀ x ∈ S, ∃ i, h x = φ i x)
    (hsep : ∀ x ∈ S, Function.Injective (fun i => φ i x)) :
    ∃ i : ι, ∀ x ∈ S, h x = φ i x := by
  classical
  let A : ι → Set S := fun i => {x | h x.val = φ i x.val}
  have hclosed (i : ι) : IsClosed (A i) :=
    isClosed_eq hh.domRestrict (hφ i).domRestrict
  have hclopen (i : ι) : IsClopen (A i) := by
    refine ⟨hclosed i, ?_⟩
    have heq : (A i)ᶜ = ⋃ j : {j : ι // j ≠ i}, A j.val := by
      ext x
      simp only [mem_compl_iff, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨j, hj⟩ := halt x.val x.property
        have hji : j ≠ i := by
          intro he
          exact hx (he ▸ hj)
        exact ⟨⟨j, hji⟩, hj⟩
      · rintro ⟨j, hj⟩ hi
        exact j.property (hsep x.val x.property (hj.symm.trans hi))
    exact isClosed_compl_iff.mp (heq ▸
      isClosed_iUnion_of_finite (fun j : {j : ι // j ≠ i} => hclosed j.val))
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, hi⟩ := halt x hx
  haveI : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  have hall := isPreconnected_univ.subset_isClopen (hclopen i)
    (show (univ ∩ A i).Nonempty from ⟨⟨x, hx⟩, mem_univ _, hi⟩)
  exact ⟨i, fun y hy => hall (mem_univ (⟨y, hy⟩ : S))⟩

/-- The cut directions are a finite union of the actual equality points,
and therefore depend only on the coefficient alternatives. -/
def collisionDirections (C : Finset ℂ) (ρ a b : ℝ) : Set ℝ :=
  {θ | θ ∈ Icc a b ∧ ∃ c ∈ C, ∃ d ∈ C,
    c ≠ d ∧ leadingReal c ρ θ = leadingReal d ρ θ}

theorem collisionDirections_finite (C : Finset ℂ) {ρ a b : ℝ} (hρ : 0 < ρ) :
    (collisionDirections C ρ a b).Finite := by
  have hh : collisionDirections C ρ a b =
      ⋃ c : C, ⋃ d : {d : C // c.val ≠ d.val},
        {θ : ℝ | θ ∈ Icc a b ∧ leadingReal c.val ρ θ = leadingReal d.val.val ρ θ} := by
    ext θ
    simp only [collisionDirections, mem_setOf_eq, mem_iUnion, exists_prop, Subtype.exists, Finset.mem_coe]
    aesop
  rw [hh]
  exact Set.finite_iUnion (fun c => Set.finite_iUnion
    (fun d => equality_directions_finite d.property hρ))

/-- On every open interval avoiding the fixed finite collision set, a
continuous indicator equals one fixed leading monomial throughout. -/
theorem indicator_on_interval (C : Finset ℂ) {ρ a b u v : ℝ} (hρ : 0 < ρ)
    (huv : u < v) (hsubset : Ioo u v ⊆ Icc a b)
    (havoid : Disjoint (Ioo u v) (collisionDirections C ρ a b))
    (h : ℝ → ℝ) (hh : Continuous h)
    (halt : ∀ θ : ℝ, ∃ c ∈ C, h θ = leadingReal c ρ θ) :
    ∃ c ∈ C, ∀ θ ∈ Ioo u v, h θ = leadingReal c ρ θ := by
  obtain ⟨c, hc⟩ := one_alternative_on_preconnected
    isPreconnected_Ioo (nonempty_Ioo.mpr huv) h
    (fun c : C => leadingReal c.val ρ) hh.continuousOn
    (fun c => (CRGIndicatorAlternatives.continuous_leadingReal c.val ρ).continuousOn)
    (fun θ _ => by obtain ⟨c, hc, hh⟩ := halt θ; exact ⟨⟨c, hc⟩, hh⟩) (by
      intro θ hθ c d heq
      apply Subtype.ext
      by_contra hne
      exact (Set.disjoint_left.mp havoid hθ
        ⟨hsubset hθ, c.val, c.property, d.val, d.property, hne, heq⟩))
  exact ⟨c.val, c.property, hc⟩

#print axioms leadingReal_zero_finite
#print axioms equality_directions_finite
#print axioms one_alternative_on_preconnected
#print axioms collisionDirections_finite
#print axioms indicator_on_interval
end CRGIndicatorPartition
