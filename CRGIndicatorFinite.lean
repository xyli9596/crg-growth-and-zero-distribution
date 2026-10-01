import CRGIndicatorPartition

/-! A finite sampling proof that a fixed finite list of harmonic indicator
alternatives produces only finitely many continuous indicators on the circle. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace CRGIndicatorFinite
open CRGPhaseDirections CRGIndicatorPartition

/-- Every point between the extreme cuts, outside the cuts themselves, lies
between two adjacent members of the finite cut set. -/
theorem exists_adjacent {s : Finset ℝ} {a b θ : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hθ : θ ∈ Icc a b) (hn : θ ∉ s) :
    ∃ u ∈ s, ∃ v ∈ s, a ≤ u ∧ u < θ ∧ θ < v ∧ v ≤ b ∧
      ∀ w ∈ s, w ∉ Ioo u v := by
  classical
  have haθ : a < θ := lt_of_le_of_ne hθ.1 (fun he => hn (he ▸ ha))
  have hθb : θ < b := lt_of_le_of_ne hθ.2 (fun he => hn (he.symm ▸ hb))
  let L := s.filter (fun x => x < θ)
  let U := s.filter (fun x => θ < x)
  have hL : L.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, haθ⟩⟩
  have hU : U.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hθb⟩⟩
  let u := L.max' hL
  let v := U.min' hU
  have hu := Finset.mem_filter.mp (L.max'_mem hL)
  have hv := Finset.mem_filter.mp (U.min'_mem hU)
  refine ⟨u, hu.1, v, hv.1,
    L.le_max' a (Finset.mem_filter.mpr ⟨ha, haθ⟩), hu.2, hv.2,
    U.min'_le b (Finset.mem_filter.mpr ⟨hb, hθb⟩), ?_⟩
  intro w hw hmid
  rcases lt_trichotomy w θ with hwθ | he | hθw
  · have hh := L.le_max' w (Finset.mem_filter.mpr ⟨hw, hwθ⟩)
    exact not_lt_of_ge hh hmid.1
  · exact hn (he ▸ hw)
  · have hh := U.min'_le w (Finset.mem_filter.mpr ⟨hw, hθw⟩)
    exact not_lt_of_ge hh hmid.2

/-- Real argument representatives in the closed fundamental interval cover
all unit-circle directions. -/
theorem angleDirection_arg (ζ : LevinGrowth.Direction) :
    CRGOrderLevin.angleDirection ζ.val.arg = ζ := by
  apply Subtype.ext
  have hh := Complex.norm_mul_exp_arg_mul_I ζ.val
  simpa only [CRGOrderLevin.angleDirection, ζ.property, Complex.ofReal_one, one_mul] using hh

/-- All continuous indicators selecting from the given finite coefficient
list form a finite set. Collisions and samples are constructed, not assumed. -/
theorem finite_continuous_indicators (C : Finset ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    {h : LevinGrowth.Direction → ℝ | Continuous h ∧
      ∀ θ : ℝ, ∃ c ∈ C,
        h (CRGOrderLevin.angleDirection θ) = leadingReal c ρ θ}.Finite := by
  classical
  let R := collisionDirections C ρ (-Real.pi) Real.pi
  have hR : R.Finite := collisionDirections_finite C hρ
  let s := insert (-Real.pi) (insert Real.pi hR.toFinset)
  have ha : -Real.pi ∈ s := Finset.mem_insert_self _ _
  have hb : Real.pi ∈ s := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hRs : R ⊆ (s : Set ℝ) := by
    intro θ hθ
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hR.mem_toFinset.mpr hθ))
  let Samples := s ⊕ (s × s)
  let point : Samples → ℝ
    | .inl x => x.val
    | .inr x => (x.1.val + x.2.val) / 2
  let H := {h : LevinGrowth.Direction → ℝ | Continuous h ∧
    ∀ θ : ℝ, ∃ c ∈ C,
      h (CRGOrderLevin.angleDirection θ) = leadingReal c ρ θ}
  have hex (h : H) (x : Samples) :
      ∃ c : C, h.val (CRGOrderLevin.angleDirection (point x)) = leadingReal c.val ρ (point x) := by
    obtain ⟨c, hc, he⟩ := h.property.2 (point x)
    exact ⟨⟨c, hc⟩, he⟩
  choose sig hsig using hex
  have hinj : Function.Injective sig := by
    intro h₁ h₂ heq
    apply Subtype.ext
    funext ζ
    let θ := ζ.val.arg
    have hθ : θ ∈ Icc (-Real.pi) Real.pi :=
      ⟨(Complex.neg_pi_lt_arg ζ.val).le, Complex.arg_le_pi ζ.val⟩
    have hsamp (x : Samples) :
        h₁.val (CRGOrderLevin.angleDirection (point x)) =
          h₂.val (CRGOrderLevin.angleDirection (point x)) := by
      rw [hsig h₁ x, hsig h₂ x, congrFun heq x]
    have hangle : h₁.val (CRGOrderLevin.angleDirection θ) =
        h₂.val (CRGOrderLevin.angleDirection θ) := by
      by_cases hcut : θ ∈ s
      · exact hsamp (.inl ⟨θ, hcut⟩)
      obtain ⟨u, hu, v, hv, hau, huθ, hθv, hvb, hgap⟩ := exists_adjacent ha hb hθ hcut
      have huv : u < v := huθ.trans hθv
      have hsub : Ioo u v ⊆ Icc (-Real.pi) Real.pi :=
        fun x hx => ⟨hau.trans hx.1.le, hx.2.le.trans hvb⟩
      have havoid : Disjoint (Ioo u v) R := by
        apply Set.disjoint_left.mpr
        intro x hx hxR
        exact hgap x (hRs hxR) hx
      obtain ⟨c₁, hc₁, h₁cell⟩ := indicator_on_interval C hρ huv hsub havoid
        (fun x => h₁.val (CRGOrderLevin.angleDirection x))
        (h₁.property.1.comp CRGOrderLevin.continuous_angleDirection) h₁.property.2
      obtain ⟨c₂, hc₂, h₂cell⟩ := indicator_on_interval C hρ huv hsub havoid
        (fun x => h₂.val (CRGOrderLevin.angleDirection x))
        (h₂.property.1.comp CRGOrderLevin.continuous_angleDirection) h₂.property.2
      have hmid : (u+v)/2 ∈ Ioo u v := ⟨by linarith, by linarith⟩
      have hsame : leadingReal c₁ ρ ((u+v)/2) = leadingReal c₂ ρ ((u+v)/2) := by
        rw [← h₁cell _ hmid, ← h₂cell _ hmid]
        exact hsamp (.inr (⟨u, hu⟩, ⟨v, hv⟩))
      have hc : c₁ = c₂ := by
        by_contra hne
        exact Set.disjoint_left.mp havoid hmid
          ⟨hsub hmid, c₁, hc₁, c₂, hc₂, hne, hsame⟩
      rw [h₁cell θ ⟨huθ, hθv⟩, h₂cell θ ⟨huθ, hθv⟩, hc]
    simpa only [θ, angleDirection_arg] using hangle
  haveI : Finite H := Finite.of_injective sig hinj
  exact Set.toFinite H

#print axioms exists_adjacent
#print axioms angleDirection_arg
#print axioms finite_continuous_indicators
end CRGIndicatorFinite
