import CRGOrderPhaseCriterion
import CRGOrderLevin
import GundersenTheorem
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Almost-everywhere finite ray data imply the complete analytic conclusion.
Gundersen is reapplied at the proved rational order, so neither the final
order nor a two-sided logarithmic estimate is an input hypothesis. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace CRGOrderAE
open CRGOrderRay

/-- Selection from the finite alternatives is made only after an a.e.
existence statement; the arbitrary choices on bad angles are never used. -/
theorem select_ae_rayData {ι : Type*} {f : ℂ → ℂ}
    (degree : ι → ℚ) (leading : ι → ℝ → ℝ)
    (h : ∀ᵐ θ : ℝ, ∃ i : ι, RayData f θ (degree i : ℝ) (leading i θ)) :
    ∃ chosen : ℝ → ι, ∀ᵐ θ : ℝ,
      RayData f θ (degree (chosen θ) : ℝ) (leading (chosen θ) θ) := by
  classical
  obtain ⟨_, i₀, _⟩ := h.exists
  have hs : ∀ θ : ℝ, ∃ i : ι,
      (∃ j : ι, RayData f θ (degree j : ℝ) (leading j θ)) →
        RayData f θ (degree i : ℝ) (leading i θ) := by
    intro θ
    by_cases hh : ∃ j : ι, RayData f θ (degree j : ℝ) (leading j θ)
    · obtain ⟨i, hi⟩ := hh
      exact ⟨i, fun _ => hi⟩
    · exact ⟨i₀, fun hh' => (hh hh').elim⟩
  choose chosen hc using hs
  exact ⟨chosen, h.mono fun θ hθ => hc θ hθ⟩

/-- Complete endpoint for a finite family of rational ray degrees. The
negative leading directions are controlled by the newly proved actual order
through the sharp Gundersen theorem, and hence also have finite normalized
limits at that order. -/
theorem complete_of_ae_rayData {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬ ∃ P : Polynomial ℂ, ∀ z : ℂ, f z = P.eval z)
    (degree : ι → ℚ) (leading : ι → ℝ → ℝ)
    (h : ∀ᵐ θ : ℝ, ∃ i : ι, RayData f θ (degree i : ℝ) (leading i θ)) :
    ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ : ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ : ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ : ℝ) := by
  obtain ⟨chosen, hchosen⟩ := select_ae_rayData degree leading h
  let d : ℝ → ℝ := fun θ => (degree (chosen θ) : ℝ)
  let a : ℝ → ℝ := fun θ => leading (chosen θ) θ
  let D : Set ℝ := {θ | RayData f θ (d θ) (a θ)}
  have hD : Dense D := volume.dense_of_ae hchosen
  obtain ⟨σ, hσ, horder, htype⟩ :=
    CRGOrderPhaseCriterion.positive_rational_order hf hfinite htrans degree chosen a hD
      (fun θ hθ => hθ)
  have hσR : 0 < (σ : ℝ) := by exact_mod_cast hσ
  refine ⟨σ, hσ, horder, htype, ?_⟩
  have hg := GundersenTheorem.ae_ray_input hf
    (LevinGrowth.finitePositiveType_nontrivial htype) hσR.le horder.2.1
  have haebound : ∀ᵐ θ : ℝ,
      RayData f θ (d θ) (a θ) ∧
      (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ᶠ r : ℝ in atTop,
        |logValue f θ r| ≤ C * r ^ ((σ : ℝ) + δ)) := by
    filter_upwards [hchosen, hg] with θ hθ hgθ
    refine ⟨hθ, fun δ hδ => ?_⟩
    obtain ⟨C, _, hC⟩ := hgθ.2.2 δ hδ
    exact ⟨C, hC⟩
  apply CRGOrderLevin.manuscriptCRG_of_two_sided hf hσR htype d a
    (volume.dense_of_ae haebound)
  · intro θ hθ
    exact hθ.1
  · intro θ hθ
    exact hθ.2

#print axioms select_ae_rayData
#print axioms complete_of_ae_rayData
end CRGOrderAE
