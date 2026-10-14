import CRGFinitePhaseEndgame

/-! The CRG finite-phase method gives exact order one when every phase has
degree at most one. Transcendence supplies a positive leading ray internally. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Polynomial
open scoped Topology
namespace CRGLinearPhaseEndgame
open CRGNormalFormGoal CRGOrderRay

theorem order_one_of_linear_phases {ι : Type*} [Fintype ι] {f : ℂ→ℂ}
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬∃Q:Polynomial ℂ, ∀z:ℂ, f z=Q.eval z)
    (G : ι→Polynomial ℂ) (hG : ∀i,(G i).coeff 0=0)
    (hdeg : ∀i,(G i).natDegree≤1)
    (hphase : ∀ᵐθ:ℝ, ∃i:ι,
      (∀ᶠr:ℝ in atTop,f (ray θ r)≠0) ∧ ∃C:ℝ,∀ᶠr:ℝ in atTop,
      |Real.log ‖f (ray θ r)‖-(phaseOnRay 1 (G i) θ 0 r).re|≤C*Real.log r) :
    CRGOrder.IsOrder f 1 ∧ LevinGrowth.FinitePositiveType f 1 ∧
      LevinGrowth.ManuscriptCRG f 1 := by
  classical
  let degree : ι→ℚ := fun i => (G i).natDegree
  let leading : ι→ℝ→ℝ := fun i => CRGFinitePhaseEndgame.leading 1 (G i)
  have hdata : ∀ᵐθ:ℝ, ∃i:ι, RayData f θ (degree i : ℝ) (leading i θ) := by
    simpa only [degree,leading,Nat.cast_one,div_one] using
      CRGFinitePhaseEndgame.ae_rayData_of_phase_comparison (fun _ : ι => 1)
        (fun _ => zero_lt_one) G hG hphase
  obtain ⟨chosen,hchosen⟩ := CRGOrderAE.select_ae_rayData degree leading hdata
  let D : Set ℝ := {θ | RayData f θ (degree (chosen θ):ℝ) (leading (chosen θ) θ)}
  have hD : Dense D := volume.dense_of_ae hchosen
  have hdat : ∀θ∈D, RayData f θ (degree (chosen θ):ℝ) (leading (chosen θ) θ) :=
    fun _ h => h
  obtain ⟨θ,hθ,hd,ha⟩ := CRGOrderPhaseCriterion.exists_positive_leading hf hfinite htrans
    degree chosen (fun θ => leading (chosen θ) θ) hD hdat
  have hd1 : (degree (chosen θ):ℝ)=1 := by
    have hd' : 0<((G (chosen θ)).natDegree:ℝ) := by simpa [degree] using hd
    have hn : 0<(G (chosen θ)).natDegree := by exact_mod_cast hd'
    have he : (G (chosen θ)).natDegree=1 := by have := hdeg (chosen θ); omega
    simp [degree,he]
  have hlo := positive_leading_lower (hdat θ hθ) hd ha
  rw [hd1] at hlo
  have hupper := CRGPhragmenRay.dense_eventual_finiteType hf hfinite
    (τ:=1) zero_le_one hD (by
      intro φ hφ
      have hp := hdat φ hφ
      have hle : (degree (chosen φ):ℝ)≤1 := by
        simp only [degree,Rat.cast_natCast]
        exact_mod_cast hdeg (chosen φ)
      by_cases hz : (degree (chosen φ):ℝ)=0
      · exact zero_degree_upper hp hz zero_lt_one
      · have hpos : 0<(degree (chosen φ):ℝ) := lt_of_le_of_ne hp.degree_nonneg (Ne.symm hz)
        rcases lt_or_gt_of_ne (hp.positive hpos).1 with hn | ha
        · obtain ⟨R,hR⟩ := eventually_atTop.mp (negative_leading_bounded hp hpos hn)
          exact ⟨0,R,fun r hr => by simpa using hR r hr⟩
        · exact positive_leading_upper hp hpos ha hle)
  have htype : LevinGrowth.FinitePositiveType f 1 := ⟨hupper,hlo⟩
  have horder := CRGOrder.finitePositiveType_isOrder zero_le_one htype
  obtain ⟨σ,hσ,ho,_,hcrg⟩ := CRGFinitePhaseEndgame.complete_of_finite_phases
    hf hfinite htrans (fun _ : ι => 1) (fun _ => zero_lt_one) G hG hphase
  have hs : (σ:ℝ)=1 := le_antisymm (ho.2.2 1 zero_le_one horder.2.1)
    (horder.2.2 σ ho.1 ho.2.1)
  exact ⟨horder,htype,by simpa only [hs] using hcrg⟩

#print axioms order_one_of_linear_phases
end CRGLinearPhaseEndgame
