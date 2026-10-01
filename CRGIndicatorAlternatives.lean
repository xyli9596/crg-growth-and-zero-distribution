import CRGIndicatorFixedPhases
import Mathlib.Topology.Connected.Clopen

/-! Indicator alternatives obtained from actual finite phase comparisons.
No indicator formula is assumed. The unrestricted indicator is identified
from the full-radius limits and the finite alternatives extend from a.e.
directions by continuity. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Polynomial
open scoped Topology
namespace CRGIndicatorAlternatives
open CRGOrderRay CRGFinitePhaseEndgame CRGIndicatorFixedPhases

/-- Retain the member of the finite degree list that realizes positive type. -/
theorem finite_positive_type_witness {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z)
    (degree : ι → ℚ) (chosen : ℝ → ι) (a : ℝ → ℝ)
    {D : Set ℝ} (hD : Dense D)
    (hdata : ∀ θ ∈ D, RayData f θ (degree (chosen θ) : ℝ) (a θ)) :
    ∃ i : ι, 0 < degree i ∧ LevinGrowth.FinitePositiveType f (degree i : ℝ) := by
  classical
  let s : Finset ι := Finset.univ.filter fun i =>
    ∃ θ ∈ D, chosen θ = i ∧ 0 < (degree i : ℝ) ∧ 0 < a θ
  obtain ⟨θ₀, hθ₀, hd₀, ha₀⟩ :=
    CRGOrderPhaseCriterion.exists_positive_leading hf hfinite htrans degree chosen a hD hdata
  have hs : s.Nonempty := ⟨chosen θ₀, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, θ₀, hθ₀, rfl, hd₀, ha₀⟩⟩
  obtain ⟨i, hi, himax⟩ := s.exists_max_image (fun i => (degree i : ℝ)) hs
  obtain ⟨θ, hθ, hchosen, hd, ha⟩ := (Finset.mem_filter.mp hi).2
  have hdataθ := hdata θ hθ
  rw [hchosen] at hdataθ
  refine ⟨i, by exact_mod_cast hd, ?_, positive_leading_lower hdataθ hd ha⟩
  apply CRGPhragmenRay.dense_eventual_finiteType hf hfinite hd.le hD
  intro φ hφ
  have hφdata := hdata φ hφ
  by_cases hd0 : (degree (chosen φ) : ℝ) = 0
  · exact zero_degree_upper hφdata hd0 hd
  have hdpos : 0 < (degree (chosen φ) : ℝ) :=
    lt_of_le_of_ne hφdata.degree_nonneg (Ne.symm hd0)
  rcases lt_or_gt_of_ne (hφdata.positive hdpos).1 with haneg | hapos
  · obtain ⟨R, hR⟩ := eventually_atTop.1 (negative_leading_bounded hφdata hdpos haneg)
    exact ⟨0, R, fun r hr => by simpa using hR r hr⟩
  · apply positive_leading_upper hφdata hdpos hapos
    exact himax (chosen φ) (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, φ, hφ, rfl, hdpos, hapos⟩)

theorem isOrder_unique {f : ℂ → ℂ} {ρ σ : ℝ}
    (hρ : CRGOrder.IsOrder f ρ) (hσ : CRGOrder.IsOrder f σ) : ρ = σ :=
  le_antisymm (hρ.2.2 σ hσ.1 hσ.2.1) (hσ.2.2 ρ hρ.1 hρ.2.1)

/-- A.e. selection from a fixed finite list forces the actual order to be
one of its positive rational degrees. -/
theorem order_mem_of_ae_rayData {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z)
    (degree : ι → ℚ) (a : ι → ℝ → ℝ)
    (hdata : ∀ᵐ θ : ℝ, ∃ i : ι, RayData f θ (degree i : ℝ) (a i θ)) :
    ∃ i : ι, 0 < degree i ∧ CRGOrder.IsOrder f (degree i : ℝ) ∧
      LevinGrowth.FinitePositiveType f (degree i : ℝ) := by
  obtain ⟨chosen, hc⟩ := CRGOrderAE.select_ae_rayData degree a hdata
  obtain ⟨i, hi, htype⟩ := finite_positive_type_witness hf hfinite htrans degree chosen
    (fun θ => a (chosen θ) θ) (volume.dense_of_ae hc) (fun θ hθ => hθ)
  exact ⟨i, hi, CRGOrder.finitePositiveType_isOrder (by exact_mod_cast hi.le) htype, htype⟩

/-- The normalized limit equals the leading coefficient only at the actual
order; every strictly smaller selected phase contributes zero. -/
theorem normalized_limit_value {f : ℂ → ℂ} {θ d a ρ : ℝ}
    (h : RayData f θ d a) (hρ : 0 < ρ) (hdρ : d ≤ ρ) :
    Tendsto (fun r : ℝ => logValue f θ r / r ^ ρ) atTop
      (𝓝 (if d = ρ then a else 0)) := by
  by_cases hd0 : d = 0
  · rw [if_neg (by simpa [hd0] using hρ.ne)]
    exact zero_normalized_limit h hd0 hρ
  have hd : 0 < d := lt_of_le_of_ne h.degree_nonneg (Ne.symm hd0)
  by_cases heq : d = ρ
  · rw [if_pos heq, ← heq]
    exact (h.positive hd).2
  rw [if_neg heq]
  have hlt : d < ρ := lt_of_le_of_ne hdρ heq
  have ht := (h.positive hd).2.mul (tendsto_rpow_neg_atTop (sub_pos.mpr hlt))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [Real.rpow_neg hr.le, Real.rpow_sub hr, div_eq_mul_inv]
  field_simp

/-- Eventual nonvanishing and a genuine full-radius limit identify the
unrestricted extended-real limsup, with zeros still valued at minus infinity. -/
theorem indicator_eq_of_limit {f : ℂ → ℂ} {ρ θ L : ℝ}
    {h : LevinGrowth.Direction → ℝ} (hi : LevinGrowth.IsIndicator f ρ h)
    (hn : ∀ᶠ r : ℝ in atTop, f (CRGPhragmenRay.point θ r) ≠ 0)
    (hl : Tendsto (fun r : ℝ => logValue f θ r / r ^ ρ) atTop (𝓝 L)) :
    h (CRGOrderLevin.angleDirection θ) = L := by
  have heq : (fun r : ℝ => LevinGrowth.extendedNormalizedLog f ρ r
      (CRGOrderLevin.angleDirection θ)) =ᶠ[atTop]
        (fun r : ℝ => ((logValue f θ r / r ^ ρ : ℝ) : EReal)) := by
    filter_upwards [hn] with r hr
    have hr' : f (LevinGrowth.rayPoint r (CRGOrderLevin.angleDirection θ)) ≠ 0 := hr
    simp only [LevinGrowth.extendedNormalizedLog, if_neg hr']
    rfl
  have hlim := (EReal.tendsto_coe.2 hl).congr' heq.symm
  have hh := hlim.limsup_eq
  rw [hi] at hh
  exact EReal.coe_injective hh

theorem continuous_leadingReal (c : ℂ) (ρ : ℝ) :
    Continuous (CRGPhaseDirections.leadingReal c ρ) := by
  unfold CRGPhaseDirections.leadingReal
  fun_prop

/-- Finite continuous alternatives holding almost everywhere hold everywhere. -/
theorem alternatives_everywhere {ι : Type*} [Fintype ι]
    (h : ℝ → ℝ) (φ : ι → ℝ → ℝ) (hh : Continuous h)
    (hφ : ∀ i, Continuous (φ i))
    (hae : ∀ᵐ θ : ℝ, ∃ i : ι, h θ = φ i θ) :
    ∀ θ : ℝ, ∃ i : ι, h θ = φ i θ := by
  let C : Set ℝ := {θ | ∃ i : ι, h θ = φ i θ}
  have hC : IsClosed C := by
    have heq : C = ⋃ i : ι, {θ | h θ = φ i θ} := by ext θ; simp [C]
    rw [heq]
    exact isClosed_iUnion_of_finite (fun i => isClosed_eq hh (hφ i))
  intro θ
  exact closure_minimal (subset_refl C) hC ((volume.dense_of_ae hae) θ)

/-- The indicator is derived from selected polynomial phases, then extended
to every angle. Phases whose degree is below the order give the zero candidate. -/
theorem indicator_alternatives {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {ρ : ℝ} (hρ : 0 < ρ)
    (horder : CRGOrder.IsOrder f ρ) (htype : LevinGrowth.FinitePositiveType f ρ)
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (P : ι → Polynomial ℂ)
    (hP0 : ∀ i, (P i).coeff 0 = 0) (hphase : PhaseComparison p hp P f)
    {h : LevinGrowth.Direction → ℝ} (hcrg : LevinGrowth.DiskRegular f ρ h)
    (hi : LevinGrowth.IsIndicator f ρ h) :
    ∀ θ : ℝ, ∃ i : ι,
      h (CRGOrderLevin.angleDirection θ) =
        CRGPhaseDirections.leadingReal
          (if ((P i).natDegree : ℝ) / (p i : ℝ) = ρ then (P i).leadingCoeff else 0) ρ θ := by
  let d : ι → ℚ := fun i => ((P i).natDegree : ℚ) / (p i : ℚ)
  have hdata := ae_rayData_of_phase_comparison p hp P hP0 hphase
  have hg := GundersenTheorem.ae_ray_input hf
    (LevinGrowth.finitePositiveType_nontrivial htype) hρ.le horder.2.1
  apply alternatives_everywhere
    (fun θ => h (CRGOrderLevin.angleDirection θ))
    (fun i => CRGPhaseDirections.leadingReal
      (if ((P i).natDegree : ℝ) / (p i : ℝ) = ρ then (P i).leadingCoeff else 0) ρ)
    (hcrg.1.comp CRGOrderLevin.continuous_angleDirection)
    (fun i => continuous_leadingReal _ _)
  filter_upwards [hdata, hg] with θ hθ hgθ
  obtain ⟨i, hiθ⟩ := hθ
  have hle : (d i : ℝ) ≤ ρ := by
    apply CRGOrderLevin.degree_le_of_two_sided hiθ hρ.le
    intro δ hδ
    obtain ⟨C, _, hC⟩ := hgθ.2.2 δ hδ
    exact ⟨C, hC⟩
  have hh := indicator_eq_of_limit hi hiθ.nonzero (normalized_limit_value hiθ hρ hle)
  refine ⟨i, hh.trans ?_⟩
  simp only [d, Rat.cast_div, Rat.cast_natCast] at hh ⊢
  split_ifs with heq
  · rw [leading_eq_monomial, heq]
  · simp [CRGPhaseDirections.leadingReal]

#print axioms finite_positive_type_witness
#print axioms order_mem_of_ae_rayData
#print axioms indicator_eq_of_limit
#print axioms alternatives_everywhere
#print axioms indicator_alternatives
end CRGIndicatorAlternatives
