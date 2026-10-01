import CRGZeroDistributionProfile

/-! Finite-cover assembly of the actual scaled zero-count estimates. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory Real Complex MeromorphicOn InnerProductSpace
open scoped Topology BigOperators
namespace CRGZeroDistributionCompact
open LevinGrowth LevinIndicatorModulus CRGZeroDistributionScaled

/-- The analytic-divisor mass on a compact set is bounded by the sum of
masses on finitely many compact covering sets. -/
theorem zeroCount_le_finite_cover {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    {K : Set ℂ} (hK : IsCompact K) (V : ι → Set ℂ) (hV : ∀ i, IsCompact (V i))
    (hf : AnalyticOnNhd ℂ f univ) (hcover : K ⊆ ⋃ i, V i) :
    zeroCount f K ≤ ∑ i, zeroCount f (V i) := by
  classical
  have hfK : AnalyticOnNhd ℂ f K := hf.mono (subset_univ _)
  have hfV (i : ι) : AnalyticOnNhd ℂ f (V i) := hf.mono (subset_univ _)
  have hle : (MeromorphicOn.divisor f K : ℂ → ℤ) ≤
      (fun z => ∑ i : ι, MeromorphicOn.divisor f (V i) z) := by
    intro z
    by_cases hz : z ∈ K
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hz)
      have heq : MeromorphicOn.divisor f K z = MeromorphicOn.divisor f (V i) z := by
        rw [hfK.divisor_apply hz, (hfV i).divisor_apply hi]
      rw [heq]
      exact Finset.single_le_sum (fun j _ => (hfV j).divisor_nonneg z) (Finset.mem_univ i)
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
      exact Finset.sum_nonneg (fun i _ => (hfV i).divisor_nonneg z)
  have hfin (i : ι) : Function.HasFiniteSupport
      (MeromorphicOn.divisor f (V i) : ℂ → ℤ) :=
    (MeromorphicOn.divisor f (V i)).finiteSupport (hV i)
  have hs := finsum_le_finsum' ((MeromorphicOn.divisor f K).finiteSupport hK)
    (Function.HasFiniteSupport.sum hfin Finset.univ) hle
  have hsum : (∑ᶠ z, ∑ i : ι, MeromorphicOn.divisor f (V i) z) =
      ∑ i : ι, ∑ᶠ z, MeromorphicOn.divisor f (V i) z := by
    simpa using finsum_sum_comm Finset.univ
      (fun z i => MeromorphicOn.divisor f (V i) z) (fun i _ => hfin i)
  rw [hsum] at hs
  simpa only [zeroCount, Int.cast_sum] using (Int.cast_le.mpr hs :
    ((∑ᶠ z, MeromorphicOn.divisor f K z : ℤ) : ℝ) ≤
      ((∑ i : ι, ∑ᶠ z, MeromorphicOn.divisor f (V i) z : ℤ) : ℝ))

/-- A harmonic-at point admits a proportional disk small enough for the
previous quantitative local zero-count theorem. -/
theorem exists_harmonic_disk {H : ℂ → ℝ} {w : ℂ} (hH : HarmonicAt H w) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/128 ∧ HarmonicOnNhd H (ball w (16*δ)) := by
  have hnhds : {z : ℂ | HarmonicAt H z} ∈ 𝓝 w :=
    (isOpen_setOfPred_harmonicAt H).mem_nhds hH
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let δ := min (d/32) (1/128 : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, min_le_right _ _, ?_⟩
  intro z hz
  apply hball
  apply mem_ball.mpr
  have hh : dist z w < 16*δ := mem_ball.mp hz
  have hbound : δ ≤ d/32 := min_le_left _ _
  linarith

/-- Every compact part of a scaled annulus where the homogeneous indicator
is harmonic has negligible zero mass. The finite disk cover is constructed
from the harmonicity and compactness hypotheses. -/
theorem compact_zero_density {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hreg : RadialRegular f ρ h) {K : Set ℂ} (hK : IsCompact K)
    (hKnorm : ∀ w ∈ K, ‖w‖ ∈ Icc (1/2 : ℝ) 3)
    (hH : ∀ w ∈ K, HarmonicAt (homogeneousIndicator ρ h) w) :
    Tendsto (fun R : ℝ => zeroCount (fun z => f ((R : ℂ)*z)) K / R^ρ)
      atTop (𝓝 0) := by
  classical
  choose δ hδ hδ1 hδH using fun w : K => exists_harmonic_disk (hH w.val w.property)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun w : K => ball w.val (δ w)) (fun _ => isOpen_ball) (by
      intro w hw
      exact mem_iUnion.mpr ⟨⟨w, hw⟩, by simp [hδ]⟩)
  let V : s → Set ℂ := fun i => closedBall i.val.val (δ i.val)
  have hcover : K ⊆ ⋃ i : s, V i := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hs hz)
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, ball_subset_closedBall hzw⟩
  have hlocal (i : s) : Tendsto
      (fun R : ℝ => zeroCount (fun z => f ((R : ℂ)*z)) (V i) / R^ρ)
      atTop (𝓝 0) :=
    local_zero_density hf hρ htype hreg (hKnorm i.val.val i.val.property)
      (hδ i.val) (hδ1 i.val) (hδH i.val)
  have hsum : Tendsto (fun R : ℝ => ∑ i : s,
      zeroCount (fun z => f ((R : ℂ)*z)) (V i) / R^ρ) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hlocal i)
  apply squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hFR : AnalyticOnNhd ℂ (fun z => f ((R : ℂ)*z)) univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (hf.comp (by fun_prop))
    exact div_nonneg (zeroCount_nonneg (hFR.mono (subset_univ _)))
      (Real.rpow_pos_of_pos hR ρ).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hFR : AnalyticOnNhd ℂ (fun z => f ((R : ℂ)*z)) univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (hf.comp (by fun_prop))
    have hh := zeroCount_le_finite_cover hK V (fun i => isCompact_closedBall _ _) hFR hcover
    simpa only [Finset.sum_div] using
      (div_le_div_of_nonneg_right hh (Real.rpow_pos_of_pos hR ρ).le)

#print axioms zeroCount_le_finite_cover
#print axioms exists_harmonic_disk
#print axioms compact_zero_density
end CRGZeroDistributionCompact
