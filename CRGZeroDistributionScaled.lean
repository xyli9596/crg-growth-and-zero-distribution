import CRGZeroDistributionLocal
import LevinScaledBounds

/-! Actual local zero density from completely regular growth and a locally
harmonic homogeneous indicator. This retains analytic-divisor multiplicities. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory Real Complex MeromorphicOn
open scoped Topology
namespace CRGZeroDistributionScaled
open LevinGrowth LevinScaledBounds LevinIndicatorModulus

/-- The actual zero count, with multiplicities, on a compact domain. -/
def zeroCount (f : ℂ → ℂ) (U : Set ℂ) : ℝ :=
  ((∑ᶠ z, MeromorphicOn.divisor f U z : ℤ) : ℝ)

theorem zeroCount_nonneg {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) : 0 ≤ zeroCount f U := by
  unfold zeroCount
  exact_mod_cast (finsum_nonneg (fun z => hf.divisor_nonneg z))

/-- Restricting the compact zero-counting domain can only lower its mass. -/
theorem zeroCount_mono {f : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsCompact U) (hV : IsCompact V) (hUV : U ⊆ V)
    (hf : AnalyticOnNhd ℂ f V) : zeroCount f U ≤ zeroCount f V := by
  have hfU := hf.mono hUV
  have hle : (MeromorphicOn.divisor f U : ℂ → ℤ) ≤ MeromorphicOn.divisor f V := by
    intro z
    by_cases hz : z ∈ U
    · rw [hfU.divisor_apply hz, hf.divisor_apply (hUV hz)]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
      exact hf.divisor_nonneg z
  have hh := finsum_le_finsum'
    ((MeromorphicOn.divisor f U).finiteSupport hU)
    ((MeromorphicOn.divisor f V).finiteSupport hV) hle
  unfold zeroCount
  exact_mod_cast hh

/-- A fixed normalized disk on which the homogeneous indicator is harmonic
has an arbitrarily small normalized zero-count bound at every large scale. -/
theorem eventually_local_zeroCount_bound {f : ℂ → ℂ} {ρ : ℝ}
    {h : Direction → ℝ} (hf : Differentiable ℂ f) (hρ : 0 < ρ)
    (htype : FinitePositiveType f ρ) (hreg : RadialRegular f ρ h)
    {w : ℂ} (hw : ‖w‖ ∈ Icc (1/2 : ℝ) 3) {δ a : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/128) (ha : 0 < a)
    (hH : InnerProductSpace.HarmonicOnNhd
      (homogeneousIndicator ρ h) (ball w (16*δ))) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      zeroCount (fun z => f ((R : ℂ)*z)) (closedBall w δ) ≤
        (2*a/Real.log 2) * R^ρ := by
  obtain ⟨R₀, hR₀, hbds⟩ := exists_scaled_bounds hf hρ htype hreg ha hδ (by linarith)
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR
  have hRpos : 0 < R := hR₀.trans_le hR
  have hT : 0 < R^ρ := Real.rpow_pos_of_pos hRpos ρ
  obtain ⟨hupper, hgood⟩ := hbds R hR
  obtain ⟨q, hqnear, _hqnorm, hFq, hqgood⟩ := hgood w hw
  let F : ℂ → ℂ := fun z => f ((R : ℂ)*z)
  have hF : Differentiable ℂ F := hf.comp (by fun_prop)
  have hFA : AnalyticOnNhd ℂ F univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  have hqH : InnerProductSpace.HarmonicOnNhd
      (fun z => R^ρ * homogeneousIndicator ρ h z) (ball q (8*δ)) := by
    intro z hz
    have hzw : dist z w < 16*δ := by
      have htri := dist_triangle z q w
      have hzq : dist z q < 8*δ := mem_ball.mp hz
      have hqw : dist q w ≤ δ := by simpa only [dist_eq_norm] using hqnear
      linarith
    change InnerProductSpace.HarmonicAt (R^ρ • homogeneousIndicator ρ h) z
    exact (hH z (mem_ball.mpr hzw)).const_smul (c := R^ρ)
  have houter : ∀ z ∈ sphere q (4*δ), ‖F z‖ ≤
      Real.exp (R^ρ * homogeneousIndicator ρ h z + a*R^ρ) := by
    intro z hz
    have hzq : dist z q = 4*δ := mem_sphere.mp hz
    have hqw : dist q w ≤ δ := by simpa only [dist_eq_norm] using hqnear
    have hzw : ‖z-w‖ ≤ 5*δ := by
      calc
        ‖z-w‖ = dist z w := by rw [dist_eq_norm]
        _ ≤ dist z q + dist q w := dist_triangle z q w
        _ ≤ 5*δ := by linarith
    have hn := abs_norm_sub_norm_le z w
    have hn' := (abs_le.mp (hn.trans hzw))
    have hzann : ‖z‖ ∈ Icc (1/4 : ℝ) 4 := by
      constructor <;> linarith [hw.1, hw.2, hn'.1, hn'.2]
    exact (hupper z hzann).trans_eq (by congr 1; ring)
  have hlo : R^ρ * homogeneousIndicator ρ h q - a*R^ρ ≤ Real.log ‖F q‖ := by
    have hl := (abs_le.mp hqgood).1
    have hh : homogeneousIndicator ρ h q - a ≤ Real.log ‖F q‖ / R^ρ := by
      dsimp [F]
      linarith
    have hh' := (le_div_iff₀ hT).mp hh
    nlinarith
  have hcount := CRGZeroDistributionLocal.zero_count_of_harmonic_profile
    (H := fun z => R^ρ * homogeneousIndicator ρ h z)
    (show 0 < 2*δ by positivity) (show 0 ≤ a*R^ρ by positivity)
    (hFA.mono (subset_univ _))
    (by simpa only [show 4*(2*δ) = 8*δ by ring] using hqH) hFq
    (by simpa only [show 2*(2*δ) = 4*δ by ring] using houter) hlo
  have hsub : closedBall w δ ⊆ closedBall q (2*δ) := by
    intro z hz
    have hzdist : dist z w ≤ δ := mem_closedBall.mp hz
    have hqw : dist w q ≤ δ := by simpa only [dist_eq_norm, norm_sub_rev] using hqnear
    apply mem_closedBall.mpr
    have hh := dist_triangle z w q
    linarith
  have hmono := zeroCount_mono (isCompact_closedBall w δ) (isCompact_closedBall q (2*δ))
    hsub (hFA.mono (subset_univ _))
  apply hmono.trans
  change zeroCount F (closedBall q (2*δ)) ≤ _
  dsimp only [zeroCount]
  apply hcount.trans_eq
  ring

/-- The actual scaled local zero count tends to zero after division by the
order power, wherever the homogeneous indicator is harmonic. -/
theorem local_zero_density {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hreg : RadialRegular f ρ h) {w : ℂ} (hw : ‖w‖ ∈ Icc (1/2 : ℝ) 3)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/128)
    (hH : InnerProductSpace.HarmonicOnNhd
      (homogeneousIndicator ρ h) (ball w (16*δ))) :
    Tendsto (fun R : ℝ => zeroCount (fun z => f ((R : ℂ)*z)) (closedBall w δ) / R^ρ)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let a := ε * Real.log 2 / 4
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨R₀, hR₀, hb⟩ := eventually_local_zeroCount_bound hf hρ htype hreg hw hδ hδ1 ha hH
  filter_upwards [eventually_ge_atTop R₀] with R hR
  have hRpos := hR₀.trans_le hR
  have hT : 0 < R^ρ := Real.rpow_pos_of_pos hRpos ρ
  have hFn : AnalyticOnNhd ℂ (fun z => f ((R : ℂ)*z)) (closedBall w δ) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (hf.comp (by fun_prop))).mono (subset_univ _)
  have hn := div_nonneg (zeroCount_nonneg hFn) hT.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  have hh := (div_le_iff₀ hT).mpr (hb R hR)
  have hc : 2*a/Real.log 2 = ε/2 := by dsimp [a]; field_simp; ring
  rw [hc] at hh
  exact hh.trans_lt (by linarith)

#print axioms zeroCount_nonneg
#print axioms zeroCount_mono
#print axioms eventually_local_zeroCount_bound
#print axioms local_zero_density
end CRGZeroDistributionScaled
