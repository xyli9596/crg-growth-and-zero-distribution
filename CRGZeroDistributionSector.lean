import CRGZeroDistributionCompact

/-! Actual radial-sector divisor counts, scaling invariance of multiplicities,
and the dyadic recurrence needed for Corollary 3.6(2). -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory Real Complex MeromorphicOn InnerProductSpace
open scoped Topology BigOperators
namespace CRGZeroDistributionSector
open LevinGrowth LevinIndicatorModulus CRGZeroDistributionScaled CRGZeroDistributionCompact

/-- Zero-counting domains use the actual compact set of directions. The
origin is included, as in the manuscript's `|z| ≤ r` count. -/
def radialSector (D : Set Direction) (r : ℝ) : Set ℂ :=
  (fun x : ℝ × Direction => rayPoint x.1 x.2) '' (Icc 0 r ×ˢ D)

def annularSector (D : Set Direction) : Set ℂ :=
  (fun x : ℝ × Direction => rayPoint x.1 x.2) '' (Icc 1 2 ×ˢ D)

theorem radialSector_compact {D : Set Direction} (hD : IsCompact D) (r : ℝ) :
    IsCompact (radialSector D r) := by
  exact (isCompact_Icc.prod hD).image (by unfold rayPoint; fun_prop)


theorem radialSector_mono (D : Set Direction) {r s : ℝ} (hrs : r ≤ s) :
    radialSector D r ⊆ radialSector D s := by
  rintro z ⟨⟨t, ζ⟩, ⟨ht, hζ⟩, rfl⟩
  exact ⟨(t, ζ), ⟨⟨ht.1, ht.2.trans hrs⟩, hζ⟩, rfl⟩

theorem zeroCount_radialSector_monotone {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {D : Set Direction} (hD : IsCompact D) :
    Monotone (fun r : ℝ => zeroCount f (radialSector D r)) := by
  intro r s hrs
  exact zeroCount_mono (radialSector_compact hD r) (radialSector_compact hD s)
    (radialSector_mono D hrs)
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).mono (subset_univ _))

theorem zeroCount_radialSector_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (D : Set Direction) (r : ℝ) : 0 ≤ zeroCount f (radialSector D r) :=
  zeroCount_nonneg ((Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).mono (subset_univ _))

theorem annularSector_compact {D : Set Direction} (hD : IsCompact D) :
    IsCompact (annularSector D) := by
  exact (isCompact_Icc.prod hD).image (by unfold rayPoint; fun_prop)

theorem annularSector_norm {D : Set Direction} {z : ℂ} (hz : z ∈ annularSector D) :
    ‖z‖ ∈ Icc (1 : ℝ) 2 := by
  obtain ⟨⟨t, ζ⟩, ⟨ht, _hζ⟩, rfl⟩ := hz
  rw [norm_rayPoint (by linarith [ht.1])]
  exact ht

theorem annularSector_direction_mem {D : Set Direction} {z : ℂ}
    (hz : z ∈ annularSector D) : normalizedDirection z ∈ D := by
  obtain ⟨⟨t, ζ⟩, ⟨ht, hζ⟩, rfl⟩ := hz
  rw [LevinScaledBounds.normalizedDirection_rayPoint (by linarith [ht.1])]
  exact hζ

/-- Scaling by a nonzero complex constant preserves every actual zero
multiplicity and reindexes the finite divisor mass bijectively. -/
theorem zeroCount_scale {f : ℂ → ℂ} {K : Set ℂ} (hf : Differentiable ℂ f)
    (a : ℂ) (ha : a ≠ 0) :
    zeroCount (fun z => f (a*z)) K = zeroCount f ((fun z => a*z) '' K) := by
  have hfa : AnalyticOnNhd ℂ f univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hF : AnalyticOnNhd ℂ (fun z => f (a*z)) univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (hf.comp (by fun_prop))
  have hbij : Function.Bijective (fun z : ℂ => a*z) := (Equiv.mulLeft₀ a ha).bijective
  have hd (z : ℂ) :
      MeromorphicOn.divisor (fun z => f (a*z)) K z =
        MeromorphicOn.divisor f ((fun z => a*z) '' K) (a*z) := by
    by_cases hz : z ∈ K
    · rw [(hF.mono (subset_univ _)).divisor_apply hz,
        (hfa.mono (subset_univ _)).divisor_apply (mem_image_of_mem _ hz)]
      have ho := analyticOrderAt_comp_of_deriv_ne_zero (f := f)
        (show AnalyticAt ℂ (fun z : ℂ => a*z) z from analyticAt_const.mul analyticAt_id)
        (show deriv (fun z : ℂ => a*z) z ≠ 0 by simpa using ha)
      simpa only [Function.comp_def] using congrArg (fun n : ℕ∞ => (n.map (fun m : ℕ => (m : ℤ))).untop₀) ho
    · have haz : a*z ∉ (fun z => a*z) '' K := by
        rintro ⟨w, hw, he⟩
        exact hz (hbij.1 he ▸ hw)
      rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz,
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ haz]
  unfold zeroCount
  exact congrArg (fun n : ℤ => (n : ℝ))
    (finsum_eq_of_bijective (fun z : ℂ => a*z) hbij hd)

/-- The outer radial sector is covered by the inner sector and one scaled
normalized annular sector. Boundaries may overlap, which only improves the
upper zero-count estimate. -/
theorem radialSector_dyadic_cover (D : Set Direction) {r : ℝ} (hr : 0 < r) :
    radialSector D (2*r) ⊆ radialSector D r ∪
      (fun z : ℂ => (r : ℂ)*z) '' annularSector D := by
  rintro z ⟨⟨t, ζ⟩, ⟨ht, hζ⟩, rfl⟩
  by_cases htr : t ≤ r
  · exact Or.inl ⟨(t, ζ), ⟨⟨ht.1, htr⟩, hζ⟩, rfl⟩
  · apply Or.inr
    refine ⟨rayPoint (t/r) ζ, ⟨(t/r, ζ), ⟨?_, hζ⟩, rfl⟩, ?_⟩
    · constructor
      · exact (le_div_iff₀ hr).mpr (by linarith [not_le.mp htr])
      · exact (div_le_iff₀ hr).mpr (by linarith [ht.2])
    · unfold rayPoint
      have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      rw [Complex.ofReal_div]
      field_simp

/-- The actual all-radius count obeys the dyadic recurrence, whose annular
term is exactly the scaled actual zero count from the compact-cover theorem. -/
theorem zeroCount_radialSector_recurrence {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {D : Set Direction} (hD : IsCompact D) {r : ℝ} (hr : 0 < r) :
    zeroCount f (radialSector D (2*r)) ≤ zeroCount f (radialSector D r) +
      zeroCount (fun z => f ((r : ℂ)*z)) (annularSector D) := by
  let V : Bool → Set ℂ := fun b => if b then
    (fun z : ℂ => (r : ℂ)*z) '' annularSector D else radialSector D r
  have hV : ∀ b, IsCompact (V b) := by
    intro b
    cases b
    · exact radialSector_compact hD r
    · exact (annularSector_compact hD).image (by fun_prop)
  have hcover : radialSector D (2*r) ⊆ ⋃ b, V b := by
    intro z hz
    rcases radialSector_dyadic_cover D hr hz with hinner | houter
    · exact mem_iUnion.mpr ⟨false, hinner⟩
    · exact mem_iUnion.mpr ⟨true, houter⟩
  have hh := zeroCount_le_finite_cover (radialSector_compact hD (2*r)) V hV
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf) hcover
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simpa only [V, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    zeroCount_scale hf (r : ℂ) hc, add_comm] using hh

/-- The annular term of the actual radial-sector recurrence is negligible
for CRG whenever its homogeneous indicator is harmonic on this closed
normalized angular region. -/
theorem annularSector_zero_density {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hreg : RadialRegular f ρ h) {D : Set Direction} (hD : IsCompact D)
    (hH : ∀ w ∈ annularSector D, HarmonicAt (homogeneousIndicator ρ h) w) :
    Tendsto (fun R : ℝ => zeroCount (fun z => f ((R : ℂ)*z)) (annularSector D) / R^ρ)
      atTop (𝓝 0) := by
  exact compact_zero_density hf hρ htype hreg (annularSector_compact hD)
    (fun w hw => by have hn := annularSector_norm hw; constructor <;> linarith [hn.1, hn.2]) hH

#print axioms zeroCount_scale
#print axioms zeroCount_radialSector_recurrence
#print axioms annularSector_zero_density
end CRGZeroDistributionSector
