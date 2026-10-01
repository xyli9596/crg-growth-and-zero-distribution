import LevinGrowth
import LevinAssembly
import LevinFiniteType

/-!
# The dense-ray criterion for globally zero-free entire functions

This is a genuine special case: the analytic modulus is derived from the
entire-function and finite-type hypotheses. The conclusion is radial regularity.
General entire functions with zeros, and the C₀-disk conclusion, are not claimed.
-/

noncomputable section
open MeasureTheory Set Filter Topology Metric
open LevinGrowth LevinDensity LevinAssembly

namespace LevinZeroFree

instance directionCompactSpace : CompactSpace Direction := by
  have hset : {ζ : ℂ | ‖ζ‖ = 1} = sphere (0 : ℂ) 1 := by
    ext ζ
    simp only [mem_ofPred_eq, mem_sphere, dist_zero_right]
  have hc : IsCompact {ζ : ℂ | ‖ζ‖ = 1} := by
    rw [hset]
    exact isCompact_sphere _ _
  exact isCompact_iff_compactSpace.mp hc

instance directionNonempty : Nonempty Direction := ⟨⟨1, norm_one⟩⟩

/-- Translate the epsilon definition on one ray into its outside filter. -/
theorem rayRegular_tendsto {f : ℂ → ℂ} {ρ : ℝ} {ζ : Direction} {a : ℝ}
    (h : RayRegular f ρ ζ a) :
    ∃ E : Set ℝ, MeasurableSet E ∧ ZeroRadialDensity E ∧
      Tendsto (fun r => normalizedLog f ρ r ζ) (outsideFilter E) (𝓝 a) := by
  obtain ⟨E, hEm, hEz, hlim⟩ := h
  refine ⟨E, hEm, hEz, Metric.tendsto_nhds.2 ?_⟩
  intro ε hε
  obtain ⟨R, _, hR⟩ := hlim ε hε
  apply eventually_inf_principal.mpr
  filter_upwards [eventually_ge_atTop R] with r hr hrE
  simpa only [Real.dist_eq] using (hR r hr hrE).2

/-- Convert a uniform limit outside an actual zero-density radial set to the
paper-facing radial definition. The nonvanishing clause is retained explicitly. -/
theorem radialRegular_of_uniform_limit {f : ℂ → ℂ} {ρ : ℝ}
    (hnz : ∀ z : ℂ, f z ≠ 0) (E : Set ℝ)
    (hEm : MeasurableSet E) (hEz : ZeroRadialDensity E) (h : Direction → ℝ)
    (hh : Continuous h)
    (hlim : TendstoUniformly (normalizedLog f ρ) h (outsideFilter E)) :
    RadialRegular f ρ h := by
  refine ⟨hh, E, hEm, hEz, ?_⟩
  intro ε hε
  have hevent := (Metric.tendstoUniformly_iff.1 hlim) ε hε
  obtain ⟨R, hR⟩ := eventually_atTop.1 (eventually_inf_principal.1 hevent)
  refine ⟨max R 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro r hr hrE ζ
  refine ⟨hnz _, ?_⟩
  have hb := hR r ((le_max_left _ _).trans hr) hrE ζ
  simpa only [Real.dist_eq, abs_sub_comm] using hb

/-- A dense set of directions admits a countable dense sequence of directions
inside it. This uses the actual topology inherited from the complex plane. -/
theorem exists_dense_sequence_in {S : Set Direction} (hS : Dense S) :
    ∃ d : ℕ → Direction, DenseRange d ∧ ∀ n, d n ∈ S := by
  obtain ⟨T, hTS, hTc, hTd⟩ := hS.exists_countable_dense_subset
  obtain ⟨d, hd⟩ := hTc.exists_eq_range hTd.nonempty
  refine ⟨d, ?_, ?_⟩
  · show Dense (range d)
    rwa [← hd]
  · intro n
    apply hTS
    rw [hd]
    exact mem_range_self n

/-- Globally zero-free entire functions of finite positive type satisfy the
radial dense-ray criterion. The angular equicontinuity is proved analytically
from these hypotheses by `LevinFiniteType`, rather than assumed here. -/
theorem radialRegular_of_zero_free_dense_sequence {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 ≤ ρ)
    (htype : FinitePositiveType f ρ) (hnz : ∀ z : ℂ, f z ≠ 0)
    (d : ℕ → Direction) (hd : DenseRange d)
    (hgood : ∀ n, ∃ a : ℝ, RayRegular f ρ (d n) a) :
    ∃ h : Direction → ℝ, RadialRegular f ρ h := by
  choose a ha using hgood
  have hdir (n : ℕ) := rayRegular_tendsto (ha n)
  have heq : ∃ E : Set ℝ, MeasurableSet E ∧ ZeroRadialDensity E ∧
      LevinCompact.AsymptoticUniformEquicontinuous (normalizedLog f ρ) (outsideFilter E) := by
    refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
    · intro ε hε
      refine ⟨0, le_rfl, fun R _ => ?_⟩
      simp only [empty_inter, measure_empty]
      exact bot_le
    · apply asymptoticUniformEquicontinuous_mono
        (LevinFiniteType.zero_free_asymptotic_equicontinuity hf hρ htype hnz)
      exact inf_le_left
  obtain ⟨E, hEm, hEz, h, hh, hlim, _⟩ :=
    exists_uniform_limit_from_separate_exceptional_sets
      (normalizedLog f ρ) d hd a hdir heq
  exact ⟨h, radialRegular_of_uniform_limit hnz E hEm hEz h hh.continuous hlim⟩

/-- Dense-set version of the zero-free special case, without a preselected
countable dense sequence. The conclusion remains radial regularity. -/
theorem radialRegular_of_zero_free_dense_rays {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 ≤ ρ)
    (htype : FinitePositiveType f ρ) (hnz : ∀ z : ℂ, f z ≠ 0)
    (hgood : Dense {ζ : Direction | ∃ a : ℝ, RayRegular f ρ ζ a}) :
    ∃ h : Direction → ℝ, RadialRegular f ρ h := by
  obtain ⟨d, hd, hmem⟩ := exists_dense_sequence_in hgood
  exact radialRegular_of_zero_free_dense_sequence hf hρ htype hnz d hd hmem

end LevinZeroFree

#print axioms LevinZeroFree.directionCompactSpace
#print axioms LevinZeroFree.directionNonempty
#print axioms LevinZeroFree.rayRegular_tendsto
#print axioms LevinZeroFree.radialRegular_of_uniform_limit
#print axioms LevinZeroFree.exists_dense_sequence_in

#print axioms LevinZeroFree.radialRegular_of_zero_free_dense_sequence
#print axioms LevinZeroFree.radialRegular_of_zero_free_dense_rays
