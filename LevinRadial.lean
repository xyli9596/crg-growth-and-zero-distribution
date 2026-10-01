import LevinZeroFree
import LevinSmallDensity

/-!
The radial dense-ray criterion for general entire functions. The assembly
lemmas below retain the analytic small-density premise explicitly. LevinGeneral
discharges it using the annular estimates and origin-zero reduction.
-/
noncomputable section
open Set Filter MeasureTheory Topology
open LevinGrowth LevinDensity LevinAssembly
namespace LevinRadial

/-- Add the actual countable set of zero radii to a uniform-limit exception.
This recovers the nonvanishing clause of the paper-facing radial definition. -/
theorem radialRegular_of_uniform_limit {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hn : ∃ z : ℂ, f z ≠ 0)
    (E : Set ℝ) (hEm : MeasurableSet E) (hEz : ZeroRadialDensity E)
    (h : Direction → ℝ) (hh : Continuous h)
    (hlim : TendstoUniformly (normalizedLog f ρ) h (outsideFilter E)) :
    RadialRegular f ρ h := by
  refine ⟨hh, E ∪ zeroRadii f, hEm.union (zeroRadii_countable hf hn).measurableSet,
    hEz.union (zeroRadii_zero_density hf hn), ?_⟩
  intro ε hε
  have hevent := (Metric.tendstoUniformly_iff.1 hlim) ε hε
  obtain ⟨R, hR⟩ := eventually_atTop.1 (eventually_inf_principal.1 hevent)
  refine ⟨max R 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro r hr hrE ζ
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1).trans
    ((le_max_right R 1).trans hr)
  refine ⟨nonzero_of_not_zeroRadii hr0 (fun hz => hrE (Or.inr hz)) ζ, ?_⟩
  have hb := hR r ((le_max_left _ _).trans hr) (fun he => hrE (Or.inl he)) ζ
  simpa only [Real.dist_eq, abs_sub_comm] using hb

/-- Assemble the general radial conclusion from an explicit analytic estimate.
The actual entire-function estimate is supplied separately, not as an axiom. -/
theorem radialRegular_of_dense_sequence_and_small_density {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hn : ∃ z : ℂ, f z ≠ 0)
    (d : ℕ → Direction) (hd : DenseRange d)
    (hgood : ∀ n, ∃ a : ℝ, RayRegular f ρ (d n) a)
    (heq : ∀ η : ℝ, 0 < η → ∃ E : Set ℝ, MeasurableSet E ∧
      LevinSmallDensity.EventuallyDensityLE E η ∧
      LevinCompact.AsymptoticUniformEquicontinuous (normalizedLog f ρ) (outsideFilter E)) :
    ∃ h : Direction → ℝ, RadialRegular f ρ h := by
  choose a ha using hgood
  obtain ⟨E, hEm, hEz, h, hh, hlim, _⟩ :=
    LevinSmallDensity.exists_zero_density_uniform_limit_of_arbitrarily_small_density
      (normalizedLog f ρ) d hd a
      (fun n => LevinZeroFree.rayRegular_tendsto (ha n)) heq
  exact ⟨h, radialRegular_of_uniform_limit hf hn E hEm hEz h hh.continuous hlim⟩

#print axioms radialRegular_of_uniform_limit
#print axioms radialRegular_of_dense_sequence_and_small_density
end LevinRadial
