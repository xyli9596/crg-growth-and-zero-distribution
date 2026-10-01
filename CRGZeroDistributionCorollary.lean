import CRGZeroDistributionHarmonic
import CRGZeroDistributionDyadic

/-! Manuscript Corollary 3.6, both numbered assertions, for the actual fixed
nonmonic exponential-polynomial differential equation. The angular zero
counts are actual analytic-divisor counts with multiplicities, and their
all-radius little-o conclusion is obtained by dyadic accumulation of the
proved annular zero-count estimates. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Metric Real Complex InnerProductSpace Polynomial
open scoped Topology
namespace CRGZeroDistributionCorollary
open LevinGrowth LevinIndicatorModulus CRGIndicatorFixedPhases CRGIndicatorAlternatives
open CRGPhaseDirections CRGZeroDistributionScaled CRGZeroDistributionSector
open CRGZeroDistributionHarmonic CRGIndicatorCorollary

/-- Accumulate the actual negligible annular divisor masses. -/
theorem radialSector_zero_density {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hreg : RadialRegular f ρ h) {D : Set Direction} (hD : IsCompact D)
    (hH : ∀ w ∈ annularSector D, HarmonicAt (homogeneousIndicator ρ h) w) :
    Tendsto (fun r : ℝ => zeroCount f (radialSector D r) / r^ρ) atTop (𝓝 0) := by
  apply CRGZeroDistributionDyadic.radial_density_of_annular_density hρ
    (fun r _ => zeroCount_radialSector_nonneg hf D r)
    ((zeroCount_radialSector_monotone hf hD).monotoneOn (Ioi 0))
    (fun r hr => zeroCount_radialSector_recurrence hf hD hr)
  exact annularSector_zero_density hf hρ htype hreg hD hH

/-- A compact closed angular region avoiding all exceptional rays has the
manuscript's `o(r^ρ)` actual zero count, including every radius and multiplicity. -/
theorem radialSector_zero_density_off_rays {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hreg : RadialRegular f ρ h) (R : Finset Direction)
    (hH : ∀ z : ℂ, z ≠ 0 → normalizedDirection z ∉ R →
      HarmonicAt (homogeneousIndicator ρ h) z)
    {D : Set Direction} (hD : IsCompact D) (haway : Disjoint D (R : Set Direction)) :
    Tendsto (fun r : ℝ => zeroCount f (radialSector D r) / r^ρ) atTop (𝓝 0) := by
  apply radialSector_zero_density hf hρ htype hreg hD
  intro w hw
  have hwn := annularSector_norm hw
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (by linarith [hwn.1])
  exact hH w hwne (fun hmem => Set.disjoint_left.mp haway (annularSector_direction_mem hw) hmem)

/-- Full Corollary 3.6 for a fixed collected equation: the same finite set
of actual rays gives both the piecewise harmonic indicator formulas and
negligible zeros on every compact angular region separated from those rays.
The first clause bounds all actual order/indicator pairs, without a CRG
hypothesis in the counted set. -/
theorem corollary_3_6_collected {n : ℕ} (E : EquationData n) :
    {x | SolutionIndicatorPair E x}.Finite ∧
    ∃ R : Finset Direction, ∀ f : ℂ → ℂ, Differentiable ℂ f → CRGOrder.FiniteOrder f →
      (¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z) → E.Solves f →
      ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ : ℝ) ∧ FinitePositiveType f (σ : ℝ) ∧
        ∃ h : Direction → ℝ, DiskRegular f (σ : ℝ) h ∧ IsIndicator f (σ : ℝ) h ∧
          (∀ u v : ℝ, u < v → Ioo u v ⊆ Icc 0 (2*Real.pi) →
            (∀ θ ∈ Ioo u v, CRGOrderLevin.angleDirection θ ∉ R) →
            ∃ c : ℂ, ∀ θ ∈ Ioo u v,
              h (CRGOrderLevin.angleDirection θ) = leadingReal c (σ : ℝ) θ) ∧
          (∀ D : Set Direction, IsCompact D → Disjoint D (R : Set Direction) →
            Tendsto (fun r : ℝ => zeroCount f (radialSector D r) / r^(σ : ℝ)) atTop (𝓝 0)) := by
  classical
  obtain ⟨T, _hT, hpartition⟩ := exists_fixed_indicator_partition E
  obtain ⟨S, hS⟩ := exists_fixed_harmonic_rays E
  let R := T.image CRGOrderLevin.angleDirection ∪ S
  refine ⟨finite_solution_indicator_pairs E, R, ?_⟩
  intro f hf hfinite htrans heq
  obtain ⟨σ, hσ, hoσ, htσ, h, hcrg, hi, hpiece⟩ := hpartition f hf hfinite htrans heq
  obtain ⟨τ, _hτ, hoτ, _htτ, h₁, hcrg₁, hi₁, hharm⟩ := hS f hf hfinite htrans heq
  have heqστ : σ = τ := Rat.cast_injective (isOrder_unique hoσ hoτ)
  subst τ
  have hheq : h₁ = h := by
    funext ζ
    exact EReal.coe_injective ((hi₁ ζ).symm.trans (hi ζ))
  subst h₁
  refine ⟨σ, hσ, hoσ, htσ, h, hcrg, hi, ?_, ?_⟩
  · intro u v huv hsub havoid
    apply hpiece u v huv hsub
    apply Set.disjoint_left.mpr
    intro θ hθ hθT
    exact havoid θ hθ (Finset.mem_union.mpr
      (Or.inl (Finset.mem_image.mpr ⟨θ, hθT, rfl⟩)))
  · intro D hD haway
    have hawayS : Disjoint D (S : Set Direction) := haway.mono_right
      (fun ζ hζ => Finset.mem_union.mpr (Or.inr hζ))
    exact radialSector_zero_density_off_rays hf (by exact_mod_cast hσ) htσ
      (diskRegular_radialRegular hcrg) S hharm hD hawayS

/-- Both numbered assertions of manuscript Corollary 3.6 for the original
possibly nonmonic exponential-polynomial ODE. The fixed finite ray set is
constructed from its coefficients before a solution is chosen. -/
theorem corollary_3_6 {n : ℕ} (A : Fin (n+1) → ℂ → ℂ)
    (hA : ∀ j, CRGExponentialCoefficients.IsExponentialPolynomial (A j))
    (htop : ∃ z : ℂ, A (Fin.last n) z ≠ 0) :
    {x : ℚ × (Direction → ℝ) |
      ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ CRGOrder.FiniteOrder f ∧
        (¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z) ∧
        SolvesEquation A f ∧ CRGOrder.IsOrder f (x.1 : ℝ) ∧ IsIndicator f (x.1 : ℝ) x.2}.Finite ∧
    ∃ R : Finset Direction, ∀ f : ℂ → ℂ, Differentiable ℂ f → CRGOrder.FiniteOrder f →
      (¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z) → SolvesEquation A f →
      ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ : ℝ) ∧ FinitePositiveType f (σ : ℝ) ∧
        ∃ h : Direction → ℝ, DiskRegular f (σ : ℝ) h ∧ IsIndicator f (σ : ℝ) h ∧
          (∀ u v : ℝ, u < v → Ioo u v ⊆ Icc 0 (2*Real.pi) →
            (∀ θ ∈ Ioo u v, CRGOrderLevin.angleDirection θ ∉ R) →
            ∃ c : ℂ, ∀ θ ∈ Ioo u v,
              h (CRGOrderLevin.angleDirection θ) = leadingReal c (σ : ℝ) θ) ∧
          (∀ D : Set Direction, IsCompact D → Disjoint D (R : Set Direction) →
            Tendsto (fun r : ℝ => zeroCount f (radialSector D r) / r^(σ : ℝ)) atTop (𝓝 0)) := by
  obtain ⟨E, hE⟩ := exists_fixed_equation_data A hA htop
  obtain ⟨_hfinite, R, hR⟩ := corollary_3_6_collected E
  exact ⟨finite_actual_solution_indicator_pairs A hA htop, R,
    fun f hf hfinite htrans heq => hR f hf hfinite htrans ((hE f).mp heq)⟩

#print axioms radialSector_zero_density
#print axioms radialSector_zero_density_off_rays
#print axioms corollary_3_6_collected
#print axioms corollary_3_6
end CRGZeroDistributionCorollary
