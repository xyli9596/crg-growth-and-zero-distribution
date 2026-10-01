import CRGPuiseuxSectorComparison
import CRGFinitePhaseWindowEndgame

/-! Proposition 5.1: finite coefficient-sector packets construct one fixed
finite Puiseux phase family and the complete analytic conclusions for each
transcendental entire finite-order solution of the actual scalar equation.
Coefficient expansions may diverge, and high formally zero coefficients
remain in the actual flat residual throughout the proof. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial MeasureTheory
open scoped Topology
namespace CRGPuiseuxProposition
open CRGNormalFormGoal CRGPuiseuxSector CRGPuiseuxSectorComparison
variable {n : ℕ} {ι : Type*} [Fintype ι]
variable {a : Fin (n+1) → ℂ → ℂ}

abbrev PhaseIndex (S : ι → Sector a) := (i : ι) × Fin (S i).highest.index.val

def phaseDenominator (S : ι → Sector a) (i : PhaseIndex S) : ℕ :=
  CRGPuiseuxCompanionNormalForm.denominator (S i.1).highest (S i.1).denominator (S i.1).formal

theorem phaseDenominator_positive (S : ι → Sector a) (i : PhaseIndex S) :
    0<phaseDenominator S i := Nat.mul_pos (S i.1).formal.positive (S i.1).positive

def phasePolynomial (S : ι → Sector a) (i : PhaseIndex S) : Polynomial ℂ :=
  (S i.1).formal.normal.phase i.2

theorem phasePolynomial_normalized (S : ι → Sector a) (i : PhaseIndex S) :
    (phasePolynomial S i).coeff 0=0 := (S i.1).formal.normal.phase_zero i.2

def PhaseComparison (S : ι → Sector a) (f : ℂ → ℂ) : Prop :=
  ∀ᵐ θ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),∃i : PhaseIndex S,
    (∀ᶠr : ℝ in atTop,f (ray θ r)≠0) ∧
    ∃M : ℝ,∀ᶠr : ℝ in atTop,
      |Real.log ‖f (ray θ r)‖-(phaseOnRay (phaseDenominator S i) (phasePolynomial S i)
        θ ⟨0,phaseDenominator_positive S i⟩ r).re|≤M*Real.log r

/-- The finite family is defined only from S; derivative estimates, actual
forcing estimates, phase selection and logarithmic comparison are proved. -/
theorem phase_comparison (S : ι → Sector a) (ha : ∀j,Differentiable ℂ (a j))
    (hcover : ∀ᵐθ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),∃i : ι,θ∈(S i).angles)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬∃P : Polynomial ℂ,∀z : ℂ,f z=P.eval z)
    (heq : ∀z : ℂ,∑j : Fin (n+1),a j z*iteratedDeriv j.val f z=0) :
    PhaseComparison S f := by
  obtain ⟨ρ,hρ,ho⟩ := hfinite
  have hn : ∃z : ℂ,f z≠0 := by
    by_contra hz
    push Not at hz
    exact htrans ⟨0,fun z=>by simpa using hz z⟩
  have hg : ∀ᵐθ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),
      (∀r : ℝ,0<r→f (ray θ r)≠0) ∧ GundersenAngles.RayDerivativeBound f ρ n 1 θ :=
    ae_restrict_of_ae ((GundersenTheorem.ae_ray_input hf hn hρ ho).mono
      (fun _ h=>⟨h.1,h.2.1 n 1 zero_lt_one⟩))
  filter_upwards [hcover,hg] with θ hθ hgθ
  obtain ⟨i,hi⟩ := hθ
  have hnon : ∀ᶠr : ℝ in atTop,f (ray θ r)≠0 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact hgθ.1 r hr
  have hjet := CRGCollectedResidual.common_jet_bound θ ρ hρ hnon
    hgθ.2
  obtain ⟨j,M,_hM,hcomp⟩ := CRGPuiseuxSectorComparison.Sector.ray_comparison (S i) ha f hf heq θ hi hnon
    ((n:ℝ)*ρ) (mul_nonneg (Nat.cast_nonneg _) hρ) hjet
  exact ⟨⟨i,j⟩,hnon,M,hcomp⟩

/-- The full analytic conclusion of manuscript Proposition 5.1 follows
from finite coefficient packets covering almost every direction in one turn.
Only complete ray expansions are required, so the uniform closed-subsector
expansions in the manuscript satisfy a stronger source condition. -/
theorem proposition_5_1 (S : ι → Sector a) (ha : ∀j,Differentiable ℂ (a j))
    (hcover : ∀ᵐθ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),∃i : ι,θ∈(S i).angles)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬∃P : Polynomial ℂ,∀z : ℂ,f z=P.eval z)
    (heq : ∀z : ℂ,∑j : Fin (n+1),a j z*iteratedDeriv j.val f z=0) :
    ∃σ : ℚ,0<σ ∧ CRGOrder.IsOrder f (σ:ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ:ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ:ℝ) ∧
      PhaseComparison S f := by
  have hp := phase_comparison S ha hcover f hf hfinite htrans heq
  obtain ⟨σ,hσ,ho,ht,hcrg⟩ := CRGFinitePhaseWindowEndgame.complete_of_finite_phases_window
    hf hfinite htrans (phaseDenominator S) (phaseDenominator_positive S)
      (phasePolynomial S) (phasePolynomial_normalized S) hp
  exact ⟨σ,hσ,ho,ht,hcrg,hp⟩

#print axioms phaseDenominator_positive
#print axioms phasePolynomial_normalized
#print axioms phase_comparison
#print axioms proposition_5_1
end CRGPuiseuxProposition
