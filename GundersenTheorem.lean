import CRGGundersenDyadic
import GundersenOrigin
import GundersenDerivative
import GundersenJet
import GundersenTwoSided

/-! The specialized Gundersen input for the manuscript, proved for every
nonzero entire function of finite upper order. All orders of differentiation and
all positive exponent errors share one Lebesgue-null angular exceptional set. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GundersenTheorem
open CRGNormalFormGoal GundersenAngles

/-- Sharp first logarithmic derivative estimate on full ray tails, for an
arbitrary nonzero entire function, including a zero at the origin. -/
theorem ae_logDeriv_bound {f : ℂ → ℂ} {ρ δ : ℝ}
    (hf : Differentiable ℂ f) (hn : ∃ z, f z ≠ 0)
    (hρ : 0 ≤ ρ) (hδ : 0 < δ) (ho : CRGOrder.UpperOrder f ρ) :
    ∀ᵐ θ : ℝ, ∀ᶠ r : ℝ in atTop,
      f (ray θ r) ≠ 0 ∧ ‖logDeriv f (ray θ r)‖ ≤ r^(ρ-1+δ) := by
  obtain ⟨m, a, ha, g, hg, hg0, hgo, heq⟩ :=
    GundersenOrigin.exists_normalized_factor hf hn hρ ho
  have hh := CRGGundersenDyadic.ae_normalized_logDeriv_bound hg hg0 hρ
    (show 0 < δ/2 by linarith) hgo
  filter_upwards [hh] with θ hθ
  exact GundersenOrigin.ray_logDeriv_restore hg ha hρ hδ heq hθ

/-- The full finite-jet Gundersen estimate at one positive error. No derivative
nonvanishing or derivative-order hypothesis is assumed here. -/
theorem ae_finite_jet_bound {f : ℂ → ℂ} {ρ δ : ℝ}
    (hf : Differentiable ℂ f) (hn : ∃ z, f z ≠ 0)
    (hρ : 0 ≤ ρ) (hδ : 0 < δ) (ho : CRGOrder.UpperOrder f ρ) (n : ℕ) :
    ∀ᵐ θ : ℝ, RayDerivativeBound f ρ n δ θ := by
  apply GundersenJet.ae_finite_jet_bound n
  apply GundersenJet.ae_iterated_quotient_bound
  · filter_upwards [GundersenAngles.ae_nonzero_on_positive_ray hf hn] with θ hθ
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact hθ r hr
  · intro j hj
    exact ae_logDeriv_bound (GundersenDerivative.entire_iteratedDeriv hf j) hj hρ hδ
      (GundersenDerivative.upperOrder_iteratedDeriv hf hρ ho j)

/-- Both countable diagonalizations are performed: the same good angles work
for EVERY finite jet and EVERY positive exponent error. -/
theorem ae_all_jets_all_errors {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hn : ∃ z, f z ≠ 0)
    (hρ : 0 ≤ ρ) (ho : CRGOrder.UpperOrder f ρ) :
    ∀ᵐ θ : ℝ, ∀ n : ℕ, ∀ δ : ℝ, 0 < δ → RayDerivativeBound f ρ n δ θ := by
  rw [ae_all_iff]
  intro n
  exact GundersenAngles.simultaneous_errors
    (fun δ hδ => ae_finite_jet_bound hf hn hρ hδ ho n)

/-- The complete paper-facing ray input: sharp finite-jet quotients,
nonvanishing, and the two-sided logarithmic growth estimate. -/
theorem ae_ray_input {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hn : ∃ z, f z ≠ 0)
    (hρ : 0 ≤ ρ) (ho : CRGOrder.UpperOrder f ρ) :
    ∀ᵐ θ : ℝ,
      (∀ r : ℝ, 0 < r → f (ray θ r) ≠ 0) ∧
      (∀ n : ℕ, ∀ δ : ℝ, 0 < δ → RayDerivativeBound f ρ n δ θ) ∧
      (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ r : ℝ in atTop, |Real.log ‖f (ray θ r)‖| ≤ C*r^(ρ+δ)) := by
  filter_upwards [ae_all_jets_all_errors hf hn hρ ho,
    GundersenAngles.ae_nonzero_on_positive_ray hf hn] with θ hθ hnθ
  refine ⟨hnθ, hθ, fun δ hδ => ?_⟩
  apply GundersenTwoSided.ray_log_norm_power_bound hf (show 0 < ρ+δ by linarith)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact hnθ r hr
  · filter_upwards [hθ 1 δ hδ] with r hr
    simpa only [iteratedDeriv_one, Nat.cast_one, one_mul] using hr 1 le_rfl le_rfl

/-- One explicit null angular exceptional set realizes every quantifier in the
Gundersen input, including all positive errors and all finite derivative lists. -/
theorem exists_null_exceptional_set {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hn : ∃ z, f z ≠ 0)
    (hρ : 0 ≤ ρ) (ho : CRGOrder.UpperOrder f ρ) :
    ∃ E : Set ℝ, volume E = 0 ∧ ∀ θ : ℝ, θ ∉ E →
      (∀ r : ℝ, 0 < r → f (ray θ r) ≠ 0) ∧
      (∀ n : ℕ, ∀ δ : ℝ, 0 < δ → RayDerivativeBound f ρ n δ θ) ∧
      (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ r : ℝ in atTop, |Real.log ‖f (ray θ r)‖| ≤ C*r^(ρ+δ)) := by
  let P := fun θ : ℝ =>
      (∀ r : ℝ, 0 < r → f (ray θ r) ≠ 0) ∧
      (∀ n : ℕ, ∀ δ : ℝ, 0 < δ → RayDerivativeBound f ρ n δ θ) ∧
      (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ r : ℝ in atTop, |Real.log ‖f (ray θ r)‖| ≤ C*r^(ρ+δ))
  refine ⟨{θ | ¬P θ}, ?_, ?_⟩
  · exact ae_iff.mp (ae_ray_input hf hn hρ ho)
  · intro θ hθ
    exact Classical.not_not.mp hθ

#print axioms ae_logDeriv_bound
#print axioms ae_finite_jet_bound
#print axioms ae_all_jets_all_errors
#print axioms ae_ray_input
#print axioms exists_null_exceptional_set
end GundersenTheorem
