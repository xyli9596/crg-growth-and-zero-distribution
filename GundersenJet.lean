import GundersenAngles
import Mathlib.Analysis.Calculus.LogDeriv

/-! Passing from consecutive logarithmic derivatives to arbitrary finite jets.
The identically-zero derivative case is included explicitly. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GundersenJet
open CRGNormalFormGoal GundersenAngles

/-- Consecutive quotients telescope at a nonzero intermediate derivative. -/
theorem quotient_step {f : ℂ → ℂ} {k : ℕ} {z : ℂ}
    (hk : iteratedDeriv k f z ≠ 0) :
    iteratedDeriv (k+1) f z / f z =
      logDeriv (iteratedDeriv k f) z * (iteratedDeriv k f z / f z) := by
  rw [iteratedDeriv_succ, logDeriv_apply]
  field_simp

/-- Sharp first-derivative estimates for the successive derivatives imply the
sharp k-th quotient estimate. If a derivative vanishes identically then all
following quotients vanish, and no nonzero premise is falsely imposed. -/
theorem ae_iterated_quotient_bound {f : ℂ → ℂ} {ρ δ : ℝ}
    (hnz : ∀ᵐ θ : ℝ, ∀ᶠ r : ℝ in atTop, f (ray θ r) ≠ 0)
    (hfirst : ∀ j : ℕ, (∃ z : ℂ, iteratedDeriv j f z ≠ 0) →
      ∀ᵐ θ : ℝ, ∀ᶠ r : ℝ in atTop,
        iteratedDeriv j f (ray θ r) ≠ 0 ∧
        ‖logDeriv (iteratedDeriv j f) (ray θ r)‖ ≤ r^(ρ-1+δ)) :
    ∀ k : ℕ, ∀ᵐ θ : ℝ, ∀ᶠ r : ℝ in atTop,
      ‖iteratedDeriv k f (ray θ r) / f (ray θ r)‖ ≤ r^((k:ℝ)*(ρ-1+δ)) := by
  intro k
  induction k with
  | zero =>
    filter_upwards [hnz] with θ hθ
    filter_upwards [hθ] with r hr
    simp [iteratedDeriv_zero, hr]
  | succ k ih =>
    by_cases hk : ∃ z : ℂ, iteratedDeriv k f z ≠ 0
    · filter_upwards [ih, hfirst k hk] with θ hθ hθk
      filter_upwards [hθ, hθk, eventually_gt_atTop (0:ℝ)] with r hr hkr hr0
      rw [quotient_step hkr.1, norm_mul]
      calc
        _ ≤ r^(ρ-1+δ)*r^((k:ℝ)*(ρ-1+δ)) :=
          mul_le_mul hkr.2 hr (norm_nonneg _) (Real.rpow_pos_of_pos hr0 _).le
        _ = _ := by
          rw [← Real.rpow_add hr0]
          congr 1
          push_cast
          ring
    · have he : iteratedDeriv k f = 0 := by
        ext z
        exact Classical.not_not.mp (fun hz => hk ⟨z,hz⟩)
      filter_upwards [] with θ
      filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr0
      rw [iteratedDeriv_succ, he]
      simpa using (Real.rpow_pos_of_pos hr0 (((k+1:ℕ):ℝ)*(ρ-1+δ))).le

/-- A finite number of eventual jet estimates has one common tail. -/
theorem ae_finite_jet_bound {f : ℂ → ℂ} {ρ δ : ℝ} (n : ℕ)
    (hk : ∀ k : ℕ, ∀ᵐ θ : ℝ, ∀ᶠ r : ℝ in atTop,
      ‖iteratedDeriv k f (ray θ r) / f (ray θ r)‖ ≤ r^((k:ℝ)*(ρ-1+δ))) :
    ∀ᵐ θ : ℝ, RayDerivativeBound f ρ n δ θ := by
  filter_upwards [ae_all_iff.mpr hk] with θ hθ
  have he : ∀ᶠ r : ℝ in atTop, ∀ k : Fin (n+1),
      ‖iteratedDeriv k.val f (ray θ r) / f (ray θ r)‖ ≤ r^((k.val:ℝ)*(ρ-1+δ)) := by
    rw [Filter.eventually_all]
    intro k
    exact hθ k.val
  filter_upwards [he] with r hr
  intro k _ hkn
  exact hr ⟨k, by omega⟩

#print axioms quotient_step
#print axioms ae_iterated_quotient_bound
#print axioms ae_finite_jet_bound
end GundersenJet
