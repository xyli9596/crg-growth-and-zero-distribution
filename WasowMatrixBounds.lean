import NormalFormGoal
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Matrix.Normed

/-!
Tail bounds for matrices converging to the identity.  Matrix inversion is the
actual nonsingular inverse.  The convergence hypothesis supplies eventual
nonsingularity as well as a common bound on the matrix and its inverse.
The norm estimate is proved for the entrywise supremum norm and does
not assume that this matrix norm is submultiplicative.
-/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators
open scoped Matrix.Norms.Elementwise

namespace WasowMatrixBounds

theorem mulVec_norm_le {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ) :
    ‖M.mulVec x‖ ≤ (m : ℝ) * ‖M‖ * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    ‖M.mulVec x i‖ = ‖∑ j, M i j * x j‖ := rfl
    _ ≤ ∑ j, ‖M i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, ‖M‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul
        ((norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i))
        (norm_le_pi_norm x j) (norm_nonneg _) (norm_nonneg _)
    _ = (m : ℝ) * ‖M‖ * ‖x‖ := by simp [mul_assoc]

theorem tendsto_inv_of_tendsto_one {α : Type*} {m : ℕ} {l : Filter α}
    {U : α → Matrix (Fin m) (Fin m) ℂ}
    (hU : Tendsto U l (𝓝 1)) :
    Tendsto (fun r => (U r)⁻¹) l (𝓝 1) := by
  have hinv : ContinuousAt (Inv.inv : Matrix (Fin m) (Fin m) ℂ → _) 1 :=
    continuousAt_matrix_inv 1 (by
      rw [Matrix.det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero)
  simpa [Function.comp_def] using hinv.tendsto.comp hU

theorem eventually_det_ne_zero {α : Type*} {m : ℕ} {l : Filter α}
    {U : α → Matrix (Fin m) (Fin m) ℂ}
    (hU : Tendsto U l (𝓝 1)) :
    ∀ᶠ r in l, (U r).det ≠ 0 := by
  have hdet : Tendsto (fun r => (U r).det) l (𝓝 1) := by
    simpa [Function.comp_def] using continuous_id.matrix_det.continuousAt.tendsto.comp hU
  exact hdet.eventually_ne one_ne_zero

theorem eventually_inverse_identities {α : Type*} {m : ℕ} {l : Filter α}
    {U : α → Matrix (Fin m) (Fin m) ℂ}
    (hU : Tendsto U l (𝓝 1)) :
    ∀ᶠ r in l, (U r)⁻¹ * U r = 1 ∧ U r * (U r)⁻¹ = 1 := by
  filter_upwards [eventually_det_ne_zero hU] with r hr
  exact ⟨Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hr),
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hr)⟩

/-- A single constant controls both operators on one common tail. -/
theorem eventually_uniform_mulVec_bounds {α : Type*} {m : ℕ} {l : Filter α}
    {U : α → Matrix (Fin m) (Fin m) ℂ}
    (hU : Tendsto U l (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in l,
      (U r)⁻¹ * U r = 1 ∧ U r * (U r)⁻¹ = 1 ∧
      (∀ x : Fin m → ℂ, ‖(U r).mulVec x‖ ≤ C * ‖x‖) ∧
      (∀ x : Fin m → ℂ, ‖((U r)⁻¹).mulVec x‖ ≤ C * ‖x‖) := by
  let B : ℝ := ‖(1 : Matrix (Fin m) (Fin m) ℂ)‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hUb : ∀ᶠ r in l, ‖U r‖ < B := hU.norm.eventually (gt_mem_nhds (by
    dsimp [B]; linarith))
  have hVb : ∀ᶠ r in l, ‖(U r)⁻¹‖ < B :=
    (tendsto_inv_of_tendsto_one hU).norm.eventually (gt_mem_nhds (by
      dsimp [B]; linarith))
  refine ⟨((m : ℝ) + 1) * B, mul_pos (by positivity) hB, ?_⟩
  filter_upwards [eventually_inverse_identities hU, hUb, hVb] with r hr hUr hVr
  refine ⟨hr.1, hr.2, ?_, ?_⟩
  · intro x
    refine (mulVec_norm_le (U r) x).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    exact mul_le_mul (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)
      hUr.le (norm_nonneg _) (by positivity)
  · intro x
    refine (mulVec_norm_le ((U r)⁻¹) x).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    exact mul_le_mul (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)
      hVr.le (norm_nonneg _) (by positivity)

end WasowMatrixBounds

#print axioms WasowMatrixBounds.mulVec_norm_le
#print axioms WasowMatrixBounds.tendsto_inv_of_tendsto_one
#print axioms WasowMatrixBounds.eventually_det_ne_zero
#print axioms WasowMatrixBounds.eventually_inverse_identities
#print axioms WasowMatrixBounds.eventually_uniform_mulVec_bounds
