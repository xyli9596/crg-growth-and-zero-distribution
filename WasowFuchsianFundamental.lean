import WasowFuchsianODE
import WasowGaugeAssembly
import Mathlib.Analysis.Normed.Operator.Mul

/-! Actual solutions of the left and right matrix equations on a half-line,
constructed from a continuous coefficient rather than postulated. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Operator
namespace WasowFuchsianFundamental
variable {m : ℕ} {a : ℝ}
/-- The actual left action, bundled via finite-dimensional continuity. -/
def leftAction : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ]
    (Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ) :=
  LinearMap.toContinuousLinearMap.toLinearMap.comp (LinearMap.mul ℝ _)

/-- The actual right action, bundled via finite-dimensional continuity. -/
def rightAction : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ]
    (Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ) :=
  LinearMap.toContinuousLinearMap.toLinearMap.comp (LinearMap.mul ℝ _).flip

/-- Both matrix initial-value problems are solved on the entire half-line.
The inverse identities and growth estimates can then be proved from these
actual derivatives; they are not input assumptions. -/
theorem exists_matrix_solutions
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (hA : ContinuousOn A (Ici a)) :
    ∃ T S : ℝ → Matrix (Fin m) (Fin m) ℂ,
      T a = 1 ∧ S a = 1 ∧ ContinuousOn T (Ici a) ∧ ContinuousOn S (Ici a) ∧
      (∀ r : ℝ, a < r → HasDerivAt T (A r * T r) r) ∧
      (∀ r : ℝ, a < r → HasDerivAt S (-(S r * A r)) r) := by
  let L : ℝ → Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    fun r => leftAction (A r)
  let R : ℝ → Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    fun r => -rightAction (A r)
  have hL : ContinuousOn L (Ici a) :=
    leftAction.continuous_of_finiteDimensional.comp_continuousOn hA
  have hR : ContinuousOn R (Ici a) :=
    (rightAction.continuous_of_finiteDimensional.comp_continuousOn hA).neg
  obtain ⟨T, hT0, hTc, hTd⟩ := WasowFuchsianODE.exists_solution_Ici L hL 1
  obtain ⟨S, hS0, hSc, hSd⟩ := WasowFuchsianODE.exists_solution_Ici R hR 1
  exact ⟨T, S, hT0, hS0, hTc, hSc, hTd, hSd⟩

#print axioms exists_matrix_solutions
end WasowFuchsianFundamental
