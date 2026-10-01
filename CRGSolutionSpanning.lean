import WasowFuchsianODE
import WasowGaugeAssembly
import WasowFundamental

/-! Every actual solution of a continuous linear system is a constant linear
combination of any genuine fundamental matrix. The coefficient vector is
constructed from one inverse matrix and equality follows from ODE uniqueness. -/
set_option autoImplicit false
noncomputable section
open Set Filter Matrix
open scoped Topology
namespace CRGSolutionSpanning
variable {m : ℕ}

theorem matrix_mulVec_hasDerivAt (Y Y' : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (c : Fin m → ℂ) {r : ℝ}
    (hY : ∀i j, HasDerivAt (fun t => Y t i j) (Y' r i j) r) :
    HasDerivAt (fun t => (Y t).mulVec c) ((Y' r).mulVec c) r := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply] using
    HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => (hY i j).mul_const (c j))

/-- The representation is proved for an arbitrary actual solution, with no
solution-representation hypothesis. The initial coefficient is explicit. -/
theorem solution_eq_fundamental_mulVec
    (A Y : ℝ → Matrix (Fin m) (Fin m) ℂ) (x : ℝ → Fin m → ℂ)
    (a b : ℝ) (hab : a < b)
    (hA : ContinuousOn A (Ioi a))
    (hY : ∀r>a, ∀i j, HasDerivAt (fun t => Y t i j) ((A r * Y r) i j) r)
    (hx : ∀r>a, HasDerivAt x ((A r).mulVec (x r)) r)
    (hdet : (Y b).det ≠ 0) :
    ∀r≥b, x r = (Y r).mulVec ((Y b)⁻¹.mulVec (x b)) := by
  let c := (Y b)⁻¹.mulVec (x b)
  have hinit : x b = (Y b).mulVec c := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  have hYc (r : ℝ) (hr : a < r) :
      HasDerivAt (fun t => (Y t).mulVec c) ((A r).mulVec ((Y r).mulVec c)) r := by
    simpa only [Matrix.mulVec_mulVec] using
      matrix_mulVec_hasDerivAt Y (fun t => A t * Y t) c (hY r hr)
  intro r hr
  have hi : Icc b r ⊆ Ioi a := fun t ht => hab.trans_le ht.1
  have hAc : ContinuousOn (fun t => (WasowGaugeAssembly.toOperator (A t)).restrictScalars ℝ)
      (Icc b r) := by
    apply (ContinuousLinearMap.continuous_restrictScalars ℝ).comp_continuousOn
    exact WasowGaugeAssembly.continuous_toOperator.comp_continuousOn (hA.mono hi)
  exact WasowFuchsianODE.solution_eqOn_Icc hr
    (fun t => (WasowGaugeAssembly.toOperator (A t)).restrictScalars ℝ) hAc x
    (fun t => (Y t).mulVec c) (fun t ht => hx t (hi ht))
    (fun t ht => hYc t (hi ht)) hinit ⟨hr,le_rfl⟩

/-- A nonzero solution has a nonzero constant coefficient vector. -/
theorem exists_nonzero_coefficients
    (A Y : ℝ → Matrix (Fin m) (Fin m) ℂ) (x : ℝ → Fin m → ℂ)
    (a b : ℝ) (hab : a < b)
    (hA : ContinuousOn A (Ioi a))
    (hY : ∀r>a, ∀i j, HasDerivAt (fun t => Y t i j) ((A r * Y r) i j) r)
    (hx : ∀r>a, HasDerivAt x ((A r).mulVec (x r)) r)
    (hdet : (Y b).det ≠ 0) (hxb : x b ≠ 0) :
    ∃c : Fin m → ℂ, c≠0 ∧ ∀r≥b, x r = (Y r).mulVec c := by
  refine ⟨(Y b)⁻¹.mulVec (x b), ?_,
    solution_eq_fundamental_mulVec A Y x a b hab hA hY hx hdet⟩
  intro hc
  have he := solution_eq_fundamental_mulVec A Y x a b hab hA hY hx hdet b le_rfl
  rw [hc, Matrix.mulVec_zero] at he
  exact hxb he

#print axioms matrix_mulVec_hasDerivAt
#print axioms solution_eq_fundamental_mulVec
#print axioms exists_nonzero_coefficients
end CRGSolutionSpanning
