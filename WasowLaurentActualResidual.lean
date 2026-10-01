import WasowClearedResidual
import WasowActualTail
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! Actual finite Laurent gauges, their true derivatives, and exact residual
identification with the proved high-order power-cleared defect. -/
set_option autoImplicit false
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Filter Asymptotics
namespace WasowLaurentActualResidual
open WasowMatrixPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Series := PowerSeries (Matrix ι ι ℂ)

def finiteGauge (a N : ℕ) (P : Series (ι := ι)) (z : ℂ) : Matrix ι ι ℂ :=
  z ^ (-(a : ℤ)) • eval (PowerSeries.trunc N P) z

def gaugeDerivative (a N : ℕ) (P : Series (ι := ι)) (z : ℂ) : Matrix ι ι ℂ :=
  z ^ (-(a : ℤ)) • eval (PowerSeries.trunc N P).derivative z +
    ((-(a : ℂ)) * z ^ (-(a : ℤ) - 1)) • eval (PowerSeries.trunc N P) z

theorem finiteGauge_hasDerivAt (a N : ℕ) (P : Series (ι := ι))
    {z : ℂ} (hz : z ≠ 0) : HasDerivAt (finiteGauge a N P) (gaugeDerivative a N P z) z := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hp := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hasDerivAt_eval (PowerSeries.trunc N P) z) i) j
  simpa only [finiteGauge, gaugeDerivative, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul, Int.cast_neg, Int.cast_natCast, add_comm] using
    (hasDerivAt_zpow (-(a : ℤ)) z (Or.inl hz)).fun_mul hp

def rawDefect (a h N : ℕ) (c : ℂ → Matrix ι ι ℂ)
    (P B : Series (ι := ι)) (z : ℂ) : Matrix ι ι ℂ :=
  (z ^ (-(h : ℤ)) • c z) * finiteGauge a N P z -
    finiteGauge a N P z * (z ^ (-(h : ℤ)) • eval (PowerSeries.trunc N B) z) -
    deriv (finiteGauge a N P) z

/-- Exact pole loss in the raw differential defect, including the derivative
of the Laurent monomial. This is an identity, not an assumed error estimate. -/
theorem rawDefect_eq (a h N : ℕ) (hh : 0 < h)
    (c : ℂ → Matrix ι ι ℂ) (P B : Series (ι := ι)) {z : ℂ} (hz : z ≠ 0) :
    rawDefect a h N c P B z = z ^ (-((a+h : ℕ) : ℤ)) •
      WasowClearedResidual.actualDefect a h N c P B z := by
  have hg : deriv (finiteGauge a N P) z = gaugeDerivative a N P z :=
    (finiteGauge_hasDerivAt a N P hz).deriv
  have hp : deriv (eval (PowerSeries.trunc N P)) z = eval (PowerSeries.trunc N P).derivative z :=
    (hasDerivAt_eval _ z).deriv
  have h₁ : z ^ (-(h : ℤ)) * z ^ (-(a : ℤ)) = z ^ (-((a+h : ℕ) : ℤ)) := by
    rw [← zpow_add₀ hz]
    congr 1
    omega
  have h₂ : z ^ (-((a+h : ℕ) : ℤ)) * z ^ h = z ^ (-(a : ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ hz]
    congr 1
    omega
  have h₃ : z ^ (-((a+h : ℕ) : ℤ)) * z ^ (h-1) = z ^ (-(a : ℤ)-1) := by
    rw [← zpow_natCast, ← zpow_add₀ hz]
    congr 1
    omega
  unfold rawDefect
  rw [hg]
  unfold finiteGauge gaugeDerivative WasowClearedResidual.actualDefect
  rw [hp]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, smul_sub]
  rw [h₁, mul_comm (z ^ (-(a : ℤ))) (z ^ (-(h : ℤ))), h₁, h₂]
  have h₄ : z ^ (-((a+h : ℕ) : ℤ)) * ((a : ℂ) * z ^ (h-1)) =
      (a : ℂ) * z ^ (-(a : ℤ)-1) := by rw [mul_left_comm, h₃]
  rw [h₄, neg_mul, neg_smul]
  abel

/-- The cleared residual is continuous in an actual neighborhood of zero. -/
theorem clearedDefect_continuousAt (a h N : ℕ) {c : ℂ → Matrix ι ι ℂ}
    {z : ℂ} (hc : ContinuousAt c z) (P B : Series (ι := ι)) :
    ContinuousAt (WasowClearedResidual.actualDefect a h N c P B) z := by
  have hd : deriv (eval (PowerSeries.trunc N P)) = eval (PowerSeries.trunc N P).derivative := by
    funext w
    exact (hasDerivAt_eval _ w).deriv
  unfold WasowClearedResidual.actualDefect
  rw [hd]
  exact (((hc.mul (continuous_eval _).continuousAt).sub
    ((continuous_eval _).continuousAt.mul (continuous_eval _).continuousAt)).sub
      ((continuousAt_id.pow _).smul (continuous_eval _).continuousAt)).add
      ((continuousAt_const.mul (continuousAt_id.pow _)).smul (continuous_eval _).continuousAt)

#print axioms finiteGauge_hasDerivAt
#print axioms rawDefect_eq
#print axioms clearedDefect_continuousAt
end WasowLaurentActualResidual
