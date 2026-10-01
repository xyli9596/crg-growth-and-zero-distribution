import WasowTruncation
import WasowMatrixPolynomial
import WasowAnalyticRemainder

/-! Actual residual estimates from an analytic coefficient function and a
formal gauge equation. Only the coefficient function has a convergent local
power series. The gauge and transformed series are truncated before evaluation;
no convergence of either infinite formal series is assumed. All matrix norms
here explicitly use the infinity operator norm. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology Matrix.Norms.Operator
open Filter Asymptotics Set MeasureTheory
namespace WasowActualTruncation
open WasowMatrixPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The polynomial-to-series map preserves subtraction also for the
noncommutative matrix coefficient ring. -/
theorem coe_sub_noncomm {R : Type*} [Ring R] (P Q : Polynomial R) :
    ((P - Q : Polynomial R) : PowerSeries R) = (P : PowerSeries R) - (Q : PowerSeries R) := by
  apply PowerSeries.ext
  intro k
  simp only [Polynomial.coeff_coe, map_sub, Polynomial.coeff_sub]

/-- A genuinely finite polynomial residual, also truncating the coefficient. -/
def polynomialDefect (A P B : PowerSeries (Matrix ι ι ℂ)) (q N : ℕ) :
    Polynomial (Matrix ι ι ℂ) :=
  PowerSeries.trunc N A * PowerSeries.trunc N P -
    PowerSeries.trunc N P * PowerSeries.trunc N B +
    Polynomial.X ^ (q + 1) * (PowerSeries.trunc N P).derivative

/-- Evaluation of the analytic Taylor polynomial is its actual partial sum. -/
theorem eval_trunc_eq_partialSum
    (p : FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ))
    (A : PowerSeries (Matrix ι ι ℂ))
    (hc : ∀ n, p.coeff n = PowerSeries.coeff n A) (N : ℕ) (z : ℂ) :
    eval (PowerSeries.trunc N A) z = p.partialSum N z := by
  change Polynomial.eval₂ (RingHom.id _) (algebraMap ℂ (Matrix ι ι ℂ) z)
    (PowerSeries.trunc N A) = _
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  unfold FormalMultilinearSeries.partialSum
  apply Finset.sum_congr rfl
  intro n hn
  have hz : (p n) (fun _ => z) = z ^ n • p.coeff n :=
    FormalMultilinearSeries.apply_eq_pow_smul_coeff
  rw [hz, hc]
  simp only [RingHom.id_apply, ← map_pow, Algebra.smul_def]
  exact (Algebra.commutes (z ^ n) (PowerSeries.coeff n A)).symm

/-- The actual finite polynomial residual inherits all low-order cancellations
from the complete formal gauge equation. -/
theorem polynomialDefect_coeff_zero (A P B : PowerSeries (Matrix ι ι ℂ)) (q N : ℕ)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P)) :
    ∀ k < N, (polynomialDefect A P B q N).coeff k = 0 := by
  intro k hk
  have ha : ∀ i < N, PowerSeries.coeff i
      ((PowerSeries.trunc N A : Polynomial (Matrix ι ι ℂ)) : PowerSeries (Matrix ι ι ℂ)) =
        PowerSeries.coeff i A := fun i hi => WasowTruncation.coeff_truncation A hi
  have hh := WasowTruncation.coeff_mul_congr_below hk ha
    (fun i _ => rfl (a := PowerSeries.coeff i
      ((PowerSeries.trunc N P : Polynomial (Matrix ι ι ℂ)) : PowerSeries (Matrix ι ι ℂ))))
  have hz := WasowTruncation.defect_coeff_zero A P B q N heq k hk
  rw [← Polynomial.coeff_coe]
  simpa only [polynomialDefect, Polynomial.coe_add, coe_sub_noncomm,
    Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, coe_derivative,
    map_add, map_sub, hh, WasowTruncation.defect] using hz

/-- A finite quotient polynomial witnesses the order of vanishing. -/
theorem polynomialDefect_divisible (A P B : PowerSeries (Matrix ι ι ℂ)) (q N : ℕ)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P)) :
    Polynomial.X ^ N ∣ polynomialDefect A P B q N :=
  Polynomial.X_pow_dvd_iff.mpr (polynomialDefect_coeff_zero A P B q N heq)

/-- The actual gauge defect, with the genuine complex derivative of the finite
polynomial gauge. It is a function, not a notation for an assumed error term. -/
def actualDefect (a : ℂ → Matrix ι ι ℂ)
    (P B : PowerSeries (Matrix ι ι ℂ)) (q N : ℕ) (z : ℂ) : Matrix ι ι ℂ :=
  a z * eval (PowerSeries.trunc N P) z -
    eval (PowerSeries.trunc N P) z * eval (PowerSeries.trunc N B) z +
    z ^ (q + 1) • deriv (eval (PowerSeries.trunc N P)) z

/-- Exact separation of the analytic Taylor remainder and a finite polynomial
whose low-order coefficients have already been proved to vanish. -/
theorem actualDefect_eq (a : ℂ → Matrix ι ι ℂ)
    (A P B : PowerSeries (Matrix ι ι ℂ)) (q N : ℕ) (z : ℂ) :
    actualDefect a P B q N z =
      (a z - eval (PowerSeries.trunc N A) z) * eval (PowerSeries.trunc N P) z +
        eval (polynomialDefect A P B q N) z := by
  unfold actualDefect polynomialDefect
  have hd : deriv (eval (PowerSeries.trunc N P)) z =
      eval (PowerSeries.trunc N P).derivative z :=
    (hasDerivAt_eval (PowerSeries.trunc N P) z).deriv
  rw [hd]
  rw [eval_add, eval_sub, eval_mul, eval_mul, eval_X_pow_mul, Matrix.sub_mul]
  abel

/-- Genuine order-`N` analytic residual for the actual finite gauge. The only
analytic expansion assumed is that of `a`; the formal `P` and `B` can diverge. -/
theorem actualDefect_isBigO
    {a : ℂ → Matrix ι ι ℂ} {p : FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ)}
    (ha : HasFPowerSeriesAt a p 0) (A P B : PowerSeries (Matrix ι ι ℂ))
    (hc : ∀ n, p.coeff n = PowerSeries.coeff n A) (q N : ℕ)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P)) :
    actualDefect a P B q N =O[𝓝 (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ N) := by
  have hA : (fun z : ℂ => a z - eval (PowerSeries.trunc N A) z) =O[𝓝 0]
      (fun z : ℂ => ‖z‖ ^ N) := by
    exact (ha.isBigO_sub_partialSum_pow N).congr_left
      (fun z => by rw [zero_add, eval_trunc_eq_partialSum p A hc]; rfl)
  have hP : eval (PowerSeries.trunc N P) =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) :=
    isBigO_const_of_tendsto ((continuous_eval _).tendsto 0) (by norm_num)
  have hproduct : (fun z : ℂ =>
      (a z - eval (PowerSeries.trunc N A) z) * eval (PowerSeries.trunc N P) z) =O[𝓝 0]
      (fun z : ℂ => ‖z‖ ^ N) := by
    simpa only [mul_one] using hA.mul hP
  have hfinite := isBigO_eval_of_X_pow_dvd (polynomialDefect A P B q N) N
    (polynomialDefect_divisible A P B q N heq)
  exact (hproduct.add hfinite).congr_left (fun z => (actualDefect_eq a A P B q N z).symm)

end WasowActualTruncation

#print axioms WasowActualTruncation.coe_sub_noncomm
#print axioms WasowActualTruncation.eval_trunc_eq_partialSum
#print axioms WasowActualTruncation.polynomialDefect_coeff_zero
#print axioms WasowActualTruncation.polynomialDefect_divisible
#print axioms WasowActualTruncation.actualDefect_eq
#print axioms WasowActualTruncation.actualDefect_isBigO
