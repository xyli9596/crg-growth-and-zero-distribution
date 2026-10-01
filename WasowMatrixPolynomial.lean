import WasowPowerSeries
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Polynomial.Div

/-! Evaluation of actual finite matrix polynomials at complex scalar arguments.
The argument is mapped into the center of the matrix ring, so multiplication
is genuinely preserved even though the coefficient matrices need not commute.
The analytic estimates explicitly use the matrix infinity operator norm,
whose genuine normed-ring instance validates multiplication estimates. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology Matrix.Norms.Operator
open Filter Asymptotics
namespace WasowMatrixPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scalar evaluation as a ring homomorphism into the noncommutative matrix ring. -/
def evaluation (z : ℂ) : Polynomial (Matrix ι ι ℂ) →+* Matrix ι ι ℂ :=
  Polynomial.eval₂RingHom' (RingHom.id _) (algebraMap ℂ (Matrix ι ι ℂ) z)
    (fun M => (Algebra.commutes z M).symm)

def eval (P : Polynomial (Matrix ι ι ℂ)) (z : ℂ) : Matrix ι ι ℂ := evaluation z P

@[simp] theorem eval_add (P Q : Polynomial (Matrix ι ι ℂ)) (z : ℂ) :
    eval (P + Q) z = eval P z + eval Q z := (evaluation z).map_add P Q

@[simp] theorem eval_sub (P Q : Polynomial (Matrix ι ι ℂ)) (z : ℂ) :
    eval (P - Q) z = eval P z - eval Q z := (evaluation z).map_sub P Q

@[simp] theorem eval_mul (P Q : Polynomial (Matrix ι ι ℂ)) (z : ℂ) :
    eval (P * Q) z = eval P z * eval Q z := (evaluation z).map_mul P Q

@[simp] theorem eval_X (z : ℂ) :
    eval (Polynomial.X : Polynomial (Matrix ι ι ℂ)) z = z • 1 := by
  simp [eval, evaluation, Polynomial.eval₂RingHom'_apply, Algebra.algebraMap_eq_smul_one]

@[simp] theorem eval_C (M : Matrix ι ι ℂ) (z : ℂ) : eval (Polynomial.C M) z = M := by
  change Polynomial.eval₂ (RingHom.id _) (algebraMap ℂ (Matrix ι ι ℂ) z) (Polynomial.C M) = M
  simp

theorem eval_eq_sum (P : Polynomial (Matrix ι ι ℂ)) (z : ℂ) :
    eval P z = ∑ n ∈ P.support, z ^ n • P.coeff n := by
  change Polynomial.eval₂ (RingHom.id _) (algebraMap ℂ (Matrix ι ι ℂ) z) P = _
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [RingHom.id_apply, ← map_pow, Algebra.smul_def]
  exact (Algebra.commutes (z ^ n) (P.coeff n)).symm

/-- A central monomial factor evaluates to the corresponding scalar power. -/
theorem eval_X_pow_mul (P : Polynomial (Matrix ι ι ℂ)) (N : ℕ) (z : ℂ) :
    eval (Polynomial.X ^ N * P) z = z ^ N • eval P z := by
  rw [eval_mul]
  change evaluation z (Polynomial.X ^ N) * eval P z = _
  rw [map_pow]
  change eval Polynomial.X z ^ N * eval P z = _
  rw [eval_X, smul_pow, one_pow, Matrix.smul_mul, Matrix.one_mul]

/-- Polynomial evaluation is continuous in the actual complex argument. -/
theorem continuous_eval (P : Polynomial (Matrix ι ι ℂ)) : Continuous (eval P) := by
  change Continuous (fun z => eval P z)
  simp_rw [eval_eq_sum]
  fun_prop

/-- The noncommutative polynomial derivative agrees with the coefficientwise
matrix power-series derivative used in the formal gauge equation. -/
theorem coe_derivative (P : Polynomial (Matrix ι ι ℂ)) :
    (P.derivative : PowerSeries (Matrix ι ι ℂ)) =
      WasowPowerSeries.derivative (P : PowerSeries (Matrix ι ι ℂ)) := by
  apply PowerSeries.ext
  intro n
  rw [Polynomial.coeff_coe, Polynomial.coeff_derivative,
    WasowPowerSeries.coeff_derivative, Polynomial.coeff_coe]
  rw [← Nat.cast_add_one]
  have hcast (k : ℕ) : (k : Matrix ι ι ℂ) = (k : ℂ) • 1 := by
    rw [← Algebra.algebraMap_eq_smul_one, map_natCast]
  rw [hcast, Matrix.mul_smul, Matrix.mul_one]

/-- Derivative evaluation is the actual finite termwise derivative sum. -/
theorem eval_derivative_eq_sum (P : Polynomial (Matrix ι ι ℂ)) (z : ℂ) :
    eval P.derivative z =
      ∑ n ∈ P.support, ((n : ℂ) * z ^ (n - 1)) • P.coeff n := by
  rw [Polynomial.derivative_apply, Polynomial.sum_def]
  change evaluation z (∑ n ∈ P.support, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  change eval (Polynomial.C (P.coeff n * (n : Matrix ι ι ℂ)) * Polynomial.X ^ (n - 1)) z = _
  rw [eval_mul, eval_C]
  have hpow : eval (Polynomial.X ^ (n - 1)) z = z ^ (n - 1) • (1 : Matrix ι ι ℂ) := by
    change evaluation z (Polynomial.X ^ (n - 1)) = _
    rw [map_pow]
    change eval Polynomial.X z ^ (n - 1) = _
    rw [eval_X, smul_pow, one_pow]
  rw [hpow, Matrix.mul_smul, Matrix.mul_one]
  have hcast : (n : Matrix ι ι ℂ) = (n : ℂ) • 1 := by
    rw [← Algebra.algebraMap_eq_smul_one, map_natCast]
  rw [hcast, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]

/-- Finite polynomial differentiation is an actual complex derivative. -/
theorem hasDerivAt_eval (P : Polynomial (Matrix ι ι ℂ)) (z : ℂ) :
    HasDerivAt (eval P) (eval P.derivative z) z := by
  rw [eval_derivative_eq_sum]
  change HasDerivAt (fun z => eval P z) _ z
  simp_rw [eval_eq_sum]
  exact HasDerivAt.fun_sum (fun n _ => (hasDerivAt_pow n z).smul_const (P.coeff n))

/-- A scalar factor `X^N` gives an actual local norm estimate of that order. -/
theorem isBigO_eval_of_X_pow_dvd (P : Polynomial (Matrix ι ι ℂ)) (N : ℕ)
    (hP : Polynomial.X ^ N ∣ P) :
    eval P =O[𝓝 (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ N) := by
  obtain ⟨Q, rfl⟩ := hP
  have hQ : eval Q =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) :=
    isBigO_const_of_tendsto (continuous_eval Q).continuousAt (by norm_num)
  have hpow : (fun z : ℂ => z ^ N) =O[𝓝 0] (fun z : ℂ => ‖z‖ ^ N) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with z
    simp
  have hh : (fun z : ℂ => z ^ N • eval Q z) =O[𝓝 0] (fun z : ℂ => ‖z‖ ^ N) := by
    simpa only [smul_eq_mul, mul_one] using hpow.smul hQ
  apply hh.congr_left
  intro z
  rw [eval_mul]
  change _ = evaluation z (Polynomial.X ^ N) * eval Q z
  rw [map_pow]
  change _ = eval Polynomial.X z ^ N * eval Q z
  rw [eval_X, smul_pow, one_pow, Matrix.smul_mul, Matrix.one_mul]

end WasowMatrixPolynomial
#print axioms WasowMatrixPolynomial.eval_add
#print axioms WasowMatrixPolynomial.eval_sub
#print axioms WasowMatrixPolynomial.eval_mul
#print axioms WasowMatrixPolynomial.eval_X
#print axioms WasowMatrixPolynomial.eval_C
#print axioms WasowMatrixPolynomial.eval_eq_sum
#print axioms WasowMatrixPolynomial.continuous_eval
#print axioms WasowMatrixPolynomial.coe_derivative
#print axioms WasowMatrixPolynomial.eval_derivative_eq_sum
#print axioms WasowMatrixPolynomial.hasDerivAt_eval
#print axioms WasowMatrixPolynomial.isBigO_eval_of_X_pow_dvd

#print axioms WasowMatrixPolynomial.eval_X_pow_mul
