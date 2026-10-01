import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-! Noncommutative matrix power series for the formal gauge equation.
The derivative is defined by its actual coefficients and is identified with
mathlib's scalar formal derivative in every matrix entry. Invertibility comes
from the unit constant coefficient, with explicit two-sided formal inverses. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowPowerSeries
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extract one scalar power series from a matrix-coefficient power series. -/
def entry (F : PowerSeries (Matrix ι ι ℂ)) (i j : ι) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => (PowerSeries.coeff n F) i j)

/-- The coefficientwise formal derivative in the noncommutative matrix ring. -/
def derivative (F : PowerSeries (Matrix ι ι ℂ)) : PowerSeries (Matrix ι ι ℂ) :=
  PowerSeries.mk (fun n => ((n+1 : ℕ) : ℂ) • PowerSeries.coeff (n+1) F)

@[simp] theorem coeff_entry (F : PowerSeries (Matrix ι ι ℂ)) (i j : ι) (n : ℕ) :
    PowerSeries.coeff n (entry F i j) = (PowerSeries.coeff n F) i j :=
  PowerSeries.coeff_mk _ _

@[simp] theorem coeff_derivative (F : PowerSeries (Matrix ι ι ℂ)) (n : ℕ) :
    PowerSeries.coeff n (derivative F) = ((n+1 : ℕ) : ℂ) • PowerSeries.coeff (n+1) F :=
  PowerSeries.coeff_mk _ _

/-- The new matrix derivative is exactly the established scalar derivative in
all entries; it is not a hypothesis about formal differentiation. -/
theorem entry_derivative (F : PowerSeries (Matrix ι ι ℂ)) (i j : ι) :
    entry (derivative F) i j = PowerSeries.derivative ℂ (entry F i j) := by
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_derivative, Matrix.smul_apply, mul_comm]

theorem coeff_mul_range_left {R : Type*} [Semiring R]
    (F G : PowerSeries R) (k : ℕ) :
    PowerSeries.coeff k (F*G) = ∑ i ∈ Finset.range (k+1),
      PowerSeries.coeff i F * PowerSeries.coeff (k-i) G := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _

theorem coeff_mul_range_right {R : Type*} [Semiring R]
    (F G : PowerSeries R) (k : ℕ) :
    PowerSeries.coeff k (F*G) = ∑ i ∈ Finset.range (k+1),
      PowerSeries.coeff (k-i) F * PowerSeries.coeff i G := by
  rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _

/-- The rank convention is `q = q_book + 1`. Changing from `z` to `t = 1/z`
turns Wasow's equation into `AP-PB = -t^(q+1) P_t'`. -/
theorem coeff_rank_derivative (F : PowerSeries (Matrix ι ι ℂ)) (q k : ℕ) :
    PowerSeries.coeff k (-((PowerSeries.X : PowerSeries (Matrix ι ι ℂ)) ^ (q+1) * derivative F)) =
      -(if q < k then ((k-q : ℕ) : ℂ) • PowerSeries.coeff (k-q) F else 0) := by
  rw [map_neg, PowerSeries.coeff_X_pow_mul']
  by_cases h : q < k
  · rw [if_pos (by omega), if_pos h, coeff_derivative]
    have heq : k - (q+1) + 1 = k-q := by omega
    rw [heq]
  · rw [if_neg (by omega), if_neg h]

/-- Coefficient identities imply the actual noncommutative formal equation. -/
theorem equation_of_coefficients (A P B : ℕ → Matrix ι ι ℂ) (q : ℕ)
    (h : ∀ k, (∑ i ∈ Finset.range (k+1), (A (k-i) * P i - P i * B (k-i))) =
      -(if q < k then ((k-q : ℕ) : ℂ) • P (k-q) else 0)) :
    PowerSeries.mk A * PowerSeries.mk P - PowerSeries.mk P * PowerSeries.mk B =
      -((PowerSeries.X : PowerSeries (Matrix ι ι ℂ)) ^ (q+1) * derivative (PowerSeries.mk P)) := by
  apply PowerSeries.ext
  intro k
  rw [map_sub, coeff_mul_range_right, coeff_mul_range_left, coeff_rank_derivative]
  simpa only [PowerSeries.coeff_mk, ← Finset.sum_sub_distrib] using h k

/-- A matrix series with identity constant term is a genuine unit. -/
theorem isUnit_of_constant_one (P : ℕ → Matrix ι ι ℂ) (hP : P 0 = 1) :
    IsUnit (PowerSeries.mk P) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hP]
  exact isUnit_one

/-- An explicit inverse series has both inverse identities. -/
theorem exists_inverse_of_constant_one (P : ℕ → Matrix ι ι ℂ) (hP : P 0 = 1) :
    ∃ S : PowerSeries (Matrix ι ι ℂ),
      S * PowerSeries.mk P = 1 ∧ PowerSeries.mk P * S = 1 := by
  refine ⟨PowerSeries.invOfUnit (PowerSeries.mk P) 1, ?_, ?_⟩
  · apply PowerSeries.invOfUnit_mul
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hP]
    rfl
  · apply PowerSeries.mul_invOfUnit
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hP]
    rfl

#print axioms coeff_entry
#print axioms coeff_derivative
#print axioms entry_derivative
#print axioms coeff_mul_range_left
#print axioms coeff_mul_range_right
#print axioms coeff_rank_derivative
#print axioms equation_of_coefficients
#print axioms isUnit_of_constant_one
#print axioms exists_inverse_of_constant_one
end WasowPowerSeries
