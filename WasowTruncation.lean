import WasowPowerSeries
import Mathlib.RingTheory.PowerSeries.Trunc

/-! Finite polynomial truncations of a genuine formal matrix gauge.
The formal residual is proved divisible by the requested power, for every
truncation order. No convergence of the infinite gauge or transformed series
is assumed or concluded. Analytic realization requires a separate remainder
estimate for an actual analytic coefficient function. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowTruncation
open WasowPowerSeries

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiplication preserves agreement of all coefficients below a bound. -/
theorem coeff_mul_congr_below {R : Type*} [Semiring R]
    {F G F' G' : PowerSeries R} {N k : ℕ} (hk : k < N)
    (hF : ∀ i < N, PowerSeries.coeff i F = PowerSeries.coeff i F')
    (hG : ∀ i < N, PowerSeries.coeff i G = PowerSeries.coeff i G') :
    PowerSeries.coeff k (F*G) = PowerSeries.coeff k (F'*G') := by
  rw [coeff_mul_range_left, coeff_mul_range_left]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  rw [hF i (hik.trans_lt hk), hG (k-i) ((Nat.sub_le _ _).trans_lt hk)]

/-- The actual polynomial truncation agrees with the prescribed formal data. -/
theorem coeff_truncation {R : Type*} [Semiring R]
    (F : PowerSeries R) {N k : ℕ} (hk : k < N) :
    PowerSeries.coeff k ((PowerSeries.trunc N F : Polynomial R) : PowerSeries R) =
      PowerSeries.coeff k F := by
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hk]

/-- Positive-rank differentiation cannot bring an omitted coefficient below
the truncation order. This includes the zero coefficient at degree `q`. -/
theorem coeff_shifted_derivative_truncation
    (P : PowerSeries (Matrix ι ι ℂ)) (q : ℕ) {N k : ℕ} (hk : k < N) :
    PowerSeries.coeff k (PowerSeries.X ^ (q+1) *
      derivative ((PowerSeries.trunc N P : Polynomial (Matrix ι ι ℂ)) : PowerSeries (Matrix ι ι ℂ))) =
      PowerSeries.coeff k (PowerSeries.X ^ (q+1) * derivative P) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  split_ifs with hq
  · rw [coeff_derivative, coeff_derivative, coeff_truncation P (by omega)]
  · rfl

def defect (A P B : PowerSeries (Matrix ι ι ℂ)) (q N : ℕ) :
    PowerSeries (Matrix ι ι ℂ) :=
  let p : PowerSeries (Matrix ι ι ℂ) := PowerSeries.trunc N P
  let b : PowerSeries (Matrix ι ι ℂ) := PowerSeries.trunc N B
  A*p-p*b+PowerSeries.X^(q+1)*derivative p

/-- All coefficients of the finite-truncation residual below `N` vanish. -/
theorem defect_coeff_zero (A P B : PowerSeries (Matrix ι ι ℂ)) (q N : ℕ)
    (heq : A*P-P*B = -(PowerSeries.X^(q+1)*derivative P)) :
    ∀ k < N, PowerSeries.coeff k (defect A P B q N) = 0 := by
  intro k hk
  have hp : ∀ i < N, PowerSeries.coeff i
      ((PowerSeries.trunc N P : Polynomial (Matrix ι ι ℂ)) : PowerSeries (Matrix ι ι ℂ)) =
        PowerSeries.coeff i P := fun i hi => coeff_truncation P hi
  have hb : ∀ i < N, PowerSeries.coeff i
      ((PowerSeries.trunc N B : Polynomial (Matrix ι ι ℂ)) : PowerSeries (Matrix ι ι ℂ)) =
        PowerSeries.coeff i B := fun i hi => coeff_truncation B hi
  have hAP := coeff_mul_congr_below hk (fun _ _ => rfl (a := PowerSeries.coeff _ A)) hp
  have hPB := coeff_mul_congr_below hk hp hb
  have hh : A*P-P*B+PowerSeries.X^(q+1)*derivative P = 0 := by
    rw [heq, neg_add_cancel]
  have hfull := congrArg (PowerSeries.coeff k) hh
  simp only [map_add, map_sub, map_zero] at hfull
  simpa only [defect, map_add, map_sub, hAP, hPB,
    coeff_shifted_derivative_truncation P q hk] using hfull

/-- A genuine factorization of the residual by `X^N`, not just a notation
for an unspecified asymptotic error. -/
theorem defect_divisible (A P B : PowerSeries (Matrix ι ι ℂ)) (q N : ℕ)
    (heq : A*P-P*B = -(PowerSeries.X^(q+1)*derivative P)) :
    (PowerSeries.X : PowerSeries (Matrix ι ι ℂ)) ^ N ∣ defect A P B q N :=
  PowerSeries.X_pow_dvd_iff.mpr (defect_coeff_zero A P B q N heq)

/-- The finite gauge itself remains formally invertible at every positive
truncation order because its constant matrix is the identity. -/
theorem truncation_isUnit (P : PowerSeries (Matrix ι ι ℂ))
    (hP : PowerSeries.constantCoeff P = 1) {N : ℕ} (hN : 0 < N) :
    IsUnit (((PowerSeries.trunc N P : Polynomial (Matrix ι ι ℂ)) : PowerSeries (Matrix ι ι ℂ))) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_truncation P hN,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hP]
  exact isUnit_one

#print axioms coeff_mul_congr_below
#print axioms coeff_truncation
#print axioms coeff_shifted_derivative_truncation
#print axioms defect_coeff_zero
#print axioms defect_divisible
#print axioms truncation_isUnit
end WasowTruncation
