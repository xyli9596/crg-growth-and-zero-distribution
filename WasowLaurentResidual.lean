import WasowLaurentGauge
import WasowClearedResidual

/-! The differential equation of a genuine Laurent matrix gauge implies the
power-cleared equation used by the actual finite-truncation estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace WasowLaurentResidual
open WasowLaurentGauge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def monomial (k : ℤ) : L := HahnSeries.single k 1

@[simp] theorem monomial_mul (j k : ℤ) : monomial j * monomial k = monomial (j+k) := by
  simp [monomial]
@[simp] theorem monomial_zero : monomial 0 = 1 := rfl

/-- Complete matrix series embed faithfully into Laurent matrices. -/
theorem toLaurent_injective : Function.Injective (toLaurent (ι := ι)) := by
  intro F G heq
  apply PowerSeries.ext
  intro n
  apply Matrix.ext
  intro i j
  have he := congrArg (fun M : Matrix ι ι L => (M i j).coeff (n : ℤ)) heq
  simpa only [toLaurent_apply, PowerSeries.coeff_coe,
    if_neg (show ¬(n : ℤ) < 0 from Int.not_lt.mpr (Int.natCast_nonneg n)),
    Int.natAbs_natCast, WasowPowerSeries.coeff_entry] using he

/-- Complex scalar multiplication is actual multiplication by the constant
Laurent scalar, not a new coefficient action. -/
theorem toLaurent_smul (c : ℂ) (P : PowerSeries (Matrix ι ι ℂ)) :
    toLaurent (c • P) = (HahnSeries.C c : L) • toLaurent P := by
  apply Matrix.ext
  intro i j
  have he : WasowPowerSeries.entry (c • P) i j =
      PowerSeries.C c * WasowPowerSeries.entry P i j := by
    apply PowerSeries.ext
    intro n
    simp [WasowPowerSeries.coeff_entry, PowerSeries.coeff_C_mul, Matrix.smul_apply]
  simp only [toLaurent_apply, Matrix.smul_apply, smul_eq_mul]
  rw [he, map_mul, HahnSeries.ofPowerSeries_C]

omit [Fintype ι] [DecidableEq ι] in
/-- Exact derivative of a Laurent scalar pole times an entire formal matrix. -/
theorem derivative_monomial_smul (k : ℤ) (P : Matrix ι ι L) :
    matrixDerivative (monomial k • P) =
      (HahnSeries.single (k-1) (k : ℂ) : L) • P + monomial k • matrixDerivative P := by
  apply Matrix.ext
  intro i j
  exact derivative_monomial_mul k (P i j)

/-- Clearing coefficient and gauge poles yields the precise extra term
coming from the derivative of t^(-a). The cleared gauge need not start at I. -/
theorem equation_of_laurent (a h : ℕ) (hh : 0 < h)
    (A P B : PowerSeries (Matrix ι ι ℂ))
    (heq : GaugeEquation
      (monomial (-(h : ℤ)) • toLaurent A)
      (monomial (-(a : ℤ)) • toLaurent P)
      (monomial (-(h : ℤ)) • toLaurent B)) :
    WasowClearedResidual.Equation a h A P B := by
  unfold GaugeEquation at heq
  rw [derivative_monomial_smul] at heq
  have hprod (c d : L) (M N : Matrix ι ι L) :
      (c • M)*(d • N) = (c*d) • (M*N) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    simp_rw [mul_mul_mul_comm]
    exact (Finset.mul_sum _ _ _).symm
  rw [hprod, hprod] at heq
  have hc₁ : monomial ((a+h : ℕ) : ℤ) *
      (monomial (-(h : ℤ)) * monomial (-(a : ℤ))) = 1 := by simp [monomial_mul]
  have hc₂ : monomial ((a+h : ℕ) : ℤ) *
      (monomial (-(a : ℤ)) * monomial (-(h : ℤ))) = 1 := by
    rw [monomial_mul, monomial_mul]
    convert monomial_zero using 1
    congr 1
    push_cast
    ring
  have hc₃ : monomial ((a+h : ℕ) : ℤ) * monomial (-(a : ℤ)) = monomial (h : ℤ) := by
    simp [monomial_mul]
  have hc₄ : monomial ((a+h : ℕ) : ℤ) * HahnSeries.single (-(a : ℤ)-1) (-(a : ℤ) : ℂ) =
      -(HahnSeries.C (a : ℂ) * monomial ((h-1 : ℕ) : ℤ)) := by
    have hconst : HahnSeries.C (a : ℂ) * monomial ((h-1 : ℕ) : ℤ) =
        (HahnSeries.single ((h-1 : ℕ) : ℤ) (a : ℂ) : L) := by
      change HahnSeries.single 0 (a : ℂ) * HahnSeries.single _ 1 = _
      simp only [HahnSeries.single_mul_single, zero_add, mul_one]
    rw [hconst]
    change HahnSeries.single ((a+h : ℕ) : ℤ) 1 *
      HahnSeries.single (-(a : ℤ)-1) (-(a : ℤ) : ℂ) = _
    rw [HahnSeries.single_mul_single]
    have hh' : ((a+h : ℕ) : ℤ) + (-(a : ℤ)-1) = ((h-1 : ℕ) : ℤ) := by omega
    rw [hh']
    simp
  apply toLaurent_injective
  simp only [map_sub, map_mul, toLaurent_X_pow, toLaurent_derivative, toLaurent_smul]
  apply Matrix.ext
  intro i j
  have heij := congrArg (fun M : Matrix ι ι L => M i j) heq
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at heij
  have heij' := congrArg (fun x : L => monomial ((a+h : ℕ) : ℤ)*x) heij
  simp only [mul_sub, mul_add, ← mul_assoc, hc₁, hc₂, hc₃, one_mul] at heij'
  simp only [Int.cast_neg] at heij'
  rw [hc₄] at heij'
  have hmul (c : L) (M N : Matrix ι ι L) : (c • M)*N = c • (M*N) := by
    simpa using hprod c 1 M N
  rw [hmul, hmul, Matrix.one_mul, Matrix.one_mul]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simpa only [monomial, neg_mul (α := L), sub_eq_add_neg, mul_assoc, add_comm] using heij'

#print axioms monomial_mul
#print axioms monomial_zero
#print axioms toLaurent_injective
#print axioms toLaurent_smul
#print axioms derivative_monomial_smul
#print axioms equation_of_laurent
end WasowLaurentResidual
