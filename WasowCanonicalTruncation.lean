import WasowGlobalFormalCanonical
import WasowLaurentClearing
import WasowMatrixPolynomial

/-! Finite truncation of the genuine canonical coefficient preserves its
entire fixed polynomial phase. Only the regular-singular series is truncated.
The phase polynomial below is a cleared finite representation with a proved
Laurent recovery identity, not a replacement phase chosen after truncation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace WasowCanonicalTruncation
open WasowLaurentGauge WasowLaurentPhase WasowLaurentClearing WasowLaurentTruncation
open WasowGlobalFormalCanonical WasowGlobalFormalRegular
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Laurent derivative of a polynomial phase has no nonnegative powers. -/
theorem phase_derivative_coeff_nonneg (F : Polynomial ℂ) (n : ℤ) (hn : 0 ≤ n) :
    (D (phaseLaurent F)).coeff n = 0 := by
  rw [derivative_coeff, phaseLaurent_eq_sum, HahnSeries.coeff_sum]
  have hh : (∑ k ∈ F.support, (HahnSeries.single (-(k : ℤ)) (F.coeff k) : L).coeff (n+1)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    exact HahnSeries.coeff_single_of_ne (by omega)
  rw [hh, mul_zero]

/-- Subtract the complete regular term after clearing the actual coefficient. -/
def phaseSeries (h : ℕ) (N : NormalData ι) : PowerSeries (Matrix ι ι ℂ) :=
  clearAt h (coefficient N) - PowerSeries.X^(h-1)*N.regular

theorem toLaurent_phaseSeries (h : ℕ) (hh : 0 < h) (N : NormalData ι)
    (hp : poleOrder (coefficient N) ≤ h) :
    toLaurent (phaseSeries h N) = (HahnSeries.single (h : ℤ) 1 : L) •
      Matrix.diagonal (fun i => D (phaseLaurent (N.phase i))) := by
  rw [phaseSeries, map_sub, toLaurent_clearAt _ _ hp, map_mul, toLaurent_X_pow]
  apply Matrix.ext
  intro i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.one_apply, coefficient, Matrix.add_apply, regularCoefficient,
    mul_ite, ite_mul, mul_one (M := L), mul_zero (M₀ := L), zero_mul (M₀ := L),
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hx : (HahnSeries.single (h : ℤ) 1 : L)*HahnSeries.single (-1) 1 =
      HahnSeries.single ((h-1 : ℕ) : ℤ) 1 := by
    rw [HahnSeries.single_mul_single, mul_one]
    have hi : (h : ℤ)+(-1) = ((h-1 : ℕ) : ℤ) := by omega
    rw [hi]
  rw [mul_add, ← mul_assoc, hx]
  abel

theorem phaseSeries_coeff_zero (h : ℕ) (hh : 0 < h) (N : NormalData ι)
    (hp : poleOrder (coefficient N) ≤ h) (n : ℕ) (hn : h ≤ n) :
    PowerSeries.coeff n (phaseSeries h N) = 0 := by
  apply Matrix.ext
  intro i j
  have he := congrArg (fun M : Matrix ι ι L => (M i j).coeff (n : ℤ))
    (toLaurent_phaseSeries h hh N hp)
  simp only [toLaurent_apply, LaurentSeries.coeff_coe_powerSeries,
    WasowPowerSeries.coeff_entry, Matrix.smul_apply, smul_eq_mul] at he
  by_cases hij : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq, HahnSeries.coeff_single_mul, one_mul] at he
    rw [phase_derivative_coeff_nonneg _ _ (by omega)] at he
    exact he
  · simp only [Matrix.diagonal_apply_ne _ hij, mul_zero, HahnSeries.coeff_zero] at he
    exact he

/-- This finite polynomial encodes the original full phase after clearing. -/
def phasePolynomial (h : ℕ) (N : NormalData ι) : Polynomial (Matrix ι ι ℂ) :=
  PowerSeries.trunc h (phaseSeries h N)

theorem phasePolynomial_coe (h : ℕ) (hh : 0 < h) (N : NormalData ι)
    (hp : poleOrder (coefficient N) ≤ h) :
    (phasePolynomial h N : PowerSeries (Matrix ι ι ℂ)) = phaseSeries h N := by
  apply PowerSeries.ext
  intro n
  rw [Polynomial.coeff_coe, phasePolynomial, PowerSeries.coeff_trunc]
  by_cases hn : n < h
  · simp [hn]
  · rw [if_neg hn, phaseSeries_coeff_zero h hh N hp n (by omega)]

/-- Recovery identifies the polynomial with the originally fixed phase derivative. -/
theorem recover_phasePolynomial (h : ℕ) (hh : 0 < h) (N : NormalData ι)
    (hp : poleOrder (coefficient N) ≤ h) :
    (HahnSeries.single (-(h : ℤ)) 1 : L) •
      toLaurent (phasePolynomial h N : PowerSeries (Matrix ι ι ℂ)) =
      Matrix.diagonal (fun i => D (phaseLaurent (N.phase i))) := by
  rw [phasePolynomial_coe h hh N hp, toLaurent_phaseSeries h hh N hp, smul_smul]
  simp

theorem trunc_phaseSeries (h n : ℕ) (hh : 0 < h) (hn : h ≤ n)
    (N : NormalData ι) (hp : poleOrder (coefficient N) ≤ h) :
    PowerSeries.trunc n (phaseSeries h N) = phasePolynomial h N := by
  apply Polynomial.ext
  intro k
  simp only [phasePolynomial, PowerSeries.coeff_trunc]
  by_cases hk : k < h
  · rw [if_pos hk, if_pos (lt_of_lt_of_le hk hn)]
  · rw [phaseSeries_coeff_zero h hh N hp k (by omega)]
    simp

theorem trunc_shift (R : PowerSeries (Matrix ι ι ℂ)) (d n : ℕ) (hd : d ≤ n) :
    PowerSeries.trunc n (PowerSeries.X^d * R) =
      Polynomial.X^d * PowerSeries.trunc (n-d) R := by
  apply Polynomial.ext
  intro k
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  by_cases hk : d ≤ k
  · rw [if_pos hk, if_pos hk, PowerSeries.coeff_trunc]
    by_cases hkn : k < n
    · rw [if_pos hkn, if_pos (by omega)]
    · rw [if_neg hkn, if_neg (by omega)]
  · simp [hk]

/-- The exact finite canonical identity: the phase term is independent of n. -/
theorem trunc_canonical (h n : ℕ) (hh : 0 < h) (hn : h ≤ n)
    (N : NormalData ι) (hp : poleOrder (coefficient N) ≤ h) :
    PowerSeries.trunc n (clearAt h (coefficient N)) =
      phasePolynomial h N + Polynomial.X^(h-1) * PowerSeries.trunc (n-h+1) N.regular := by
  have he : clearAt h (coefficient N) = phaseSeries h N + PowerSeries.X^(h-1)*N.regular := by
    unfold phaseSeries
    abel
  rw [he, map_add, trunc_phaseSeries h n hh hn N hp, trunc_shift _ _ _ (by omega)]
  rw [show n-(h-1)=n-h+1 by omega]

/-- Actual finite evaluation retains the complete fixed phase polynomial and
only shortens the regular series. No infinite formal series is evaluated. -/
theorem eval_trunc_canonical (h n : ℕ) (hh : 0 < h) (hn : h ≤ n)
    (N : NormalData ι) (hp : poleOrder (coefficient N) ≤ h)
    {z : ℂ} (hz : z ≠ 0) :
    z^(-(h : ℤ)) • WasowMatrixPolynomial.eval (PowerSeries.trunc n
      (clearAt h (coefficient N))) z =
      z^(-(h : ℤ)) • WasowMatrixPolynomial.eval (phasePolynomial h N) z +
      z⁻¹ • WasowMatrixPolynomial.eval (PowerSeries.trunc (n-h+1) N.regular) z := by
  rw [trunc_canonical h n hh hn N hp, WasowMatrixPolynomial.eval_add,
    WasowMatrixPolynomial.eval_X_pow_mul, smul_add, smul_smul]
  have he : z^(-(h : ℤ))*z^(h-1) = z⁻¹ := by
    rw [← zpow_natCast, ← zpow_add₀ hz]
    have hi : -(h : ℤ) + ((h-1 : ℕ) : ℤ) = -1 := by omega
    rw [hi, zpow_neg_one]
  rw [he]

/-- Finite regular coefficients retain the original phase-fiber decomposition. -/
theorem truncated_regular_separated (N : NormalData ι) (n k : ℕ) (i j : ι)
    (hne : N.phase i ≠ N.phase j) :
    (PowerSeries.trunc n N.regular).coeff k i j = 0 := by
  rw [PowerSeries.coeff_trunc]
  split_ifs
  · exact N.separated k i j hne
  · rfl

#print axioms phase_derivative_coeff_nonneg
#print axioms toLaurent_phaseSeries
#print axioms phaseSeries_coeff_zero
#print axioms phasePolynomial_coe
#print axioms recover_phasePolynomial
#print axioms trunc_phaseSeries
#print axioms trunc_shift
#print axioms trunc_canonical
#print axioms eval_trunc_canonical
#print axioms truncated_regular_separated
end WasowCanonicalTruncation
