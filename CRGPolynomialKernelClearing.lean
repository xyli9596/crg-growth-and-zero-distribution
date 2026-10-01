import CRGPolynomialKernelFormalGroups
import CRGAsymptoticCoefficientScalarAlgebra

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial Asymptotics
open scoped Topology BigOperators
namespace CRGPolynomialKernel
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientScalarAlgebra

/-- The polynomial obtained by clearing a ramified polynomial's pole. -/
def clearedPolynomial (P : Polynomial ℂ) (p h : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (P.natDegree+1), Polynomial.C (P.coeff j) * Polynomial.X^(h-p*j)

theorem clearedPolynomial_eval {P : Polynomial ℂ} {p h : ℕ}
    (hh : p*P.natDegree ≤ h) {x : ℂ} (hx : x ≠ 0) :
    (clearedPolynomial P p h).eval x = x^h * P.eval (x^(-(p:ℤ))) := by
  rw [clearedPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_eq_sum_range]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j ≤ P.natDegree := by
    simp only [Finset.mem_range] at hj
    omega
  have hjh : p*j ≤ h := (Nat.mul_le_mul_left p hjd).trans hh
  have he : x^h * (x^(-(p:ℤ)))^j = x^(h-p*j) := by
    rw [←zpow_natCast x h,←zpow_natCast (x^(-(p:ℤ))) j,←zpow_mul,←zpow_add₀ hx]
    have hn : (h:ℤ)+(-(p:ℤ)*(j:ℤ)) = (h-p*j:ℕ) := by
      rw [Nat.cast_sub hjh,Nat.cast_mul]
      ring
    rw [hn,zpow_natCast]
  rw [mul_left_comm,he]

theorem clearedPolynomial_coeff_above (P : Polynomial ℂ) (p h j : ℕ) (hj : h<j) :
    (clearedPolynomial P p h).coeff j = 0 := by
  rw [clearedPolynomial,Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k _
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,if_neg (by omega),mul_zero]

theorem clearedPolynomial_ne_zero {P : Polynomial ℂ} (hP : P≠0)
    {p h : ℕ} (hp : 0<p) (hh : p*P.natDegree ≤ h) : clearedPolynomial P p h ≠ 0 := by
  have hc : (clearedPolynomial P p h).coeff (h-p*P.natDegree) = P.leadingCoeff := by
    rw [clearedPolynomial,Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single P.natDegree]
    · simp [Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Polynomial.coeff_natDegree]
    · intro j hj hne
      have hjd : j ≤ P.natDegree := by
        simp only [Finset.mem_range] at hj
        omega
      have hje : h-p*j ≠ h-p*P.natDegree := by
        intro he
        have hjh := (Nat.mul_le_mul_left p hjd).trans hh
        have hm : p*j = p*P.natDegree := by omega
        exact hne (Nat.eq_of_mul_eq_mul_left hp hm)
      rw [Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,if_neg (Ne.symm hje),mul_zero]
    · intro hn
      simp only [Finset.mem_range] at hn
      omega
  intro hz
  rw [hz,Polynomial.coeff_zero] at hc
  exact (Polynomial.leadingCoeff_ne_zero.mpr hP) hc.symm

/-- Multiplying an integral's zero-head series by the clearing monomial
places every coefficient strictly above the entire polynomial head. -/
theorem cleared_zero_head_coeff {A : PowerSeries ℂ} (hA : PowerSeries.constantCoeff A=0)
    (h j : ℕ) (hj : j≤h) : PowerSeries.coeff j (PowerSeries.X^h*A)=0 := by
  rcases lt_or_eq_of_le hj with hj | rfl
  · rw [PowerSeries.coeff_X_pow_mul']
    rw [if_neg (Nat.not_le.mpr hj)]
  · rw [PowerSeries.coeff_X_pow_mul']
    simp only [if_pos le_rfl,Nat.sub_self,PowerSeries.coeff_zero_eq_constantCoeff_apply,hA]

#print axioms clearedPolynomial_eval
#print axioms clearedPolynomial_ne_zero
#print axioms cleared_zero_head_coeff
end CRGPolynomialKernel
