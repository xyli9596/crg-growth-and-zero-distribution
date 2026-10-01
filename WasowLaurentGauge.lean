import WasowPowerSeries
import Mathlib.RingTheory.LaurentSeries

/-! Genuine Laurent-series differentiation and composition of formal gauges.
Negative powers and nonidentity constant coordinate changes are allowed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace WasowLaurentGauge

abbrev L := LaurentSeries ℂ
abbrev D : L →ₗ[ℂ] L := LaurentSeries.derivative ℂ

theorem derivative_coeff (f : L) (n : ℤ) :
    (D f).coeff n = (n + 1 : ℂ) * f.coeff (n + 1) := by
  simp [D, LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff, zsmul_eq_mul]

theorem derivative_monomial_mul (m : ℤ) (f : L) :
    D (HahnSeries.single m 1 * f) =
      HahnSeries.single (m-1) (m : ℂ) * f + HahnSeries.single m 1 * D f := by
  ext n
  simp only [derivative_coeff, HahnSeries.coeff_single_mul, one_mul,
    HahnSeries.coeff_add]
  have h : n - (m-1) = n+1-m := by omega
  have h' : n-m+1 = n+1-m := by omega
  rw [h, h']
  push_cast
  ring

theorem derivative_powerSeries (f : PowerSeries ℂ) :
    D (f : L) = (PowerSeries.derivative ℂ f : L) := by
  ext n
  rw [derivative_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  by_cases hn : 0 ≤ n
  · rw [if_neg (by omega), if_neg (by omega), PowerSeries.coeff_derivative]
    have heq : (n+1).natAbs = n.natAbs+1 := by omega
    rw [heq]
    have hc : (n : ℂ) = (n.natAbs : ℂ) := by
      have hz : (n.natAbs : ℤ) = n := by omega
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℂ)) hz.symm
    rw [hc]
    ring
  · by_cases h1 : n = -1
    · subst n
      simp
    · rw [if_pos (by omega), if_pos (by omega)]
      simp

theorem derivative_mul (f g : L) : D (f*g) = D f*g+f*D g := by
  suffices ∀ (m n : ℤ) (a b : PowerSeries ℂ),
      D ((HahnSeries.single m 1 * (a : L)) * (HahnSeries.single n 1 * (b : L))) =
      D (HahnSeries.single m 1 * (a : L)) * (HahnSeries.single n 1 * (b : L)) +
      (HahnSeries.single m 1 * (a : L)) * D (HahnSeries.single n 1 * (b : L)) by
    simpa using this f.order g.order f.powerSeriesPart g.powerSeriesPart
  intro m n a b
  rw [show (HahnSeries.single m 1 * (a : L)) * (HahnSeries.single n 1 * (b : L)) =
      HahnSeries.single (m+n) 1 * ((a*b : PowerSeries ℂ) : L) by
        rw [PowerSeries.coe_mul, show (HahnSeries.single (m+n) 1 : L) =
          HahnSeries.single m 1 * HahnSeries.single n 1 by simp]
        ring]
  rw [derivative_monomial_mul, derivative_powerSeries, Derivation.leibniz]
  simp only [smul_eq_mul, map_add, map_mul]
  rw [derivative_monomial_mul, derivative_monomial_mul, derivative_powerSeries,
    derivative_powerSeries]
  have h1 : (HahnSeries.single (m+n-1) ((m+n : ℤ) : ℂ) : L) =
      HahnSeries.single (m-1) (m : ℂ) * HahnSeries.single n 1 +
      HahnSeries.single m 1 * HahnSeries.single (n-1) (n : ℂ) := by
    simp only [HahnSeries.single_mul_single, mul_one, one_mul]
    rw [show m-1+n=m+n-1 by omega, show m+(n-1)=m+n-1 by omega,
      ← HahnSeries.single_add]
    norm_cast
  rw [h1, show (HahnSeries.single (m+n) 1 : L) =
      HahnSeries.single m 1 * HahnSeries.single n 1 by simp]
  ring

variable {ι κ ν : Type*}

def matrixDerivative (A : Matrix ι κ L) : Matrix ι κ L := fun i j => D (A i j)

theorem matrixDerivative_mul [Fintype κ] (A : Matrix ι κ L) (B : Matrix κ ν L) :
    matrixDerivative (A*B) = matrixDerivative A*B + A*matrixDerivative B := by
  apply Matrix.ext
  intro i j
  simp only [matrixDerivative, Matrix.mul_apply, Matrix.add_apply, map_sum,
    derivative_mul, Finset.sum_add_distrib]

/-- An actual formal differential gauge identity, including rectangular changes of basis. -/
def GaugeEquation [Fintype ι] [Fintype κ]
    (A : Matrix ι ι L) (G : Matrix ι κ L) (B : Matrix κ κ L) : Prop :=
  A*G-G*B=matrixDerivative G

/-- Genuine Laurent matrix products compose their differential gauge equations. -/
theorem gaugeEquation_comp [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι ι L) (G : Matrix ι κ L) (B : Matrix κ κ L)
    (H : Matrix κ ν L) (C : Matrix ν ν L)
    (hG : GaugeEquation A G B) (hH : GaugeEquation B H C) :
    GaugeEquation A (G*H) C := by
  unfold GaugeEquation at *
  rw [matrixDerivative_mul, ← hG, ← hH]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

section PowerSeriesEmbedding
variable [Fintype ι] [DecidableEq ι]

/-- The actual coefficientwise identification, with matrix multiplication preserved. -/
def entries : PowerSeries (Matrix ι ι ℂ) →+* Matrix ι ι (PowerSeries ℂ) where
  toFun F := fun i j => WasowPowerSeries.entry F i j
  map_zero' := by
    apply Matrix.ext
    intro i j
    apply PowerSeries.ext
    intro n
    simp
  map_one' := by
    apply Matrix.ext
    intro i j
    apply PowerSeries.ext
    intro n
    by_cases hij : i=j <;> by_cases hn : n=0 <;> simp [Matrix.one_apply, hij, hn]
  map_add' F G := by
    apply Matrix.ext
    intro i j
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (WasowPowerSeries.entry (F+G) i j) =
      PowerSeries.coeff n (WasowPowerSeries.entry F i j + WasowPowerSeries.entry G i j)
    simp
  map_mul' F G := by
    apply Matrix.ext
    intro i j
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (WasowPowerSeries.entry (F*G) i j) =
      PowerSeries.coeff n (∑ k, WasowPowerSeries.entry F i k * WasowPowerSeries.entry G k j)
    simp only [WasowPowerSeries.coeff_entry, PowerSeries.coeff_mul, map_sum]
    simp only [Matrix.sum_apply, Matrix.mul_apply]
    exact Finset.sum_comm

/-- This map is defined on complete series, not on a truncation or a symbolic expression. -/
def toLaurent : PowerSeries (Matrix ι ι ℂ) →+* Matrix ι ι L :=
  (HahnSeries.ofPowerSeries ℤ ℂ).mapMatrix.comp entries

@[simp] theorem toLaurent_apply (F : PowerSeries (Matrix ι ι ℂ)) (i j : ι) :
    toLaurent F i j = (WasowPowerSeries.entry F i j : L) := rfl

theorem toLaurent_derivative (F : PowerSeries (Matrix ι ι ℂ)) :
    toLaurent (WasowPowerSeries.derivative F) = matrixDerivative (toLaurent F) := by
  apply Matrix.ext
  intro i j
  change (WasowPowerSeries.entry (WasowPowerSeries.derivative F) i j : L) =
    D (WasowPowerSeries.entry F i j : L)
  rw [WasowPowerSeries.entry_derivative, derivative_powerSeries]

theorem toLaurent_C (A : Matrix ι ι ℂ) :
    toLaurent (PowerSeries.C A) = A.map HahnSeries.C := by
  apply Matrix.ext
  intro i j
  change (WasowPowerSeries.entry (PowerSeries.C A) i j : L) = HahnSeries.C (A i j)
  rw [show WasowPowerSeries.entry (PowerSeries.C A) i j = PowerSeries.C (A i j) by
    apply PowerSeries.ext
    intro n
    by_cases hn : n=0 <;> simp [PowerSeries.coeff_C, hn]]
  exact PowerSeries.coe_C _

theorem toLaurent_X_pow (n : ℕ) :
    toLaurent (PowerSeries.X ^ n : PowerSeries (Matrix ι ι ℂ)) =
      (HahnSeries.single (n : ℤ) 1 : L) • (1 : Matrix ι ι L) := by
  apply Matrix.ext
  intro i j
  have he : WasowPowerSeries.entry
      (PowerSeries.X ^ n : PowerSeries (Matrix ι ι ℂ)) i j =
      if i=j then (PowerSeries.X ^ n : PowerSeries ℂ) else 0 := by
    apply PowerSeries.ext
    intro k
    by_cases hij : i=j <;> by_cases hkn : k=n <;>
      simp [PowerSeries.coeff_X_pow, hij, hkn]
  rw [toLaurent_apply]
  rw [he]
  by_cases hij : i=j <;> simp [hij, Matrix.smul_apply,
    HahnSeries.ofPowerSeries_X_pow]

theorem toLaurent_inverses (P Q : PowerSeries (Matrix ι ι ℂ))
    (hPQ : P*Q=1) (hQP : Q*P=1) :
    toLaurent P*toLaurent Q=1 ∧ toLaurent Q*toLaurent P=1 := by
  constructor
  · simpa using congrArg (toLaurent (ι := ι)) hPQ
  · simpa using congrArg (toLaurent (ι := ι)) hQP

/-- The real differential coefficient in the inverse variable `t=1/z`.
The book rank is `q`; the coefficient is `-t^(-q-2) A(t)`. -/
def differentialCoefficient (q : ℕ) (A : PowerSeries (Matrix ι ι ℂ)) : Matrix ι ι L :=
  (HahnSeries.single (-(q : ℤ)-2) (-1) : L) • toLaurent A

/-- Every previously proved full power-series gauge equation becomes an actual
Laurent differential equation, including its genuine two-sided gauge inverse. -/
theorem powerSeries_gauge_equation (q : ℕ) (A P B : PowerSeries (Matrix ι ι ℂ))
    (heq : A*P-P*B = -(PowerSeries.X^(q+2) * WasowPowerSeries.derivative P)) :
    GaugeEquation (differentialCoefficient q A) (toLaurent P)
      (differentialCoefficient q B) := by
  have he := congrArg (toLaurent (ι := ι)) heq
  simp only [map_sub, map_mul, map_neg, toLaurent_X_pow, toLaurent_derivative] at he
  unfold GaugeEquation differentialCoefficient
  apply Matrix.ext
  intro i j
  have heij := congrFun (congrFun he i) j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, ite_mul,
    mul_one, zero_mul, mul_zero] at heij
  dsimp only [matrixDerivative] at heij ⊢
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true] at heij
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc, mul_left_comm (toLaurent P i _)]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub, heij]
  have hcancel (x : L) :
      (HahnSeries.single (-(q : ℤ)-2) (-1) : L) *
        -(HahnSeries.single ((q+2 : ℕ) : ℤ) 1 * x) = x := by
    rw [mul_neg (α := L), ← mul_assoc, HahnSeries.single_mul_single]
    simp
    ring
  exact hcancel _

end PowerSeriesEmbedding

#print axioms derivative_coeff
#print axioms derivative_monomial_mul
#print axioms derivative_powerSeries
#print axioms derivative_mul
#print axioms matrixDerivative_mul
#print axioms gaugeEquation_comp
#print axioms toLaurent_apply
#print axioms toLaurent_derivative
#print axioms toLaurent_C
#print axioms toLaurent_X_pow
#print axioms toLaurent_inverses
#print axioms powerSeries_gauge_equation
end WasowLaurentGauge
