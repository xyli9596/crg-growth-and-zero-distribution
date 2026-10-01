import WasowLaurentRamification
import WasowScalarPhase

/-! Fixed polynomial phases as genuine finite Laurent series in the inverse
variable, compatible with the ramification of differential coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace WasowLaurentPhase
open WasowLaurentGauge WasowLaurentRamification WasowScalarPhase

/-- Evaluation of a phase polynomial at the actual Laurent element `t⁻¹`. -/
def phaseLaurent : Polynomial ℂ →+* L :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (-1) 1)

@[simp] theorem phaseLaurent_monomial (n : ℕ) (c : ℂ) :
    phaseLaurent (Polynomial.monomial n c) = HahnSeries.single (-(n : ℤ)) c := by
  simp [phaseLaurent, Polynomial.eval₂_monomial, HahnSeries.single_pow,
    HahnSeries.C_apply]

theorem phaseLaurent_eq_sum (F : Polynomial ℂ) :
    phaseLaurent F = ∑ n ∈ F.support, HahnSeries.single (-(n : ℤ)) (F.coeff n) := by
  conv_lhs => rw [← Polynomial.sum_monomial_eq F]
  simp only [Polynomial.sum, map_sum, phaseLaurent_monomial]

@[simp] theorem phaseLaurent_zero : phaseLaurent 0 = 0 := map_zero _

@[simp] theorem phaseLaurent_add (F H : Polynomial ℂ) :
    phaseLaurent (F+H) = phaseLaurent F + phaseLaurent H := map_add _ _ _

/-- Scalar extraction at rank q has exactly the inverse-variable derivative. -/
theorem derivative_rankPhase (q : ℕ) (α : ℂ) :
    D (phaseLaurent (rankPhase q α)) = HahnSeries.single (-(q : ℤ)-2) (-α) := by
  rw [rankPhase, phaseLaurent_monomial]
  simp only [D, LaurentSeries.derivative, LaurentSeries.hasseDeriv_single,
    Ring.choose_one_right, zsmul_eq_mul, Nat.cast_one]
  have hq : (q : ℂ)+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero q)
  have he : -((q+1 : ℕ) : ℤ)-1 = -(q : ℤ)-2 := by omega
  rw [he]
  congr 1
  push_cast
  field_simp

/-- Additional ramification is polynomial composition, not a newly selected phase. -/
theorem ramify_phaseLaurent (p : ℕ) (hp : 0 < p) (F : Polynomial ℂ) :
    ramify p hp (phaseLaurent F) = phaseLaurent (F.comp (Polynomial.X^p)) := by
  induction F using Polynomial.induction_on' with
  | add F H hF hH => simp only [map_add, Polynomial.add_comp, hF, hH]
  | monomial n c =>
    rw [phaseLaurent_monomial, ramify_single, Polynomial.monomial_comp]
    simp only [map_mul, map_pow]
    simp [phaseLaurent, HahnSeries.single_pow, HahnSeries.C_apply, mul_comm]

theorem derivative_phase_ramify (p : ℕ) (hp : 0 < p) (F : Polynomial ℂ) :
    D (phaseLaurent (F.comp (Polynomial.X^p))) =
      jacobian p * ramify p hp (D (phaseLaurent F)) := by
  rw [← ramify_phaseLaurent, derivative_ramify]

#print axioms phaseLaurent_monomial
#print axioms phaseLaurent_eq_sum
#print axioms phaseLaurent_zero
#print axioms phaseLaurent_add
#print axioms derivative_rankPhase
#print axioms ramify_phaseLaurent
#print axioms derivative_phase_ramify
end WasowLaurentPhase
