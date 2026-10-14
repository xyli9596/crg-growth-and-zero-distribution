import CRGConstantMultiplierOrder
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! The actual LWW equation is converted algebraically to the independent
CRG constant-multiplier theorem. No LWW growth or representation lemma is imported. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators
namespace CRGPolynomialExponentialOrder

theorem normalized_coefficient_expansion (p : Polynomial ℂ) (γ : ℕ) (ω z : ℂ) :
    Complex.exp (-((γ:ℂ)*ω*z))*p.eval (Complex.exp (ω*z)) =
      ∑i:Fin (p.natDegree+1), p.coeff i.val *
        Complex.exp (((i.val:ℂ)-(γ:ℂ))*ω*z) := by
  rw [Polynomial.eval_eq_sum_range, ←Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Complex.exp_nat_mul]
  calc
    _ = p.coeff i * (Complex.exp (-((γ:ℂ)*ω*z)) * Complex.exp ((i:ℂ)*(ω*z))) := by ring
    _ = p.coeff i * Complex.exp (-((γ:ℂ)*ω*z)+(i:ℂ)*(ω*z)) := by rw [Complex.exp_add]
    _ = _ := by congr 2; ring

/-- Any leading exponential monomial, with the actual entire finite-order
nonpolynomial solution and pointwise equation, has order one, mean type and CRG. -/
theorem polynomial_exponential_order_one {n γ : ℕ}
    (P : Fin (n+1)→Polynomial ℂ) (ω : ℂ)
    (hlead : P (Fin.last n)=X^γ) (f : ℂ→ℂ)
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬∃p:Polynomial ℂ,∀z:ℂ,f z=p.eval z)
    (heq : ∀z:ℂ,∑j:Fin (n+1),
      (P j).eval (Complex.exp (ω*z))*iteratedDeriv j.val f z=0) :
    CRGOrder.IsOrder f 1 ∧ LevinGrowth.FinitePositiveType f 1 ∧
      LevinGrowth.ManuscriptCRG f 1 := by
  let N : Fin n→ℕ := fun j => (P j.castSucc).natDegree+1
  let c : (j:Fin n)→Fin (N j)→ℂ := fun j i => (P j.castSucc).coeff i.val
  let ν : (j:Fin n)→Fin (N j)→ℂ := fun _ i => ((i.val:ℂ)-(γ:ℂ))*ω
  apply CRGConstantMultiplierOrder.order_one_of_constant_multipliers N c ν f hf hfinite htrans
  intro z
  have hcancel : Complex.exp (-((γ:ℂ)*ω*z)) * (Complex.exp (ω*z))^γ=1 := by
    rw [←Complex.exp_nat_mul, ←Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  have hexpand (j:Fin n) :
      (∑i:Fin (N j),c j i*Complex.exp (ν j i*z)) =
        Complex.exp (-((γ:ℂ)*ω*z))*(P j.castSucc).eval (Complex.exp (ω*z)) := by
    simpa only [N,c,ν,mul_assoc] using
      (normalized_coefficient_expansion (P j.castSucc) γ ω z).symm
  simp_rw [hexpand]
  calc
    _ = Complex.exp (-((γ:ℂ)*ω*z)) *
      (∑j:Fin (n+1),(P j).eval (Complex.exp (ω*z))*iteratedDeriv j.val f z) := by
        rw [Fin.sum_univ_castSucc, mul_add, Finset.mul_sum]
        simp only [Fin.val_castSucc,Fin.val_last,hlead,eval_pow,eval_X]
        rw [←mul_assoc, hcancel,one_mul]
        rw [add_comm (iteratedDeriv n f z)]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = 0 := by rw [heq z,mul_zero]

#print axioms normalized_coefficient_expansion
#print axioms polynomial_exponential_order_one
end CRGPolynomialExponentialOrder
