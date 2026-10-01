import CRGPuiseuxMonic
import CRGCollectedEquation

/-! Coefficient-wise finite collection of the exponential-polynomial parts
in both integral-kernel classes. The monic top coefficient is explicitly
retained in the zero exponent group, before any integral is considered. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators
namespace CRGExponentialCoefficientGroups
open CRGExponentialCoefficients CRGCollectedEquation CRGPuiseuxMonic
variable {n : ℕ}

structure MonicGroups (a : Fin n → ℂ → ℂ) where
  exponents : Finset (Polynomial ℂ)
  zero_mem : 0∈exponents
  coeff : Polynomial ℂ → Fin (n+1) → Polynomial ℂ
  normalized : ∀q∈exponents,q.coeff 0=0
  top : ∀q,coeff q (Fin.last n)=if q=0 then 1 else 0
  representation : ∀j z,fullCoefficient a j z=
    ∑q∈exponents,Complex.exp (q.eval z)*(coeff q j).eval z

theorem exists_monic_groups (a : Fin n → ℂ → ℂ)
    (ha : ∀j,IsExponentialPolynomial (a j)) : Nonempty (MonicGroups a) := by
  classical
  choose N P Q hrep using ha
  let ι := TermIndex N
  let P' : ι → Polynomial ℂ := termPolynomial P
  let Q' : ι → Polynomial ℂ := termExponent Q
  let k : ι → Fin (n+1) := termOrder
  let b := coefficientGroup P' Q' k
  let S := Finset.univ.image (fun i : ι=>normalizedExponent (Q' i))
  have h0 : 0∈S := Finset.mem_image.mpr
    ⟨Sum.inl (),Finset.mem_univ _,by simp [Q',termExponent,normalizedExponent]⟩
  have hid (v : Fin (n+1) → ℂ) (z : ℂ) :
      (∑j,fullCoefficient a j z*v j)=
        ∑q∈S,Complex.exp (q.eval z)*(∑j,(b q j).eval z*v j) := by
    calc
      _ = ∑i : ι,(P' i).eval z*Complex.exp ((Q' i).eval z)*v (k i) := by
        rw [Fin.sum_univ_castSucc]
        simp only [ι,Fintype.sum_sum_type,Fintype.sum_sigma,Finset.univ_unique,
          Finset.sum_singleton,P',Q',k,termPolynomial,termExponent,termOrder,
          fullCoefficient_castSucc,fullCoefficient_last,eval_one,eval_zero,
          Complex.exp_zero,one_mul]
        simp_rw [hrep,Finset.sum_mul]
        ring
      _ = _ := collected_identity P' Q' k v z
  refine ⟨⟨S,h0,b,?_,?_,?_⟩⟩
  · intro q hq
    obtain ⟨i,_hi,he⟩ := Finset.mem_image.mp hq
    rw [←he]
    exact normalizedExponent_zero _
  · intro q
    simp [b,coefficientGroup,P',Q',k,ι,Fintype.sum_sum_type,
      termPolynomial,termExponent,termOrder,normalizedExponent,normalizedMultiplier,eq_comm]
  · intro j z
    have hh := hid (fun k=>if k=j then 1 else 0) z
    simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,
      if_true] using hh

#print axioms exists_monic_groups
end CRGExponentialCoefficientGroups
