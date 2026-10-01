import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-! Actual collection of exponential-polynomial coefficient terms. Constant
exponents are absorbed into polynomial multipliers before equal exponents are
combined; cancellation of an entire coefficient group is allowed. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators
namespace CRGExponentialCoefficients

def normalizedExponent (Q : Polynomial ℂ) : Polynomial ℂ := Q-C (Q.coeff 0)

def normalizedMultiplier (P Q : Polynomial ℂ) : Polynomial ℂ :=
  C (Complex.exp (Q.coeff 0))*P

theorem normalizedExponent_zero (Q : Polynomial ℂ) :
    (normalizedExponent Q).coeff 0=0 := by simp [normalizedExponent]

theorem normalized_term (P Q : Polynomial ℂ) (z : ℂ) :
    P.eval z*Complex.exp (Q.eval z) =
    (normalizedMultiplier P Q).eval z*Complex.exp ((normalizedExponent Q).eval z) := by
  simp only [normalizedMultiplier, normalizedExponent, eval_mul, eval_C, eval_sub]
  rw [mul_comm (Complex.exp (Q.coeff 0)) (P.eval z), mul_assoc, ← Complex.exp_add]
  congr 1
  ring_nf

def groupedCoefficient {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P Q : ι → Polynomial ℂ) (q : Polynomial ℂ) : Polynomial ℂ :=
  ∑ i ∈ s.filter (fun i => normalizedExponent (Q i)=q), normalizedMultiplier (P i) (Q i)

theorem grouped_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P Q : ι → Polynomial ℂ) (z : ℂ) :
    (∑ i ∈ s, (P i).eval z*Complex.exp ((Q i).eval z)) =
    ∑ q ∈ s.image (fun i => normalizedExponent (Q i)),
      (groupedCoefficient s P Q q).eval z*Complex.exp (q.eval z) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := s)
    (t := s.image (fun i => normalizedExponent (Q i)))
    (g := fun i => normalizedExponent (Q i))
    (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    (fun i => (P i).eval z*Complex.exp ((Q i).eval z))]
  apply Finset.sum_congr rfl
  intro q _
  unfold groupedCoefficient
  rw [eval_finsetSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [normalized_term]
  rw [(Finset.mem_filter.mp hi).2]

theorem distinct_normalized_nonconstant {P Q : Polynomial ℂ}
    (hP : P.coeff 0=0) (hQ : Q.coeff 0=0) (hne : P≠Q) :
    0<(P-Q).natDegree := by
  by_contra h
  have hd : (P-Q).natDegree=0 := Nat.eq_zero_of_not_pos h
  have he := (P-Q).eq_C_of_natDegree_eq_zero hd
  have hzero : P-Q=0 := by simpa [coeff_sub,hP,hQ] using he
  exact hne (sub_eq_zero.mp hzero)

def IsExponentialPolynomial (g : ℂ → ℂ) : Prop :=
  ∃ N : ℕ, ∃ P Q : Fin N → Polynomial ℂ,
    ∀ z, g z = ∑ i, (P i).eval z*Complex.exp ((Q i).eval z)

def SolvesMonicEquation (n : ℕ) (a : Fin n → ℂ → ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, iteratedDeriv n f z + ∑ k : Fin n, a k z*iteratedDeriv k.val f z = 0

#print axioms normalizedExponent_zero
#print axioms normalized_term
#print axioms grouped_sum
#print axioms distinct_normalized_nonconstant
end CRGExponentialCoefficients
