import WasowPencilSimilarity

/-! Genuine rectangular changes between different Jordan block coordinate
sets preserve the polynomial-pencil degree invariant. Equal dimension is
proved from the two inverse identities, not supplied as an extra hypothesis. -/
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace WasowPencilCoordinates
open WasowPencilReduction WasowReductionDescent WasowPencilDescent

/-- A rectangular pair with both inverse identities has equal dimensions,
as follows from the traces of its two products over the complex numbers. -/
theorem card_eq_of_two_sided_inverse {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (P : Matrix ι κ ℂ) (Q : Matrix κ ι ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Fintype.card ι = Fintype.card κ := by
  have ht := Matrix.trace_mul_comm P Q
  rw [hPQ, hQP, Matrix.trace_one, Matrix.trace_one] at ht
  exact_mod_cast ht

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
  {h : σ → ℕ} {g : τ → ℕ}

omit [Fintype τ] in
/-- The actual characteristic pencil transforms by the mapped rectangular
coordinate matrices, including the coefficient of the variable. -/
theorem pencil_coordinates (C : Matrix (OldIndex h) (OldIndex h) ℂ)
    (P : Matrix (OldIndex h) (OldIndex g) ℂ)
    (Q : Matrix (OldIndex g) (OldIndex h) ℂ) (hQP : Q * P = 1) :
    pencil (Q * C * P) = Q.map Polynomial.C * pencil C * P.map Polynomial.C := by
  unfold pencil
  rw [Matrix.map_mul, Matrix.map_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [← Matrix.map_mul (L := Q) (M := P), hQP]
  simp

/-- Every determinantal divisor is preserved in the new coordinate type. -/
theorem minorGCD_coordinates (C : Matrix (OldIndex h) (OldIndex h) ℂ)
    (P : Matrix (OldIndex h) (OldIndex g) ℂ)
    (Q : Matrix (OldIndex g) (OldIndex h) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (k : ℕ) :
    minorGCD (pencil (Q * C * P)) k = minorGCD (pencil C) k := by
  rw [pencil_coordinates C P Q hQP]
  have hm : P.map Polynomial.C * Q.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hPQ]
    simp
  exact WasowMinorEquivalence.minorGCD_equivalent
    (Q.map Polynomial.C) (P.map Polynomial.C) (pencil C)
    (P.map Polynomial.C) (Q.map Polynomial.C) hm hm k

/-- The full degree sum, with its actual dimension-dependent range, is
preserved across a genuine rectangular two-sided coordinate change. -/
theorem degreeMass_coordinates (C : Matrix (OldIndex h) (OldIndex h) ℂ)
    (P : Matrix (OldIndex h) (OldIndex g) ℂ)
    (Q : Matrix (OldIndex g) (OldIndex h) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    degreeMass (pencil (Q * C * P)) = degreeMass (pencil C) := by
  have hc := card_eq_of_two_sided_inverse P Q hPQ hQP
  unfold WasowPencilDescent.degreeMass
  simp_rw [minorGCD_coordinates C P Q hPQ hQP]
  rw [hc]

/-- The coordinate invariant also survives the actual scalar subtraction
used before choosing the next nilpotent Jordan basis. -/
theorem degreeMass_translated_coordinates (C : Matrix (OldIndex h) (OldIndex h) ℂ)
    (α : ℂ) (P : Matrix (OldIndex h) (OldIndex g) ℂ)
    (Q : Matrix (OldIndex g) (OldIndex h) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    degreeMass (pencil (Q * (C - α • 1) * P)) = degreeMass (pencil C) := by
  rw [degreeMass_coordinates _ P Q hPQ hQP, WasowPencilSimilarity.degreeMass_sub_scalar]

#print axioms card_eq_of_two_sided_inverse
#print axioms pencil_coordinates
#print axioms minorGCD_coordinates
#print axioms degreeMass_coordinates
#print axioms degreeMass_translated_coordinates
end WasowPencilCoordinates
