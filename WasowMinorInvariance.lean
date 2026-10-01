import WasowMinorExpansion
import WasowReductionDescent

/-! Exact determinantal-divisor invariance under invertible polynomial row
and column operations. This includes the unimodular transformations used in
reducing characteristic pencils; no assumed invariant-preservation property
is supplied by the caller. -/
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
namespace WasowMinorInvariance
open WasowReductionDescent WasowMinorExpansion
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Left multiplication can only increase the divisibility of minor gcds. -/
theorem minorGCD_dvd_left_mul (A T : Matrix ι ι (Polynomial ℂ)) (k : ℕ) :
    minorGCD T k ∣ minorGCD (A*T) k := by
  rw [dvd_minorGCD_iff]
  exact dvd_minor_mul A T k (minorGCD T k) (minorGCD_dvd_minor T k)

/-- The analogous statement for right multiplication. -/
theorem minorGCD_dvd_right_mul (T A : Matrix ι ι (Polynomial ℂ)) (k : ℕ) :
    minorGCD T k ∣ minorGCD (T*A) k := by
  rw [dvd_minorGCD_iff]
  exact dvd_minor_mul_left T A k (minorGCD T k) (minorGCD_dvd_minor T k)

/-- Exact normalized gcd invariance under a polynomial left inverse. -/
theorem minorGCD_left_mul (A S T : Matrix ι ι (Polynomial ℂ))
    (hSA : S*A=1) (k : ℕ) : minorGCD (A*T) k = minorGCD T k := by
  have hnorm (U : Matrix ι ι (Polynomial ℂ)) : normalize (minorGCD U k) = minorGCD U k :=
    Finset.normalize_gcd
  apply dvd_antisymm_of_normalize_eq (hnorm _) (hnorm _)
  · have h := minorGCD_dvd_left_mul S (A*T) k
    simpa only [← Matrix.mul_assoc, hSA, Matrix.one_mul] using h
  · exact minorGCD_dvd_left_mul A T k

/-- Exact normalized gcd invariance under a polynomial right inverse. -/
theorem minorGCD_right_mul (T A S : Matrix ι ι (Polynomial ℂ))
    (hAS : A*S=1) (k : ℕ) : minorGCD (T*A) k = minorGCD T k := by
  have hnorm (U : Matrix ι ι (Polynomial ℂ)) : normalize (minorGCD U k) = minorGCD U k :=
    Finset.normalize_gcd
  apply dvd_antisymm_of_normalize_eq (hnorm _) (hnorm _)
  · have h := minorGCD_dvd_right_mul (T*A) S k
    simpa only [Matrix.mul_assoc, hAS, Matrix.mul_one] using h
  · exact minorGCD_dvd_right_mul T A k

/-- Both sides may be transformed by actual unimodular polynomial matrices. -/
theorem minorGCD_equivalent (L Linv T R Rinv : Matrix ι ι (Polynomial ℂ))
    (hL : Linv*L=1) (hR : R*Rinv=1) (k : ℕ) :
    minorGCD (L*T*R) k = minorGCD T k := by
  rw [minorGCD_right_mul (L*T) R Rinv hR, minorGCD_left_mul L Linv T hL]

/-- The degree invariant used in descent is consequently basis independent. -/
theorem minorDegree_equivalent (L Linv T R Rinv : Matrix ι ι (Polynomial ℂ))
    (hL : Linv*L=1) (hR : R*Rinv=1) (k : ℕ) :
    (minorGCD (L*T*R) k).natDegree = (minorGCD T k).natDegree := by
  rw [minorGCD_equivalent L Linv T R Rinv hL hR k]

/-- The complete finite degree mass is unchanged by unimodular equivalence. -/
theorem degreeMass_equivalent {n : ℕ}
    (L Linv T R Rinv : Matrix (Fin n) (Fin n) (Polynomial ℂ))
    (hL : Linv*L=1) (hR : R*Rinv=1) :
    degreeMass (L*T*R) = degreeMass T := by
  unfold degreeMass
  apply Finset.sum_congr rfl
  intro k _
  exact minorDegree_equivalent L Linv T R Rinv hL hR k.val

end WasowMinorInvariance
#print axioms WasowMinorInvariance.minorGCD_dvd_left_mul
#print axioms WasowMinorInvariance.minorGCD_dvd_right_mul
#print axioms WasowMinorInvariance.minorGCD_left_mul
#print axioms WasowMinorInvariance.minorGCD_right_mul
#print axioms WasowMinorInvariance.minorGCD_equivalent
#print axioms WasowMinorInvariance.minorDegree_equivalent

#print axioms WasowMinorInvariance.degreeMass_equivalent
