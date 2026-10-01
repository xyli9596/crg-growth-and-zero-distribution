import WasowMinorInvariance

/-! Determinantal divisors are invariant under actual polynomial coordinate
isomorphisms even when the source and target use different finite index types. -/
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace WasowMinorEquivalence
open WasowReductionDescent WasowMinorExpansion

/-- Rectangular row operations preserve divisibility by every common divisor
of the minors of the untransformed rectangular matrix. -/
theorem dvd_minor_left_product {R α β γ : Type*} [CommRing R]
    [Fintype α] [Fintype β] [Fintype γ]
    (A : Matrix α β R) (B : Matrix β γ R) (k : ℕ) (d : R)
    (hd : ∀ r : Fin k → β, ∀ c : Fin k → γ, d ∣ (B.submatrix r c).det)
    (r : Fin k → α) (c : Fin k → γ) : d ∣ ((A*B).submatrix r c).det := by
  classical
  rw [Matrix.submatrix_mul A B r id c Function.bijective_id, det_rectangular_mul]
  apply Finset.dvd_sum
  intro f _
  apply dvd_mul_of_dvd_right
  simpa only [Matrix.submatrix_submatrix, Function.id_comp, Function.comp_id] using hd f c

theorem dvd_minor_right_product {R α β γ : Type*} [CommRing R]
    [Fintype α] [Fintype β] [Fintype γ]
    (A : Matrix α β R) (B : Matrix β γ R) (k : ℕ) (d : R)
    (hd : ∀ r : Fin k → α, ∀ c : Fin k → β, d ∣ (A.submatrix r c).det)
    (r : Fin k → α) (c : Fin k → γ) : d ∣ ((A*B).submatrix r c).det := by
  classical
  have htrans : ∀ r : Fin k → β, ∀ c : Fin k → α,
      d ∣ (A.transpose.submatrix r c).det := by
    intro r c
    change d ∣ (A.submatrix c r).transpose.det
    simpa only [Matrix.det_transpose] using hd c r
  have hh := dvd_minor_left_product B.transpose A.transpose k d htrans c r
  rw [← Matrix.transpose_mul] at hh
  change d ∣ ((A*B).submatrix r c).transpose.det at hh
  simpa only [Matrix.det_transpose] using hh

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Two-sided coordinate changes with genuinely different finite index types. -/
theorem minorGCD_dvd_two_sided (L : Matrix κ ι (Polynomial ℂ))
    (T : Matrix ι ι (Polynomial ℂ)) (V : Matrix ι κ (Polynomial ℂ)) (k : ℕ) :
    minorGCD T k ∣ minorGCD (L*T*V) k := by
  rw [dvd_minorGCD_iff]
  exact dvd_minor_right_product (L*T) V k (minorGCD T k)
    (dvd_minor_left_product L T k (minorGCD T k) (minorGCD_dvd_minor T k))

/-- Exact invariance under concrete left and right polynomial inverses.
This applies directly to the sum-type coordinates of a Jordan pencil. -/
theorem minorGCD_equivalent [DecidableEq ι] (L : Matrix κ ι (Polynomial ℂ))
    (S : Matrix ι κ (Polynomial ℂ)) (T : Matrix ι ι (Polynomial ℂ))
    (V : Matrix ι κ (Polynomial ℂ)) (W : Matrix κ ι (Polynomial ℂ))
    (hL : S*L=1) (hV : V*W=1) (k : ℕ) :
    minorGCD (L*T*V) k = minorGCD T k := by
  classical
  have hnorm₁ : normalize (minorGCD (L*T*V) k) = minorGCD (L*T*V) k := Finset.normalize_gcd
  have hnorm₂ : normalize (minorGCD T k) = minorGCD T k := Finset.normalize_gcd
  apply dvd_antisymm_of_normalize_eq hnorm₁ hnorm₂
  · have hh := minorGCD_dvd_two_sided S (L*T*V) W k
    have he : S * (L*T*V) * W = T := by
      calc
        _ = (S*L)*T*(V*W) := by simp only [Matrix.mul_assoc]
        _ = T := by rw [hL,hV,Matrix.one_mul,Matrix.mul_one]
    rwa [he] at hh
  · exact minorGCD_dvd_two_sided L T V k

/-- Relabeling coordinates alone does not change any determinantal divisor. -/
theorem minorGCD_reindex (T : Matrix ι ι (Polynomial ℂ)) (e : κ ≃ ι) (k : ℕ) :
    minorGCD (T.submatrix e e) k = minorGCD T k := by
  classical
  have hnorm₁ : normalize (minorGCD (T.submatrix e e) k) = minorGCD (T.submatrix e e) k := Finset.normalize_gcd
  have hnorm₂ : normalize (minorGCD T k) = minorGCD T k := Finset.normalize_gcd
  apply dvd_antisymm_of_normalize_eq hnorm₁ hnorm₂
  · rw [dvd_minorGCD_iff]
    intro r c
    have hh := minorGCD_dvd_minor (T.submatrix e e) k (e.symm ∘ r) (e.symm ∘ c)
    simpa only [Matrix.submatrix_submatrix, Function.comp_def, Equiv.apply_symm_apply] using hh
  · rw [dvd_minorGCD_iff]
    intro r c
    simpa only [Matrix.submatrix_submatrix] using minorGCD_dvd_minor T k (e ∘ r) (e ∘ c)

end WasowMinorEquivalence
#print axioms WasowMinorEquivalence.dvd_minor_left_product
#print axioms WasowMinorEquivalence.dvd_minor_right_product
#print axioms WasowMinorEquivalence.minorGCD_dvd_two_sided
#print axioms WasowMinorEquivalence.minorGCD_equivalent
#print axioms WasowMinorEquivalence.minorGCD_reindex
