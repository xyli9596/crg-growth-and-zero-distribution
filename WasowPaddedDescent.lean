import WasowMinorEquivalence

/-! The strict polynomial-pencil decrease at its original full dimension.
Auxiliary unit blocks contribute zero exponents and are retained explicitly. -/
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
namespace WasowPaddedDescent
open WasowReductionDescent

def padded {s : ℕ} (d : ℕ) (T : Matrix (Fin s) (Fin s) (Polynomial ℂ)) :
    Matrix (Fin (d+s)) (Fin (d+s)) (Polynomial ℂ) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) (Polynomial ℂ)) 0 0 T)

def paddedDegrees {s : ℕ} (d : ℕ) (m : Fin s → ℕ) : Fin (d+s) → ℕ :=
  Fin.addCases (fun _ => 0) m

/-- Ordering the auxiliary zeros first preserves the sorted exponent list. -/
theorem paddedDegrees_monotone {s : ℕ} (d : ℕ) (m : Fin s → ℕ) (hm : Monotone m) :
    Monotone (paddedDegrees d m) := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · intro j _
    simp only [paddedDegrees, Fin.addCases_left]
    exact Nat.zero_le _
  · intro j
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j
    · intro hab
      have : (Fin.natAdd d a).val ≤ (Fin.castAdd s b).val := hab
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    · intro hab
      simp only [paddedDegrees, Fin.addCases_right]
      apply hm
      have hh : (Fin.natAdd d a).val ≤ (Fin.natAdd d b).val := hab
      change a.val ≤ b.val
      simpa only [Fin.val_natAdd, Nat.add_le_add_iff_left] using hh

/-- The actual block diagonal padding is lower triangular in the displayed order. -/
theorem padded_lowerTriangular {s : ℕ} (d : ℕ)
    (T : Matrix (Fin s) (Fin s) (Polynomial ℂ)) (hT : T.IsLowerTriangular) :
    (padded d T).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  revert j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · intro j
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j
    · intro hab
      have hne : a ≠ b := by intro he; subst b; exact lt_irrefl _ hab
      simp [padded, Matrix.reindex_apply, hne]
    · intro _
      simp [padded, Matrix.reindex_apply]
  · intro j
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j
    · intro hab
      simp [padded, Matrix.reindex_apply]
    · intro hab
      have hh : a < b := by
        change (Fin.natAdd d a).val < (Fin.natAdd d b).val at hab
        change a.val < b.val
        simpa only [Fin.val_natAdd, Nat.add_lt_add_iff_left] using hab
      simpa [padded, Matrix.reindex_apply] using hT hh

/-- The diagonal is exactly zero-exponent units followed by the reduced diagonal. -/
theorem padded_diagonal {s : ℕ} (d : ℕ)
    (T : Matrix (Fin s) (Fin s) (Polynomial ℂ)) (m : Fin s → ℕ)
    (hdiag : ∀ i, T i i = X^m i) (i : Fin (d+s)) :
    padded d T i i = X^(paddedDegrees d m i) := by
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · simp [padded, paddedDegrees, Matrix.reindex_apply]
  · simp [padded, paddedDegrees, Matrix.reindex_apply, hdiag]

/-- An actual reduced entry remains the same entry after adjoining the unit block. -/
theorem padded_entry {s : ℕ} (d : ℕ)
    (T : Matrix (Fin s) (Fin s) (Polynomial ℂ)) (a b : Fin s) :
    padded d T (Fin.natAdd d a) (Fin.natAdd d b) = T a b := by
  simp [padded, Matrix.reindex_apply]

/-- The strict degree-mass drop holds in the original dimension, with all
auxiliary unit blocks explicitly included. -/
theorem padded_degreeMass_strict_drop {s : ℕ} (d : ℕ)
    (T : Matrix (Fin s) (Fin s) (Polynomial ℂ)) (hT : T.IsLowerTriangular)
    (m : Fin s → ℕ) (hm : Monotone m) (hdiag : ∀ i, T i i = X^m i)
    (hentry : ∃ ℓ a, T a ℓ ≠ 0 ∧ (T a ℓ).natDegree < m ℓ) :
    degreeMass (padded d T) <
      degreeMass (Matrix.diagonal (fun i => (X : Polynomial ℂ)^(paddedDegrees d m i))) := by
  apply degreeMass_strict_drop (padded d T) (padded_lowerTriangular d T hT)
    (paddedDegrees d m) (paddedDegrees_monotone d m hm) (padded_diagonal d T m hdiag)
  obtain ⟨ℓ,a,hne,hdeg⟩ := hentry
  refine ⟨Fin.natAdd d ℓ, Fin.natAdd d a, ?_, ?_⟩
  · simpa only [padded_entry] using hne
  · simpa only [padded_entry, paddedDegrees, Fin.addCases_right] using hdeg

end WasowPaddedDescent
#print axioms WasowPaddedDescent.paddedDegrees_monotone
#print axioms WasowPaddedDescent.padded_lowerTriangular
#print axioms WasowPaddedDescent.padded_diagonal
#print axioms WasowPaddedDescent.padded_entry
#print axioms WasowPaddedDescent.padded_degreeMass_strict_drop
