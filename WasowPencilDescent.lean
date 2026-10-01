import WasowPencilReduction
import WasowPaddedDescent

/-! Actual determinantal-degree descent for the original normalized constant
matrix pencil, using proved polynomial coordinate transformations. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace WasowPencilDescent
open WasowPencilReduction WasowPencilCoefficients WasowReductionDescent

/-- The same invariant on any finite coordinate type, with orders 0 through dimension. -/
def degreeMass {ι : Type*} [Fintype ι] (T : Matrix ι ι ℂ[X]) : ℕ :=
  ∑ k : Fin (Fintype.card ι + 1), (minorGCD T k.val).natDegree

theorem degreeMass_fin {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ[X]) :
    degreeMass T = WasowReductionDescent.degreeMass T := by
  unfold degreeMass WasowReductionDescent.degreeMass
  rw [Fintype.card_fin]

theorem degreeMass_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : Matrix ι ι ℂ[X]) (e : κ ≃ ι) :
    degreeMass (T.submatrix e e) = degreeMass T := by
  unfold degreeMass
  simp_rw [WasowMinorEquivalence.minorGCD_reindex]
  rw [Fintype.card_congr e]

/-- The invariant of the original pencil is exactly that of the proved smaller
presentation with its auxiliary identity block retained. -/
theorem degreeMass_pencil {σ : Type*} [Fintype σ] [DecidableEq σ]
    {h : σ → ℕ} {C : Matrix (OldIndex h) (OldIndex h) ℂ} (hC : LastRowForm h C) :
    degreeMass (pencil C) =
      degreeMass (Matrix.fromBlocks (1 : Matrix (Interior h) (Interior h) ℂ[X]) 0 0 (presentation C)) := by
  obtain ⟨L, Li, R, Ri, hLiL, _, hRRi, _, he⟩ := exists_pencil_reduction hC
  have hminor (k : ℕ) : minorGCD (pencil C) k =
      minorGCD (Matrix.fromBlocks (1 : Matrix (Interior h) (Interior h) ℂ[X]) 0 0 (presentation C)) k := by
    have hh := WasowMinorEquivalence.minorGCD_equivalent L Li (pencil C) R Ri hLiL hRRi k
    rw [he] at hh
    exact hh.symm
  unfold degreeMass
  simp_rw [hminor]
  rw [← Fintype.card_congr (rowIndexEquiv h)]

/-- Arbitrary auxiliary indices may be numbered without changing the invariant. -/
theorem degreeMass_fromBlocks {κ : Type*} [Fintype κ] [DecidableEq κ] {s : ℕ}
    (T : Matrix (Fin s) (Fin s) ℂ[X]) :
    degreeMass (Matrix.fromBlocks (1 : Matrix κ κ ℂ[X]) 0 0 T) =
      WasowReductionDescent.degreeMass (WasowPaddedDescent.padded (Fintype.card κ) T) := by
  let e : Fin (Fintype.card κ) ⊕ Fin s ≃ κ ⊕ Fin s :=
    Equiv.sumCongr (Fintype.equivFin κ).symm (Equiv.refl _)
  have he : (Matrix.fromBlocks (1 : Matrix κ κ ℂ[X]) 0 0 T).submatrix e e =
      Matrix.fromBlocks (1 : Matrix (Fin (Fintype.card κ)) (Fin (Fintype.card κ)) ℂ[X]) 0 0 T := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> simp [e, Matrix.submatrix, Matrix.fromBlocks, Matrix.one_apply]
  rw [← degreeMass_reindex _ e, he]
  rw [← degreeMass_reindex _ (finSumFinEquiv.symm)]
  change degreeMass (WasowPaddedDescent.padded (Fintype.card κ) T) = _
  exact degreeMass_fin _

/-- Padding a diagonal monomial presentation only adds zero exponents. -/
theorem padded_diagonal {s : ℕ} (d : ℕ) (m : Fin s → ℕ) :
    WasowPaddedDescent.padded d (Matrix.diagonal (fun i => (X : ℂ[X]) ^ m i)) =
      Matrix.diagonal (fun i => (X : ℂ[X]) ^ WasowPaddedDescent.paddedDegrees d m i) := by
  apply Matrix.ext
  intro i j
  revert j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · intro j
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
      simp [WasowPaddedDescent.padded, WasowPaddedDescent.paddedDegrees,
        Matrix.reindex_apply, Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff]
      ; omega
  · intro j
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
      simp [WasowPaddedDescent.padded, WasowPaddedDescent.paddedDegrees,
        Matrix.reindex_apply, Matrix.diagonal_apply, Fin.ext_iff]
      ; omega

/-- The original Jordan pencil satisfies exactly the normalization assumptions. -/
theorem jordan_lastRowForm {σ : Type*} [Fintype σ] [DecidableEq σ] (h : σ → ℕ) :
    LastRowForm h (WasowMultiShiftReduction.jordanShift h) := by
  intro a i j
  rcases j with ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    simp [WasowMultiShiftReduction.jordanShift, WasowShiftReduction.shift, Fin.ext_iff]
  · have hn : (⟨b, j⟩ : OldIndex h) ≠ ⟨a, i.succ⟩ := fun hh =>
      hab (congrArg Sigma.fst hh).symm
    simp [WasowMultiShiftReduction.jordanShift, Matrix.blockDiagonal'_apply_ne _ _ _ hab, hn]

theorem jordan_lastRow_zero {σ : Type*} [Fintype σ] [DecidableEq σ] (h : σ → ℕ)
    (a b : σ) (j : Fin (h b+1)) :
    WasowMultiShiftReduction.jordanShift h ⟨a, Fin.last (h a)⟩ ⟨b, j⟩ = 0 := by
  by_cases hab : a = b
  · subst b
    have hj : j.val ≠ h a + 1 := by omega
    simp [WasowMultiShiftReduction.jordanShift, WasowShiftReduction.shift, hj]
  · exact Matrix.blockDiagonal'_apply_ne _ _ _ hab

theorem presentation_jordan {σ : Type*} [Fintype σ] [DecidableEq σ] (h : σ → ℕ) :
    presentation (WasowMultiShiftReduction.jordanShift h) =
      Matrix.diagonal (fun a => (X : ℂ[X]) ^ (h a+1)) := by
  apply Matrix.ext
  intro a b
  simp [presentation, rowPolynomial, jordan_lastRow_zero, Matrix.diagonal_apply]


/-- The structural conditions refer to the actual constant matrix blocks. -/
def LowerBlocks {s : ℕ} (h : Fin s → ℕ)
    (C : Matrix (OldIndex h) (OldIndex h) ℂ) : Prop :=
  ∀ a b, a < b → ∀ i j, C ⟨a, i⟩ ⟨b, j⟩ = 0

def ShiftDiagonal {s : ℕ} (h : Fin s → ℕ)
    (C : Matrix (OldIndex h) (OldIndex h) ℂ) : Prop :=
  ∀ a i j, C ⟨a, i⟩ ⟨a, j⟩ = WasowShiftReduction.shift (h a) i j

theorem presentation_lower {s : ℕ} {h : Fin s → ℕ}
    {C : Matrix (OldIndex h) (OldIndex h) ℂ} (hL : LowerBlocks h C) :
    (presentation C).IsLowerTriangular := by
  intro a b hab
  change a < b at hab
  rw [presentation_offDiagonal C a b (ne_of_lt hab)]
  apply neg_eq_zero.mpr
  exact (rowPolynomial_eq_zero_iff _).mpr (fun j => hL a b hab _ j)

theorem presentation_diag {s : ℕ} {h : Fin s → ℕ}
    {C : Matrix (OldIndex h) (OldIndex h) ℂ} (hD : ShiftDiagonal h C) (a : Fin s) :
    presentation C a a = X ^ (h a+1) := by
  apply presentation_diagonal C a
  intro j
  rw [hD a]
  have hj : j.val ≠ h a+1 := by omega
  simp [WasowShiftReduction.shift, hj]

/-- The actual pencil invariant equals the numbered, padded presentation invariant. -/
theorem degreeMass_pencil_model {s : ℕ} {h : Fin s → ℕ}
    {C : Matrix (OldIndex h) (OldIndex h) ℂ} (hC : LastRowForm h C) :
    degreeMass (pencil C) = WasowReductionDescent.degreeMass
      (WasowPaddedDescent.padded (Fintype.card (Interior h)) (presentation C)) := by
  rw [degreeMass_pencil hC, degreeMass_fromBlocks]

theorem degreeMass_jordan_model {s : ℕ} (h : Fin s → ℕ) :
    degreeMass (pencil (WasowMultiShiftReduction.jordanShift h)) =
      WasowReductionDescent.degreeMass
        (Matrix.diagonal (fun i => (X : ℂ[X]) ^
          WasowPaddedDescent.paddedDegrees (Fintype.card (Interior h)) (fun a => h a+1) i)) := by
  rw [degreeMass_pencil_model (jordan_lastRowForm h), presentation_jordan, padded_diagonal]

/-- Weak descent requires no ordering of block sizes and no nonzero entry hypothesis. -/
theorem pencil_degreeMass_le {s : ℕ} {h : Fin s → ℕ}
    {C : Matrix (OldIndex h) (OldIndex h) ℂ}
    (hC : LastRowForm h C) (hL : LowerBlocks h C) (hD : ShiftDiagonal h C) :
    degreeMass (pencil C) ≤ degreeMass (pencil (WasowMultiShiftReduction.jordanShift h)) := by
  rw [degreeMass_pencil_model hC, degreeMass_jordan_model]
  unfold WasowReductionDescent.degreeMass
  apply Finset.sum_le_sum
  intro k _
  exact minor_degree_le_diagonal (by omega) _
    (WasowPaddedDescent.padded_lowerTriangular _ _ (presentation_lower hL)) _
    (WasowPaddedDescent.padded_diagonal _ _ _ (presentation_diag hD))

/-- Strict descent of the original constant-matrix pencil, deduced from an
actual nonzero off-diagonal last row and the proved polynomial equivalence. -/
theorem pencil_degreeMass_strict_drop {s : ℕ} {h : Fin s → ℕ}
    {C : Matrix (OldIndex h) (OldIndex h) ℂ}
    (hh : Monotone h) (hC : LastRowForm h C) (hL : LowerBlocks h C) (hD : ShiftDiagonal h C)
    (hn : ∃ a b, a ≠ b ∧ ∃ j, C ⟨a, Fin.last (h a)⟩ ⟨b, j⟩ ≠ 0) :
    degreeMass (pencil C) < degreeMass (pencil (WasowMultiShiftReduction.jordanShift h)) := by
  rw [degreeMass_pencil_model hC, degreeMass_jordan_model]
  apply WasowPaddedDescent.padded_degreeMass_strict_drop _ _ (presentation_lower hL)
    (fun a => h a+1) (fun a b hab => Nat.add_le_add_right (hh hab) 1) (presentation_diag hD)
  obtain ⟨a, b, hab, j, hj⟩ := hn
  exact ⟨b, a, presentation_offDiagonal_nonzero_degree C a b hab ⟨j, hj⟩⟩

#print axioms degreeMass_fin
#print axioms degreeMass_reindex
#print axioms degreeMass_pencil
#print axioms degreeMass_fromBlocks
#print axioms padded_diagonal
#print axioms jordan_lastRowForm
#print axioms jordan_lastRow_zero
#print axioms presentation_jordan
#print axioms presentation_lower
#print axioms presentation_diag
#print axioms degreeMass_pencil_model
#print axioms degreeMass_jordan_model
#print axioms pencil_degreeMass_le
#print axioms pencil_degreeMass_strict_drop
end WasowPencilDescent
