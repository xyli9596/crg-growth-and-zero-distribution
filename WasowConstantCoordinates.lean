import WasowJordanBasis
import WasowGaugeComposition

/-! Constant matrices have actual Jordan coordinates with integer weights.
The off-diagonal entries connect equal eigenvalues and decrease the weight
by one. This includes repeated eigenvalues and nontrivial Jordan blocks. -/
set_option autoImplicit false
noncomputable section
open Matrix Module
open scoped BigOperators
namespace WasowConstantCoordinates

theorem exists_weighted_coordinates {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    ∃ (C : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℂ) (k : Fin m → ℤ),
      C.det ≠ 0 ∧
      (∀ i, (C⁻¹ * A * C) i i = μ i) ∧
      (∀ i j, i ≠ j → (C⁻¹ * A * C) i j ≠ 0 →
        μ i = μ j ∧ k j - k i = -1) := by
  classical
  let f := Matrix.toLin' A
  obtain ⟨τ, fτ, dτ, h, b, hb⟩ := WasowJordanBasis.exists_generalized_jordan_basis f
  let _ := fτ
  let _ := dτ
  let I := Σ a : WasowLeadingBlocks.Eigenvalues f, WasowMultiShiftReduction.Index (h a)
  let e : I ≃ Fin m := Fintype.equivOfCardEq (by
    rw [← Module.finrank_eq_card_basis b]
    simp)
  let b' := b.reindex e
  let C := (Pi.basisFun ℂ (Fin m)).toMatrix b'
  let Q := b'.toMatrix (Pi.basisFun ℂ (Fin m))
  have hCQ : C * Q = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hQC : Q * C = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hC : C.det ≠ 0 := by
    have hd := congrArg Matrix.det hCQ
    rw [Matrix.det_mul, Matrix.det_one] at hd
    intro hz
    rw [hz, zero_mul] at hd
    exact zero_ne_one hd
  have hi : C⁻¹ = Q := by
    calc
      C⁻¹ = C⁻¹ * (C * Q) := by rw [hCQ, Matrix.mul_one]
      _ = Q := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.mpr hC), Matrix.one_mul]
  have hJ : C⁻¹ * A * C =
      (Matrix.blockDiagonal' (fun a : WasowLeadingBlocks.Eigenvalues f =>
        a.val • 1 + WasowMultiShiftReduction.jordanShift (h a))).submatrix e.symm e.symm := by
    rw [hi]
    have hc := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      b' (Pi.basisFun ℂ (Fin m)) b' (Pi.basisFun ℂ (Fin m)) f
    have he : LinearMap.toMatrix b' b' f = (LinearMap.toMatrix b b f).submatrix e.symm e.symm := by
      ext i j
      simp [b', LinearMap.toMatrix_apply, Basis.reindex_apply]
    simpa only [C, Q, f, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', he, hb] using hc
  refine ⟨C, (fun i => (e.symm i).1.val), (fun i => -((e.symm i).2.2.val : ℤ)), hC, ?_, ?_⟩
  · intro i
    rw [hJ]
    rcases he : e.symm i with ⟨a,c,u⟩
    simp [Matrix.submatrix, he, WasowMultiShiftReduction.jordanShift,
      WasowShiftReduction.shift, Matrix.blockDiagonal'_apply_eq]
  · intro i j hij hnon
    rw [hJ] at hnon
    rcases hi' : e.symm i with ⟨a,c,u⟩
    rcases hj' : e.symm j with ⟨b,d,v⟩
    have hne : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    by_cases hab : a = b
    · subst b
      by_cases hcd : c = d
      · subst d
        have huv : u ≠ v := by
          intro hh
          apply hne
          simp [hi', hj', hh]
        have hv : v.val = u.val + 1 := by
          by_contra hn
          exact hnon (by simp [Matrix.submatrix, hi', hj',
            WasowMultiShiftReduction.jordanShift, WasowShiftReduction.shift,
            Matrix.blockDiagonal'_apply_eq, huv, hn])
        constructor
        · simp [hi', hj']
        · change -((e.symm j).2.2.val : ℤ) - -((e.symm i).2.2.val : ℤ) = -1
          rw [hi', hj']
          change -(v.val : ℤ) - -(u.val : ℤ) = -1
          omega
      · have hcu : (⟨c,u⟩ : WasowMultiShiftReduction.Index (h a)) ≠ ⟨d,v⟩ := by
          intro hh
          exact hcd (congrArg Sigma.fst hh)
        exact (hnon (by simp [Matrix.submatrix, hi', hj', hcu,
          WasowMultiShiftReduction.jordanShift,
          Matrix.blockDiagonal'_apply_ne _ _ _ hcd])).elim
    · exact (hnon (by simp [Matrix.submatrix, hi', hj',
        Matrix.blockDiagonal'_apply_ne _ _ _ hab])).elim

#print axioms exists_weighted_coordinates
end WasowConstantCoordinates
