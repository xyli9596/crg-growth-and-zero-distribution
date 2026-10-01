import WasowJordanBasis
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Lex

/-! Jordan blocks can be genuinely enumerated in nondecreasing size order.
The order required by the determinantal-divisor descent is constructed, not
added as an assumption on the original matrix. -/
set_option autoImplicit false
noncomputable section
open Module Module.End
namespace WasowSortedJordan

/-- Sort a finite family by its values, breaking ties by a finite enumeration. -/
theorem exists_sorted_equiv {σ : Type*} [Fintype σ] (h : σ → ℕ) :
    ∃ e : Fin (Fintype.card σ) ≃ σ, Monotone (h ∘ e) := by
  let f : σ → Lex (ℕ × Fin (Fintype.card σ)) := fun a => toLex (h a, Fintype.equivFin σ a)
  have hf : Function.Injective f := by
    intro a b hab
    exact (Fintype.equivFin σ).injective (congrArg (fun x => (ofLex x).2) hab)
  let : LinearOrder σ := LinearOrder.lift' f hf
  let e := monoEquivOfFin σ rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  have hh : f (e i) ≤ f (e j) := e.monotone hij
  rcases Prod.Lex.le_iff.mp hh with hh | hh
  · exact hh.le
  · exact hh.1.le

/-- Permuting whole chains preserves their actual Jordan-shift matrix. -/
theorem jordanShift_reindex {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]
    (h : σ → ℕ) (e : τ ≃ σ) :
    (WasowMultiShiftReduction.jordanShift h).submatrix
      (Equiv.sigmaCongrLeft e) (Equiv.sigmaCongrLeft e) =
        WasowMultiShiftReduction.jordanShift (h ∘ e) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases hab : a=b
  · subst b
    simp [WasowMultiShiftReduction.jordanShift, Matrix.submatrix]
  · have he : e a ≠ e b := fun hh => hab (e.injective hh)
    simp [WasowMultiShiftReduction.jordanShift, Matrix.submatrix,
      Matrix.blockDiagonal'_apply_ne _ _ _ hab, Matrix.blockDiagonal'_apply_ne _ _ _ he]

/-- A nilpotent operator has an actual Jordan basis with sorted chain lengths. -/
theorem exists_sorted_jordan_basis {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : End ℂ V) (hf : IsNilpotent f) :
    ∃ (s : ℕ) (h : Fin s → ℕ), Monotone h ∧
      ∃ b : Basis (WasowMultiShiftReduction.Index h) ℂ V,
        LinearMap.toMatrix b b f = WasowMultiShiftReduction.jordanShift h := by
  classical
  obtain ⟨σ, fσ, dσ, h, b, hb⟩ := WasowJordanBasis.exists_jordan_basis f hf
  let := fσ
  let := dσ
  obtain ⟨e, he⟩ := exists_sorted_equiv h
  let E := Equiv.sigmaCongrLeft (β := fun a => Fin (h a+1)) e
  refine ⟨Fintype.card σ, h ∘ e, he, b.reindex E.symm, ?_⟩
  calc
    LinearMap.toMatrix (b.reindex E.symm) (b.reindex E.symm) f =
        (LinearMap.toMatrix b b f).submatrix E E := by
      ext i j
      simp [LinearMap.toMatrix_apply, Basis.reindex_apply]
    _ = _ := by rw [hb]; exact jordanShift_reindex h e

/-- Sorted actual matrix coordinates, with both inverse identities. -/
theorem exists_sorted_jordan_matrix_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : IsNilpotent A) :
    ∃ (s : ℕ) (h : Fin s → ℕ), Monotone h ∧
      ∃ (P : Matrix ι (WasowMultiShiftReduction.Index h) ℂ)
        (Q : Matrix (WasowMultiShiftReduction.Index h) ι ℂ),
        P * Q = 1 ∧ Q * P = 1 ∧
          Q * A * P = WasowMultiShiftReduction.jordanShift h := by
  have hnil : IsNilpotent (Matrix.toLin' A) := by
    exact hA.map (Matrix.toLinAlgEquiv (Pi.basisFun ℂ ι))
  obtain ⟨s, h, hh, b, hb⟩ := exists_sorted_jordan_basis (Matrix.toLin' A) hnil
  refine ⟨s, h, hh, (Pi.basisFun ℂ ι).toMatrix b, b.toMatrix (Pi.basisFun ℂ ι),
    Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩
  have hx := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    b (Pi.basisFun ℂ ι) b (Pi.basisFun ℂ ι) (Matrix.toLin' A)
  simpa only [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', hb] using hx

#print axioms exists_sorted_equiv
#print axioms jordanShift_reindex
#print axioms exists_sorted_jordan_basis
#print axioms exists_sorted_jordan_matrix_coordinates
end WasowSortedJordan
