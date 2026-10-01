import WasowFormalSeries
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Actual generalized-eigenspace coordinates for an arbitrary finite-dimensional
complex linear operator. No block decomposition or Jordan basis is assumed. -/
set_option autoImplicit false
noncomputable section
namespace WasowLeadingBlocks
open Module
open scoped DirectSum
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

abbrev Eigenvalues (f : End ℂ V) := f.Eigenvalues

def blockSpace (f : End ℂ V) (a : Eigenvalues f) : Submodule ℂ V :=
  f.maxGenEigenspace a.val

omit [FiniteDimensional ℂ V] in
/-- Every selected block is nonzero; zero-dimensional blocks are omitted. -/
theorem blockSpace_ne_bot (f : End ℂ V) (a : Eigenvalues f) : blockSpace f a ≠ ⊥ :=
  a.property.le le_top

/-- The sum is a genuine internal direct sum, not merely a spanning family. -/
theorem internal_blocks (f : End ℂ V) : DirectSum.IsInternal (blockSpace f) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact f.independent_maxGenEigenspace.comp Subtype.val_injective
  · apply top_unique
    rw [← f.iSup_maxGenEigenspace_eq_top]
    apply iSup_le
    intro μ
    by_cases hμ : f.HasEigenvalue μ
    · exact le_iSup (blockSpace f) ⟨μ, hμ⟩
    · have hbot : f.maxGenEigenspace μ = ⊥ := by
        by_contra hn
        exact hμ (Module.End.HasUnifEigenvalue.lt zero_lt_one hn)
      rw [hbot]
      exact bot_le

/-- The exact direct-sum coordinate equivalence. -/
def directSumEquiv (f : End ℂ V) : (⨁ a : Eigenvalues f, blockSpace f a) ≃ₗ[ℂ] V :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (blockSpace f)) (internal_blocks f)

/-- Positive block dimensions in the successor form required by formal recursion. -/
def blockSize (f : End ℂ V) (a : Eigenvalues f) : ℕ :=
  finrank ℂ (blockSpace f a) - 1

theorem block_finrank (f : End ℂ V) (a : Eigenvalues f) :
    finrank ℂ (blockSpace f a) = blockSize f a + 1 := by
  have : Nontrivial (blockSpace f a) := Submodule.nontrivial_iff_ne_bot.mpr (blockSpace_ne_bot f a)
  have hp : 0 < finrank ℂ (blockSpace f a) := Module.finrank_pos
  dsimp [blockSize]
  omega

def blockBasis (f : End ℂ V) (a : Eigenvalues f) :
    Basis (Fin (blockSize f a + 1)) ℂ (blockSpace f a) :=
  Module.finBasisOfFinrankEq ℂ (blockSpace f a) (block_finrank f a)

/-- An actual basis of the original space, indexed exactly as the formal theorem. -/
def basis (f : End ℂ V) : Basis (WasowMultiShiftReduction.Index (blockSize f)) ℂ V :=
  (internal_blocks f).collectedBasis (blockBasis f)

/-- The basis itself provides an invertible coordinate change. -/
def coordinates (f : End ℂ V) : V ≃ₗ[ℂ] (WasowMultiShiftReduction.Index (blockSize f) → ℂ) :=
  (basis f).equivFun

omit [FiniteDimensional ℂ V] in
theorem block_invariant (f : End ℂ V) (a : Eigenvalues f) :
    Set.MapsTo f (blockSpace f a) (blockSpace f a) :=
  f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) a.val

def restriction (f : End ℂ V) (a : Eigenvalues f) : End ℂ (blockSpace f a) :=
  f.restrict (block_invariant f a)

/-- Nilpotence holds inside each entire generalized eigenspace, allowing all
multiplicities and any number of Jordan blocks for the same eigenvalue. -/
theorem restriction_sub_nilpotent (f : End ℂ V) (a : Eigenvalues f) :
    IsNilpotent (restriction f a - algebraMap ℂ (End ℂ (blockSpace f a)) a.val) := by
  let g : End ℂ (blockSpace f a) :=
    (f - algebraMap ℂ (End ℂ V) a.val).restrict
      (f.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f a.val) a.val)
  have hg : IsNilpotent g := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap a.val
  have heq : g = restriction f a - algebraMap ℂ (End ℂ (blockSpace f a)) a.val := by
    ext x
    rfl
  rwa [heq] at hg

def nilpotentBlock (f : End ℂ V) (a : Eigenvalues f) :
    Matrix (Fin (blockSize f a + 1)) (Fin (blockSize f a + 1)) ℂ :=
  LinearMap.toMatrix (blockBasis f a) (blockBasis f a)
    (restriction f a - algebraMap ℂ (End ℂ (blockSpace f a)) a.val)

theorem nilpotentBlock_isNilpotent (f : End ℂ V) (a : Eigenvalues f) :
    IsNilpotent (nilpotentBlock f a) := by
  exact (restriction_sub_nilpotent f a).map (LinearMap.toMatrixAlgEquiv (blockBasis f a))

/-- The newly constructed basis puts the arbitrary operator into the precise
leading form consumed by `exists_multiblock_powerSeries`. -/
theorem toMatrix_eq_leading (f : End ℂ V) :
    LinearMap.toMatrix (basis f) (basis f) f =
      WasowMultiBlockReduction.leading (blockSize f) (fun a => a.val) (nilpotentBlock f) := by
  rw [basis, LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal'
    (internal_blocks f) (internal_blocks f) (blockBasis f) (blockBasis f) (block_invariant f)]
  congr 1
  funext a
  simp [nilpotentBlock, restriction, map_sub, Algebra.algebraMap_eq_smul_one]


omit [FiniteDimensional ℂ V] in
/-- Distinct block labels always carry distinct eigenvalues. -/
theorem eigenvalues_injective (f : End ℂ V) :
    Function.Injective (fun a : Eigenvalues f => a.val) := Subtype.val_injective

section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev MatrixIndex (A : Matrix ι ι ℂ) :=
  WasowMultiShiftReduction.Index (blockSize (Matrix.toLin' A))

/-- Columns of the generalized-eigenspace basis in the original coordinates. -/
def changeMatrix (A : Matrix ι ι ℂ) : Matrix ι (MatrixIndex A) ℂ :=
  (Pi.basisFun ℂ ι).toMatrix (basis (Matrix.toLin' A))

/-- The actual inverse coordinate matrix. -/
def inverseChangeMatrix (A : Matrix ι ι ℂ) : Matrix (MatrixIndex A) ι ℂ :=
  (basis (Matrix.toLin' A)).toMatrix (Pi.basisFun ℂ ι)

theorem change_mul_inverse (A : Matrix ι ι ℂ) :
    changeMatrix A * inverseChangeMatrix A = 1 := by
  exact Basis.toMatrix_mul_toMatrix_flip _ _

theorem inverse_mul_change (A : Matrix ι ι ℂ) :
    inverseChangeMatrix A * changeMatrix A = 1 := by
  exact Basis.toMatrix_mul_toMatrix_flip _ _

/-- Exact conjugation of any complex matrix to distinct eigenvalue blocks.
Both coordinate matrices have already been proved to be mutual inverses. -/
theorem matrix_conjugation (A : Matrix ι ι ℂ) :
    inverseChangeMatrix A * A * changeMatrix A =
      WasowMultiBlockReduction.leading (blockSize (Matrix.toLin' A))
        (fun a => a.val) (nilpotentBlock (Matrix.toLin' A)) := by
  calc
    _ = LinearMap.toMatrix (basis (Matrix.toLin' A)) (basis (Matrix.toLin' A))
        (Matrix.toLin' A) := by
      have hh := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
        (basis (Matrix.toLin' A)) (Pi.basisFun ℂ ι)
        (basis (Matrix.toLin' A)) (Pi.basisFun ℂ ι) (Matrix.toLin' A)
      simpa only [changeMatrix, inverseChangeMatrix, LinearMap.toMatrix_eq_toMatrix',
        LinearMap.toMatrix'_toLin'] using hh
    _ = _ := toMatrix_eq_leading (Matrix.toLin' A)

/-- Multiplicative coefficient transport, suitable for `PowerSeries.map`. -/
def matrixCoordinates (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ ≃ₐ[ℂ] Matrix (MatrixIndex A) (MatrixIndex A) ℂ :=
  (Matrix.toLinAlgEquiv (Pi.basisFun ℂ ι)).trans
    (LinearMap.toMatrixAlgEquiv (basis (Matrix.toLin' A)))

theorem matrixCoordinates_apply (A B : Matrix ι ι ℂ) :
    matrixCoordinates A B = inverseChangeMatrix A * B * changeMatrix A := by
  change LinearMap.toMatrix (basis (Matrix.toLin' A)) (basis (Matrix.toLin' A))
    (Matrix.toLin' B) = _
  have hh := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    (basis (Matrix.toLin' A)) (Pi.basisFun ℂ ι)
    (basis (Matrix.toLin' A)) (Pi.basisFun ℂ ι) (Matrix.toLin' B)
  simpa only [changeMatrix, inverseChangeMatrix, LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin'] using hh.symm

theorem matrixCoordinates_leading (A : Matrix ι ι ℂ) :
    matrixCoordinates A A = WasowMultiBlockReduction.leading (blockSize (Matrix.toLin' A))
      (fun a => a.val) (nilpotentBlock (Matrix.toLin' A)) := by
  rw [matrixCoordinates_apply, matrix_conjugation]

end Matrix

#print axioms blockSpace_ne_bot
#print axioms internal_blocks
#print axioms block_finrank
#print axioms block_invariant
#print axioms restriction_sub_nilpotent
#print axioms nilpotentBlock_isNilpotent
#print axioms toMatrix_eq_leading
#print axioms eigenvalues_injective
#print axioms change_mul_inverse
#print axioms inverse_mul_change
#print axioms matrix_conjugation
#print axioms matrixCoordinates_apply
#print axioms matrixCoordinates_leading
end WasowLeadingBlocks
