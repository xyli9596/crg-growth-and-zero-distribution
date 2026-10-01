import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic

/-! A constructive algebraic step for Wasow's formal block reduction.
Distinct scalar eigenvalues are allowed to have arbitrary nilpotent parts:
the Sylvester operator is a nonzero scalar plus a nilpotent operator. Its
invertibility follows from the finite geometric-series inverse for nilpotents.
This does not assert the formal or analytic normal-form existence theorem. -/
set_option autoImplicit false
noncomputable section
open Matrix
namespace WasowFormalSylvester

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Left multiplication on rectangular matrices, as a complex linear map. -/
def leftMul (A : Matrix m m ℂ) : Module.End ℂ (Matrix m n ℂ) where
  toFun X := A * X
  map_add' X Y := Matrix.mul_add A X Y
  map_smul' a X := Matrix.mul_smul A a X

/-- Right multiplication on the same rectangular matrix space. -/
def rightMul (B : Matrix n n ℂ) : Module.End ℂ (Matrix m n ℂ) where
  toFun X := X * B
  map_add' X Y := Matrix.add_mul X Y B
  map_smul' a X := Matrix.smul_mul a X B

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
@[simp] theorem leftMul_apply (A : Matrix m m ℂ) (X : Matrix m n ℂ) :
    leftMul A X = A * X := rfl

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
@[simp] theorem rightMul_apply (B : Matrix n n ℂ) (X : Matrix m n ℂ) :
    rightMul B X = X * B := rfl

omit [Fintype n] [DecidableEq n] in
/-- Matrix powers agree with powers of the left multiplication operator. -/
theorem leftMul_pow_apply (A : Matrix m m ℂ) (k : ℕ) (X : Matrix m n ℂ) :
    (leftMul A ^ k) X = A ^ k * X := by
  induction k generalizing X with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, leftMul_apply, ih, pow_succ, Matrix.mul_assoc]

omit [Fintype m] [DecidableEq m] in
/-- Right multiplication powers preserve the order of matrix multiplication. -/
theorem rightMul_pow_apply (B : Matrix n n ℂ) (k : ℕ) (X : Matrix m n ℂ) :
    (rightMul B ^ k) X = X * B ^ k := by
  induction k generalizing X with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, rightMul_apply, ih, pow_succ', Matrix.mul_assoc]

omit [DecidableEq m] [DecidableEq n] in
/-- Left and right multiplication commute even for nondiagonal blocks. -/
theorem leftMul_commute_rightMul (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    Commute (leftMul (n := n) A) (rightMul (m := m) B) := by
  apply LinearMap.ext
  intro X
  exact (Matrix.mul_assoc A X B).symm

omit [Fintype n] [DecidableEq n] in
theorem isNilpotent_leftMul {A : Matrix m m ℂ} (hA : IsNilpotent A) :
    IsNilpotent (leftMul (n := n) A) := by
  obtain ⟨k, hk⟩ := hA
  refine ⟨k, LinearMap.ext (fun X => ?_)⟩
  simp [leftMul_pow_apply, hk]

omit [Fintype m] [DecidableEq m] in
theorem isNilpotent_rightMul {B : Matrix n n ℂ} (hB : IsNilpotent B) :
    IsNilpotent (rightMul (m := m) B) := by
  obtain ⟨k, hk⟩ := hB
  refine ⟨k, LinearMap.ext (fun X => ?_)⟩
  simp [rightMul_pow_apply, hk]

/-- The Sylvester map for two possibly nondiagonal repeated-eigenvalue blocks. -/
def sylvester (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    Module.End ℂ (Matrix m n ℂ) := leftMul A - rightMul B

omit [DecidableEq m] [DecidableEq n] in
@[simp] theorem sylvester_apply (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (X : Matrix m n ℂ) : sylvester A B X = A * X - X * B := rfl

/-- The nilpotent parts may have any sizes and any Jordan block multiplicities. -/
theorem sylvester_scalar_parts (α β : ℂ) (N : Matrix m m ℂ) (M : Matrix n n ℂ) :
    sylvester (α • 1 + N) (β • 1 + M) =
      algebraMap ℂ (Module.End ℂ (Matrix m n ℂ)) (α - β) + sylvester N M := by
  apply LinearMap.ext
  intro X
  change (α • 1 + N) * X - X * (β • 1 + M) =
    (α - β) • X + (N * X - X * M)
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, sub_smul]
  abel

/-- Nonresonant Sylvester invertibility for arbitrary nilpotent blocks.
No invertibility or solvability of the Sylvester map is assumed. -/
theorem isUnit_sylvester_of_nilpotent_parts {α β : ℂ}
    (hαβ : α ≠ β) {N : Matrix m m ℂ} {M : Matrix n n ℂ}
    (hN : IsNilpotent N) (hM : IsNilpotent M) :
    IsUnit (sylvester (α • 1 + N) (β • 1 + M)) := by
  have hnil : IsNilpotent (sylvester N M) :=
    (leftMul_commute_rightMul N M).isNilpotent_sub
      (isNilpotent_leftMul hN) (isNilpotent_rightMul hM)
  have hscalar : IsUnit (algebraMap ℂ (Module.End ℂ (Matrix m n ℂ)) (α - β)) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hαβ)).map _
  have hcomm : Commute (sylvester N M)
      (algebraMap ℂ (Module.End ℂ (Matrix m n ℂ)) (α - β)) :=
    (Algebra.commutes (α - β) (sylvester N M)).symm
  rw [sylvester_scalar_parts]
  exact hnil.isUnit_add_left_of_commute hscalar hcomm

/-- The actual unique off-diagonal coefficient needed at every formal
block-reduction step exists, including repeated eigenvalues within each block. -/
theorem existsUnique_sylvester_of_nilpotent_parts {α β : ℂ}
    (hαβ : α ≠ β) {N : Matrix m m ℂ} {M : Matrix n n ℂ}
    (hN : IsNilpotent N) (hM : IsNilpotent M) (C : Matrix m n ℂ) :
    ∃! X : Matrix m n ℂ, (α • 1 + N) * X - X * (β • 1 + M) = C := by
  exact ((Module.End.isUnit_iff _).mp
    (isUnit_sylvester_of_nilpotent_parts hαβ hN hM)).existsUnique C

/-- One full coefficient step of Wasow's formal block reduction: the diagonal
part of the new gauge coefficient is zero and the transformed coefficient is
block diagonal. The residual `H` may be any matrix produced by earlier steps. -/
theorem exists_block_coefficient {α β : ℂ} (hαβ : α ≠ β)
    {N : Matrix m m ℂ} {M : Matrix n n ℂ}
    (hN : IsNilpotent N) (hM : IsNilpotent M)
    (H : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    ∃ X : Matrix m n ℂ, ∃ Y : Matrix n m ℂ,
      let A₀ := Matrix.fromBlocks (α • 1 + N) 0 0 (β • 1 + M)
      let P := Matrix.fromBlocks 0 X Y 0
      let B := Matrix.fromBlocks (-H.toBlocks₁₁) 0 0 (-H.toBlocks₂₂)
      A₀ * P - P * A₀ = B + H := by
  obtain ⟨X, hX, _⟩ := existsUnique_sylvester_of_nilpotent_parts hαβ hN hM H.toBlocks₁₂
  obtain ⟨Y, hY, _⟩ := existsUnique_sylvester_of_nilpotent_parts hαβ.symm hM hN H.toBlocks₂₁
  refine ⟨X, Y, ?_⟩
  dsimp only
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.fromBlocks, Matrix.toBlocks₁₁]
  · simpa [Matrix.fromBlocks, Matrix.toBlocks₁₂] using congrFun (congrFun hX i) j
  · simpa [Matrix.fromBlocks, Matrix.toBlocks₂₁] using congrFun (congrFun hY i) j
  · simp [Matrix.fromBlocks, Matrix.toBlocks₂₂]

#print axioms leftMul_apply
#print axioms rightMul_apply
#print axioms leftMul_pow_apply
#print axioms rightMul_pow_apply
#print axioms leftMul_commute_rightMul
#print axioms isNilpotent_leftMul
#print axioms isNilpotent_rightMul
#print axioms sylvester_apply
#print axioms sylvester_scalar_parts
#print axioms isUnit_sylvester_of_nilpotent_parts
#print axioms existsUnique_sylvester_of_nilpotent_parts
#print axioms exists_block_coefficient
end WasowFormalSylvester
