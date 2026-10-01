import WasowShiftReduction
import Mathlib.Data.Matrix.Block

/-! All-order formal row normalization for any finite family of nilpotent
Jordan shift blocks. Each rectangular coefficient equation is solved using the
proved row recurrence, then assembled into the actual full matrix equation.
A leading matrix in the given Jordan-block coordinates is the only normal-form
hypothesis; neither a formal gauge nor a future reduction is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowMultiShiftReduction
open WasowShiftReduction

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Each block has positive size `h a + 1`; the whole family may be empty. -/
abbrev Index (h : σ → ℕ) := Σ a, Fin (h a + 1)

/-- The actual dependent block diagonal matrix of nilpotent shifts. -/
def jordanShift (h : σ → ℕ) : Matrix (Index h) (Index h) ℂ :=
  Matrix.blockDiagonal' (fun a => shift (h a))

/-- Extract the rectangular block with row block `a` and column block `b`. -/
def block {h : σ → ℕ} (P : Matrix (Index h) (Index h) ℂ) (a b : σ) :
    Matrix (Fin (h a + 1)) (Fin (h b + 1)) ℂ :=
  fun i j => P ⟨a, i⟩ ⟨b, j⟩

/-- Assemble all rectangular blocks, including off-diagonal ones. -/
def assemble {h : σ → ℕ}
    (P : ∀ a b, Matrix (Fin (h a + 1)) (Fin (h b + 1)) ℂ) :
    Matrix (Index h) (Index h) ℂ :=
  fun i j => P i.1 j.1 i.2 j.2

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem block_assemble {h : σ → ℕ}
    (P : ∀ a b, Matrix (Fin (h a + 1)) (Fin (h b + 1)) ℂ) (a b : σ) :
    block (assemble P) a b = P a b := rfl

/-- Left multiplication selects exactly the corresponding row shift block. -/
theorem block_jordanShift_mul (h : σ → ℕ)
    (P : Matrix (Index h) (Index h) ℂ) (a b : σ) :
    block (jordanShift h * P) a b = shift (h a) * block P a b := by
  ext i j
  simp only [block, jordanShift, Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro c hca
    apply Finset.sum_eq_zero
    intro l hl
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hca.symm, zero_mul]

/-- Right multiplication selects exactly the corresponding column shift block. -/
theorem block_mul_jordanShift (h : σ → ℕ)
    (P : Matrix (Index h) (Index h) ℂ) (a b : σ) :
    block (P * jordanShift h) a b = block P a b * shift (h b) := by
  ext i j
  simp only [block, jordanShift, Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single b]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro c hcb
    apply Finset.sum_eq_zero
    intro l hl
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hcb, mul_zero]

/-- An actual full coefficient step for arbitrary many shift blocks. The first
row of every gauge block vanishes; only the last row of each transformed block
is allowed to remain. Existence, rather than an unnecessary uniqueness claim,
is the conclusion. -/
theorem exists_multishift_step (h : σ → ℕ)
    (H : Matrix (Index h) (Index h) ℂ) :
    ∃ P B : Matrix (Index h) (Index h) ℂ,
      (∀ a b j, P ⟨a, 0⟩ ⟨b, j⟩ = 0) ∧
      (∀ a b i j, i.val < h a → B ⟨a, i⟩ ⟨b, j⟩ = 0) ∧
      jordanShift h * P - P * jordanShift h = B + H := by
  choose p b hp hb heq using fun a b =>
    exists_rectangular_step (shift (h b)) (block H a b)
  refine ⟨assemble p, assemble b, ?_, ?_, ?_⟩
  · intro a c j
    exact hp a c j
  · intro a c i j hi
    exact hb a c i j hi
  · ext ⟨a, i⟩ ⟨c, j⟩
    change (block (jordanShift h * assemble p) a c) i j -
      (block (assemble p * jordanShift h) a c) i j =
      b a c i j + (block H a c) i j
    rw [block_jordanShift_mul, block_mul_jordanShift, block_assemble]
    exact congrFun (congrFun (heq a c) i) j

/-- The complete formal coefficient recursion for an arbitrary finite family
of nilpotent shift blocks. Constant coefficients are retained, and the row
normalizations apply to every positive order. -/
theorem exists_formal_multishift_reduction (h : σ → ℕ)
    (A : ℕ → Matrix (Index h) (Index h) ℂ)
    (hA : A 0 = jordanShift h) {q : ℕ} (hq : 0 < q) :
    ∃ P B : ℕ → Matrix (Index h) (Index h) ℂ,
      P 0 = 1 ∧ B 0 = A 0 ∧
      (∀ k a b j, P (k + 1) ⟨a, 0⟩ ⟨b, j⟩ = 0) ∧
      (∀ k a b i j, i.val < h a → B (k + 1) ⟨a, i⟩ ⟨b, j⟩ = 0) ∧
      ∀ k, (∑ i ∈ Finset.range (k + 1),
        (A (k - i) * P i - P i * B (k - i))) =
          -WasowFormalRecurrence.derivativeCoeff q P k := by
  apply WasowRecurrencePrinciple.exists_formal_reduction_of_step A hq
    (fun p => ∀ a b j, p ⟨a, 0⟩ ⟨b, j⟩ = 0)
    (fun b => ∀ a c i j, i.val < h a → b ⟨a, i⟩ ⟨c, j⟩ = 0)
  intro H
  simpa only [hA] using exists_multishift_step h H

end WasowMultiShiftReduction
#print axioms WasowMultiShiftReduction.block_assemble
#print axioms WasowMultiShiftReduction.block_jordanShift_mul
#print axioms WasowMultiShiftReduction.block_mul_jordanShift
#print axioms WasowMultiShiftReduction.exists_multishift_step
#print axioms WasowMultiShiftReduction.exists_formal_multishift_reduction
