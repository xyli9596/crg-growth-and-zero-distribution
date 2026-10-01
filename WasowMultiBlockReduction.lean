import WasowMultiShiftReduction
import WasowFormalSylvester

/-! All-order splitting of any finite family of distinct eigenvalue blocks,
allowing arbitrary nilpotent parts and multiplicities inside each block.
The leading matrix is given in these generalized-eigenvector coordinates;
constructing those coordinates for an arbitrary matrix is a separate step. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowMultiBlockReduction
open WasowMultiShiftReduction
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Generic left multiplication by a dependent block diagonal matrix. -/
theorem block_diagonal_mul (h : σ → ℕ)
    (L : ∀ a, Matrix (Fin (h a+1)) (Fin (h a+1)) ℂ)
    (P : Matrix (Index h) (Index h) ℂ) (a b : σ) :
    block (Matrix.blockDiagonal' L * P) a b = L a * block P a b := by
  ext i j
  simp only [block, Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro c hca
    apply Finset.sum_eq_zero
    intro l hl
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hca.symm, zero_mul]

/-- Generic right multiplication by a dependent block diagonal matrix. -/
theorem block_mul_diagonal (h : σ → ℕ)
    (L : ∀ a, Matrix (Fin (h a+1)) (Fin (h a+1)) ℂ)
    (P : Matrix (Index h) (Index h) ℂ) (a b : σ) :
    block (P * Matrix.blockDiagonal' L) a b = block P a b * L b := by
  ext i j
  simp only [block, Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single b]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro c hcb
    apply Finset.sum_eq_zero
    intro l hl
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hcb, mul_zero]

def leading (h : σ → ℕ) (eigenvalue : σ → ℂ)
    (N : ∀ a, Matrix (Fin (h a+1)) (Fin (h a+1)) ℂ) : Matrix (Index h) (Index h) ℂ :=
  Matrix.blockDiagonal' (fun a => eigenvalue a • 1 + N a)

/-- Every off-diagonal rectangular equation is genuinely solved, then all
blocks are assembled into one full coefficient equation. -/
theorem exists_multiblock_step (h : σ → ℕ) (eigenvalue : σ → ℂ)
    (N : ∀ a, Matrix (Fin (h a+1)) (Fin (h a+1)) ℂ)
    (heigenvalue : Function.Injective eigenvalue) (hN : ∀ a, IsNilpotent (N a))
    (H : Matrix (Index h) (Index h) ℂ) :
    ∃ P B : Matrix (Index h) (Index h) ℂ,
      (∀ a i j, P ⟨a,i⟩ ⟨a,j⟩ = 0) ∧
      (∀ a b, a ≠ b → ∀ i j, B ⟨a,i⟩ ⟨b,j⟩ = 0) ∧
      leading h eigenvalue N * P - P * leading h eigenvalue N = B + H := by
  choose X hX huniq using fun (a b : σ) (hab : a ≠ b) =>
    WasowFormalSylvester.existsUnique_sylvester_of_nilpotent_parts
      (fun heq => hab (heigenvalue heq)) (hN a) (hN b) (block H a b)
  let p : ∀ a b, Matrix (Fin (h a+1)) (Fin (h b+1)) ℂ :=
    fun a b => if hab : a = b then 0 else X a b hab
  let P := assemble p
  let B : Matrix (Index h) (Index h) ℂ := Matrix.blockDiagonal' (fun a => -block H a a)
  have hpdiag (a : σ) : block P a a = 0 := by
    simp [P, block_assemble, p]
  have hpoff (a b : σ) (hab : a ≠ b) : block P a b = X a b hab := by
    simp [P, block_assemble, p, hab]
  refine ⟨P, B, ?_, ?_, ?_⟩
  · intro a i j
    exact congrFun (congrFun (hpdiag a) i) j
  · intro a b hab i j
    exact Matrix.blockDiagonal'_apply_ne _ _ _ hab
  · ext ⟨a,i⟩ ⟨b,j⟩
    change (block (leading h eigenvalue N * P) a b) i j -
      (block (P * leading h eigenvalue N) a b) i j = B ⟨a,i⟩ ⟨b,j⟩ + H ⟨a,i⟩ ⟨b,j⟩
    rw [leading, block_diagonal_mul, block_mul_diagonal]
    by_cases hab : a = b
    · subst b
      rw [hpdiag, Matrix.mul_zero, Matrix.zero_mul]
      simp [B, block]
    · rw [hpoff a b hab]
      have hb : B ⟨a,i⟩ ⟨b,j⟩ = 0 := Matrix.blockDiagonal'_apply_ne _ _ _ hab
      rw [hb, zero_add]
      exact congrFun (congrFun (hX a b hab) i) j

/-- All formal orders for an arbitrary finite family of eigenvalue blocks. -/
theorem exists_formal_multiblock_reduction (h : σ → ℕ) (eigenvalue : σ → ℂ)
    (N : ∀ a, Matrix (Fin (h a+1)) (Fin (h a+1)) ℂ)
    (heigenvalue : Function.Injective eigenvalue) (hN : ∀ a, IsNilpotent (N a))
    (A : ℕ → Matrix (Index h) (Index h) ℂ) (hA : A 0 = leading h eigenvalue N)
    {q : ℕ} (hq : 0 < q) :
    ∃ P B : ℕ → Matrix (Index h) (Index h) ℂ,
      P 0 = 1 ∧ B 0 = A 0 ∧
      (∀ k a i j, P (k+1) ⟨a,i⟩ ⟨a,j⟩ = 0) ∧
      (∀ k a b, a ≠ b → ∀ i j, B k ⟨a,i⟩ ⟨b,j⟩ = 0) ∧
      ∀ k, (∑ i ∈ Finset.range (k+1), (A (k-i) * P i - P i * B (k-i))) =
        -WasowFormalRecurrence.derivativeCoeff q P k := by
  obtain ⟨P,B,hP0,hB0,hP,hB,heq⟩ :=
    WasowRecurrencePrinciple.exists_formal_reduction_of_step A hq
      (fun p => ∀ a i j, p ⟨a,i⟩ ⟨a,j⟩ = 0)
      (fun b => ∀ a c, a ≠ c → ∀ i j, b ⟨a,i⟩ ⟨c,j⟩ = 0)
      (fun H => by simpa only [hA] using exists_multiblock_step h eigenvalue N heigenvalue hN H)
  refine ⟨P,B,hP0,hB0,hP,?_,heq⟩
  intro k
  cases k with
  | zero =>
    intro a b hab i j
    rw [hB0,hA]
    exact Matrix.blockDiagonal'_apply_ne _ _ _ hab
  | succ k => exact hB k

#print axioms block_diagonal_mul
#print axioms block_mul_diagonal
#print axioms exists_multiblock_step
#print axioms exists_formal_multiblock_reduction
end WasowMultiBlockReduction
