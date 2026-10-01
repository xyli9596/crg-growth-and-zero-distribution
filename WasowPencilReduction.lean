import WasowPencilCoefficients
import WasowMultiShiftReduction
import WasowPencilElimination
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fin.Tuple.Basic

/-! Actual polynomial coordinate transformations reducing a normalized
last-row matrix pencil to its smaller polynomial presentation. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Module Polynomial
open scoped BigOperators Matrix
namespace WasowPencilReduction
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

abbrev OldIndex (h : σ → ℕ) := WasowMultiShiftReduction.Index h
abbrev Interior (h : σ → ℕ) := Σ a, Fin (h a)
abbrev NewIndex (h : σ → ℕ) := Interior h ⊕ σ

/-- Columns e₁,...,e_h,(1,X,...,X^h), with e₀ omitted. -/
def columnEquiv (h : σ → ℕ) :
    (NewIndex h → ℂ[X]) ≃ₗ[ℂ[X]] (OldIndex h → ℂ[X]) where
  toFun v p :=
    (if hp : 0 < p.2.val then v (.inl ⟨p.1, ⟨p.2.val - 1, by have := p.2.isLt; omega⟩⟩) else 0) +
      X ^ p.2.val * v (.inr p.1)
  invFun w := Sum.elim
    (fun p => w ⟨p.1, p.2.succ⟩ - X ^ (p.2.val + 1) * w ⟨p.1, 0⟩)
    (fun a => w ⟨a, 0⟩)
  left_inv v := by
    funext p
    cases p with
    | inl p => rcases p with ⟨a, i⟩; simp
    | inr a => simp
  right_inv w := by
    funext ⟨a, i⟩
    by_cases hi : 0 < i.val
    · simp only [hi, dif_pos, Sum.elim_inl, Sum.elim_inr]
      have heq : (⟨i.val - 1, by omega⟩ : Fin (h a)).succ = i := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [heq]
      have hexp : i.val - 1 + 1 = i.val := by omega
      rw [hexp]
      ring
    · have hi0 : i = 0 := Fin.ext (show i.val = 0 by omega)
      subst i
      simp
  map_add' v w := by
    funext ⟨a, i⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp; ring
  map_smul' c v := by
    funext ⟨a, i⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [smul_eq_mul]; ring

/-- Reorder rows so all shift equations precede the last-row equations. -/
def rowIndexEquiv (h : σ → ℕ) : NewIndex h ≃ OldIndex h where
  toFun := Sum.elim (fun p => ⟨p.1, p.2.castSucc⟩) (fun a => ⟨a, Fin.last (h a)⟩)
  invFun p := Fin.lastCases (.inr p.1) (fun i => .inl ⟨p.1, i⟩) p.2
  left_inv p := by cases p <;> simp
  right_inv p := by
    rcases p with ⟨a, i⟩
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

def rowEquiv (h : σ → ℕ) :
    (OldIndex h → ℂ[X]) ≃ₗ[ℂ[X]] (NewIndex h → ℂ[X]) :=
  LinearEquiv.funCongrLeft ℂ[X] ℂ[X] (rowIndexEquiv h)

def rightMatrix (h : σ → ℕ) : Matrix (OldIndex h) (NewIndex h) ℂ[X] :=
  LinearMap.toMatrix' (columnEquiv h).toLinearMap

def rightInverse (h : σ → ℕ) : Matrix (NewIndex h) (OldIndex h) ℂ[X] :=
  LinearMap.toMatrix' (columnEquiv h).symm.toLinearMap

def rowMatrix (h : σ → ℕ) : Matrix (NewIndex h) (OldIndex h) ℂ[X] :=
  LinearMap.toMatrix' (rowEquiv h).toLinearMap

def rowInverse (h : σ → ℕ) : Matrix (OldIndex h) (NewIndex h) ℂ[X] :=
  LinearMap.toMatrix' (rowEquiv h).symm.toLinearMap

theorem right_mul_inverse (h : σ → ℕ) : rightMatrix h * rightInverse h = 1 := by
  apply Matrix.toLin'.injective
  simp [rightMatrix, rightInverse, Matrix.toLin'_mul]

theorem inverse_mul_right (h : σ → ℕ) : rightInverse h * rightMatrix h = 1 := by
  apply Matrix.toLin'.injective
  simp [rightMatrix, rightInverse, Matrix.toLin'_mul]

theorem row_mul_inverse (h : σ → ℕ) : rowMatrix h * rowInverse h = 1 := by
  apply Matrix.toLin'.injective
  simp [rowMatrix, rowInverse, Matrix.toLin'_mul]

theorem inverse_mul_row (h : σ → ℕ) : rowInverse h * rowMatrix h = 1 := by
  apply Matrix.toLin'.injective
  simp [rowMatrix, rowInverse, Matrix.toLin'_mul]

/-- Only the actual first h rows of each block are prescribed; the last rows
are arbitrary and will become the smaller polynomial presentation. -/
def LastRowForm (h : σ → ℕ) (C : Matrix (OldIndex h) (OldIndex h) ℂ) : Prop :=
  ∀ a (i : Fin (h a)) j, C ⟨a, i.castSucc⟩ j = if j = ⟨a, i.succ⟩ then 1 else 0

def pencil {h : σ → ℕ} (C : Matrix (OldIndex h) (OldIndex h) ℂ) :
    Matrix (OldIndex h) (OldIndex h) ℂ[X] := (X : ℂ[X]) • 1 - C.map Polynomial.C

def presentation {h : σ → ℕ} (C : Matrix (OldIndex h) (OldIndex h) ℂ) : Matrix σ σ ℂ[X] :=
  fun a b => (if a = b then X ^ (h a + 1) else 0) -
    WasowPencilCoefficients.rowPolynomial (fun j => C ⟨a, Fin.last (h a)⟩ ⟨b, j⟩)

/-- The normalized rows act as X v_i-v_(i+1). -/
theorem pencil_mulVec_top {h : σ → ℕ} {C : Matrix (OldIndex h) (OldIndex h) ℂ}
    (hC : LastRowForm h C) (v : OldIndex h → ℂ[X]) (a : σ) (i : Fin (h a)) :
    (pencil C *ᵥ v) ⟨a, i.castSucc⟩ = X * v ⟨a, i.castSucc⟩ - v ⟨a, i.succ⟩ := by
  unfold pencil
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  change X * v ⟨a, i.castSucc⟩ - ((C.map Polynomial.C) *ᵥ v) ⟨a, i.castSucc⟩ = _
  congr 1
  change ∑ b, Polynomial.C (C ⟨a, i.castSucc⟩ b) * v b = v ⟨a, i.succ⟩
  rw [Finset.sum_eq_single (⟨a, i.succ⟩ : OldIndex h)]
  · simp only [hC a i _, ite_true, map_one, one_mul]
  · intro b _ hb
    simp only [hC a i b, if_neg hb, map_zero, zero_mul]
  · simp


omit [Fintype σ] [DecidableEq σ] in
theorem column_zero (h : σ → ℕ) (v : NewIndex h → ℂ[X]) (a : σ) :
    columnEquiv h v ⟨a, 0⟩ = v (.inr a) := by
  simp [columnEquiv]

omit [Fintype σ] [DecidableEq σ] in
theorem column_succ (h : σ → ℕ) (v : NewIndex h → ℂ[X]) (a : σ) (i : Fin (h a)) :
    columnEquiv h v ⟨a, i.succ⟩ = v (.inl ⟨a, i⟩) + X^(i.val+1) * v (.inr a) := by
  simp [columnEquiv]

omit [Fintype σ] in
theorem column_single_right (h : σ → ℕ) (a b : σ) (i : Fin (h a+1)) :
    columnEquiv h (Pi.single (.inr b) 1) ⟨a, i⟩ = if a = b then X^i.val else 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [column_zero]
    simp [Pi.single_apply]
  · rw [column_succ]
    simp [Pi.single_apply]

omit [Fintype σ] in
theorem column_single_left (h : σ → ℕ) (a b : σ) (i : Fin (h a+1)) (j : Fin (h b)) :
    columnEquiv h (Pi.single (.inl ⟨b, j⟩) 1) ⟨a, i⟩ =
      if (⟨a, i⟩ : OldIndex h) = ⟨b, j.succ⟩ then 1 else 0 := by
  refine Fin.cases ?_ (fun l => ?_) i
  · rw [column_zero]
    have hn : (⟨a, 0⟩ : OldIndex h) ≠ ⟨b, j.succ⟩ := by
      intro hh
      have hab : a = b := congrArg Sigma.fst hh
      subst b
      have hh' : (0 : Fin (h a+1)) = j.succ := by simpa using hh
      have := congrArg Fin.val hh'
      simp at this
    simp [hn]
  · rw [column_succ]
    by_cases hab : a = b
    · subst b
      simp [Pi.single_apply, eq_comm]
    · have hn : (⟨a, l.succ⟩ : OldIndex h) ≠ ⟨b, j.succ⟩ := by
        intro hh
        exact hab (congrArg Sigma.fst hh)
      have hn' : (⟨b, j⟩ : Interior h) ≠ ⟨a, l⟩ := by
        intro hh
        exact hab (congrArg Sigma.fst hh).symm
      simp [hn, hn']

def afterColumns {h : σ → ℕ} (C : Matrix (OldIndex h) (OldIndex h) ℂ) :
    Matrix (NewIndex h) (NewIndex h) ℂ[X] := rowMatrix h * pencil C * rightMatrix h

theorem afterColumns_apply {h : σ → ℕ} (C : Matrix (OldIndex h) (OldIndex h) ℂ)
    (r c : NewIndex h) :
    afterColumns C r c =
      (pencil C *ᵥ columnEquiv h (Pi.single c 1)) (rowIndexEquiv h r) := by
  have hh : afterColumns C r c =
      Matrix.toLin' (afterColumns C) (Pi.single c 1) r := by
    rw [← LinearMap.toMatrix'_apply, LinearMap.toMatrix'_toLin']
  rw [hh]
  simp only [afterColumns, Matrix.toLin'_mul, rowMatrix, rightMatrix,
    Matrix.toLin'_toMatrix', LinearMap.comp_apply, Matrix.toLin'_apply]
  rfl


/-- The chain columns kill all normalized shift rows exactly. -/
theorem afterColumns_top_right {h : σ → ℕ} {C : Matrix (OldIndex h) (OldIndex h) ℂ}
    (hC : LastRowForm h C) (a b : σ) (i : Fin (h a)) :
    afterColumns C (.inl ⟨a, i⟩) (.inr b) = 0 := by
  rw [afterColumns_apply]
  change (pencil C *ᵥ columnEquiv h (Pi.single (.inr b) 1)) ⟨a, i.castSucc⟩ = 0
  rw [pencil_mulVec_top hC, column_single_right, column_single_right]
  by_cases hab : a = b
  · subst b
    simp [pow_succ, mul_comm]
  · simp [hab]

/-- The remaining entries are exactly the polynomials of the original last rows. -/
theorem afterColumns_bottom_right {h : σ → ℕ}
    (C : Matrix (OldIndex h) (OldIndex h) ℂ) (a b : σ) :
    afterColumns C (.inr a) (.inr b) = presentation C a b := by
  rw [afterColumns_apply]
  change (pencil C *ᵥ columnEquiv h (Pi.single (.inr b) 1)) ⟨a, Fin.last (h a)⟩ = _
  unfold pencil
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.map_apply, column_single_right, Fin.val_last,
    ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single b]
  · simp only [ite_true]
    rw [presentation, WasowPencilCoefficients.rowPolynomial_eq_sum_C_mul_X_pow]
    by_cases hab : a = b
    · subst b
      simp only [ite_true]
      rw [pow_succ, mul_comm X (X ^ h a)]
    · simp only [if_neg hab, mul_zero]
  · intro c hcb
    simp [hcb]


/-- The surviving upper-left block is a universal unit, independent of the last rows. -/
theorem afterColumns_top_left {h : σ → ℕ} {C : Matrix (OldIndex h) (OldIndex h) ℂ}
    (hC : LastRowForm h C) (a b : σ) (i : Fin (h a)) (j : Fin (h b)) :
    afterColumns C (.inl ⟨a, i⟩) (.inl ⟨b, j⟩) =
      Matrix.blockDiagonal' (fun a => WasowPencilElimination.localB (h a)) ⟨a, i⟩ ⟨b, j⟩ := by
  rw [afterColumns_apply]
  change (pencil C *ᵥ columnEquiv h (Pi.single (.inl ⟨b, j⟩) 1)) ⟨a, i.castSucc⟩ = _
  rw [pencil_mulVec_top hC, column_single_left, column_single_left]
  by_cases hab : a = b
  · subst b
    rw [Matrix.blockDiagonal'_apply_eq]
    unfold WasowPencilElimination.localB
    have heq₁ : ((⟨a, i.castSucc⟩ : OldIndex h) = ⟨a, j.succ⟩) ↔ i.val = j.val+1 := by
      simp [Fin.ext_iff]
    have heq₂ : ((⟨a, i.succ⟩ : OldIndex h) = ⟨a, j.succ⟩) ↔ i = j := by simp
    simp only [heq₁, heq₂]
    split_ifs <;> ring
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab]
    have hn₁ : (⟨a, i.castSucc⟩ : OldIndex h) ≠ ⟨b, j.succ⟩ := fun hh =>
      hab (congrArg Sigma.fst hh)
    have hn₂ : (⟨a, i.succ⟩ : OldIndex h) ≠ ⟨b, j.succ⟩ := fun hh =>
      hab (congrArg Sigma.fst hh)
    simp only [if_neg hn₁, if_neg hn₂, mul_zero, sub_self]

/-- Exact block form of the original pencil under actual invertible coordinate changes. -/
theorem afterColumns_eq {h : σ → ℕ} {C : Matrix (OldIndex h) (OldIndex h) ℂ}
    (hC : LastRowForm h C) :
    rowMatrix h * pencil C * rightMatrix h =
      Matrix.fromBlocks (Matrix.blockDiagonal' (fun a => WasowPencilElimination.localB (h a)))
        0 (afterColumns C).toBlocks₂₁ (presentation C) := by
  change afterColumns C = _
  apply Matrix.ext
  intro r c
  cases r with
  | inl r =>
    rcases r with ⟨a, i⟩
    cases c with
    | inl c => rcases c with ⟨b, j⟩; exact afterColumns_top_left hC a b i j
    | inr b => exact afterColumns_top_right hC a b i
  | inr a =>
    cases c with
    | inl c => rfl
    | inr b => exact afterColumns_bottom_right C a b


/-- A complete, genuinely invertible left/right reduction of the original
matrix pencil. The small matrix is computed from the original last rows. -/
theorem exists_pencil_reduction {h : σ → ℕ} {C : Matrix (OldIndex h) (OldIndex h) ℂ}
    (hC : LastRowForm h C) :
    ∃ (L : Matrix (NewIndex h) (OldIndex h) ℂ[X])
      (LInv : Matrix (OldIndex h) (NewIndex h) ℂ[X])
      (R : Matrix (OldIndex h) (NewIndex h) ℂ[X])
      (RInv : Matrix (NewIndex h) (OldIndex h) ℂ[X]),
      LInv * L = 1 ∧ L * LInv = 1 ∧ R * RInv = 1 ∧ RInv * R = 1 ∧
      L * pencil C * R = Matrix.fromBlocks 1 0 0 (presentation C) := by
  let B := Matrix.blockDiagonal' (fun a => WasowPencilElimination.localB (h a))
  let F := (afterColumns C).toBlocks₂₁
  let E := WasowPencilElimination.elimination B⁻¹ F
  let EInv := WasowPencilElimination.eliminationInverse B F
  obtain ⟨hBl, hBr⟩ := WasowPencilElimination.auxiliary_inverse h
  have hEE : EInv * E = 1 ∧ E * EInv = 1 :=
    WasowPencilElimination.elimination_inverse B B⁻¹ F hBl hBr
  refine ⟨E * rowMatrix h, rowInverse h * EInv, rightMatrix h, rightInverse h,
    ?_, ?_, right_mul_inverse h, inverse_mul_right h, ?_⟩
  · calc
      (rowInverse h * EInv) * (E * rowMatrix h) =
          rowInverse h * (EInv * E) * rowMatrix h := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hEE.1, Matrix.mul_one, inverse_mul_row]
  · calc
      (E * rowMatrix h) * (rowInverse h * EInv) =
          E * (rowMatrix h * rowInverse h) * EInv := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [row_mul_inverse, Matrix.mul_one, hEE.2]
  · calc
      (E * rowMatrix h) * pencil C * rightMatrix h =
          E * (rowMatrix h * pencil C * rightMatrix h) := by simp only [Matrix.mul_assoc]
      _ = E * Matrix.fromBlocks B 0 F (presentation C) := by rw [afterColumns_eq hC]
      _ = _ := WasowPencilElimination.elimination_mul B B⁻¹ F (presentation C) hBl

omit [Fintype σ] in
/-- Off-diagonal entries have the precise coefficient form used in degree descent. -/
theorem presentation_offDiagonal {h : σ → ℕ}
    (C : Matrix (OldIndex h) (OldIndex h) ℂ) (a b : σ) (hab : a ≠ b) :
    presentation C a b = -WasowPencilCoefficients.rowPolynomial
      (fun j => C ⟨a, Fin.last (h a)⟩ ⟨b, j⟩) := by
  simp [presentation, hab]

omit [Fintype σ] in
/-- A shift diagonal block has zero last row, hence contributes exactly X^(h+1). -/
theorem presentation_diagonal {h : σ → ℕ}
    (C : Matrix (OldIndex h) (OldIndex h) ℂ) (a : σ)
    (ha : ∀ j, C ⟨a, Fin.last (h a)⟩ ⟨a, j⟩ = 0) :
    presentation C a a = X ^ (h a+1) := by
  simp [presentation, WasowPencilCoefficients.rowPolynomial, ha]

omit [Fintype σ] in
/-- Every actual nonzero off-diagonal last row survives with the required strict degree bound. -/
theorem presentation_offDiagonal_nonzero_degree {h : σ → ℕ}
    (C : Matrix (OldIndex h) (OldIndex h) ℂ) (a b : σ) (hab : a ≠ b)
    (hn : ∃ j, C ⟨a, Fin.last (h a)⟩ ⟨b, j⟩ ≠ 0) :
    presentation C a b ≠ 0 ∧ (presentation C a b).natDegree < h b + 1 := by
  rw [presentation_offDiagonal C a b hab]
  exact WasowPencilCoefficients.neg_rowPolynomial_nonzero_degree _ hn

#print axioms right_mul_inverse
#print axioms inverse_mul_right
#print axioms row_mul_inverse
#print axioms inverse_mul_row
#print axioms pencil_mulVec_top
#print axioms column_zero
#print axioms column_succ
#print axioms column_single_right
#print axioms column_single_left
#print axioms afterColumns_apply
#print axioms afterColumns_top_right
#print axioms afterColumns_bottom_right
#print axioms afterColumns_top_left
#print axioms afterColumns_eq
#print axioms exists_pencil_reduction
#print axioms presentation_offDiagonal
#print axioms presentation_diagonal
#print axioms presentation_offDiagonal_nonzero_degree
end WasowPencilReduction
