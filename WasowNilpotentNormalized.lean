import WasowShiftReduction
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! A normalized companion-shaped matrix cannot have nonzero last-row
feedback if it is nilpotent. This supplies the diagonal-block conclusion in
Wasow Lemma 19.3 without assuming a companion characteristic-polynomial formula. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowNilpotentNormalized

theorem nilpotent_pow_size {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (hC : IsNilpotent C) : C^n = 0 := by
  have hp : C.charpoly = Polynomial.X^n := by
    have hh := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hC
    simpa only [Fintype.card_fin, sub_eq_zero] using hh.eq_zero
  have he := Matrix.aeval_self_charpoly C
  simpa only [hp, map_pow, Polynomial.aeval_X] using he

/-- Before reaching the last row, the zeroth row of a power walks along
the actual superdiagonal chain. -/
theorem pow_first_row {h : ℕ} (C : Matrix (Fin (h+1)) (Fin (h+1)) ℂ)
    (hrows : ∀ i j, i.val < h →
      C i j = if j.val = i.val+1 then 1 else 0)
    (k : ℕ) (hk : k ≤ h) (j : Fin (h+1)) :
    (C^k) 0 j = if j.val = k then 1 else 0 := by
  induction k generalizing j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Fin.ext_iff, Fin.val_zero]
    exact if_congr (eq_comm) rfl rfl
  | succ k ih =>
    have hkh : k ≤ h := by omega
    have hkl : k < h := by omega
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih hkh]
    rw [Fintype.sum_eq_single (⟨k,by omega⟩ : Fin (h+1))]
    · simpa using hrows (⟨k,by omega⟩ : Fin (h+1)) j hkl
    · intro l hne
      have hl : l.val ≠ k := fun he => hne (Fin.ext he)
      simp [hl]

/-- A nilpotent normalized block has zero last row, hence is exactly the
original shift. Nilpotence is an input, the vanishing last row is proved. -/
theorem nilpotent_normalized_eq_shift {h : ℕ}
    (C : Matrix (Fin (h+1)) (Fin (h+1)) ℂ)
    (hrows : ∀ i j, i.val < h →
      C i j = if j.val = i.val+1 then 1 else 0)
    (hC : IsNilpotent C) : C = WasowShiftReduction.shift h := by
  have hp := nilpotent_pow_size C hC
  have hlast : ∀ j, C (Fin.last h) j = 0 := by
    intro j
    have he : (C^(h+1)) 0 j = C (Fin.last h) j := by
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [pow_first_row C hrows h le_rfl]
      rw [Fintype.sum_eq_single (Fin.last h)]
      · simp
      · intro l hne
        have hl : l.val ≠ h := fun he => hne (Fin.ext he)
        simp [hl]
    rw [hp] at he
    exact he.symm
  ext i j
  by_cases hi : i.val < h
  · exact hrows i j hi
  · have hilast : i = Fin.last h := Fin.ext (by simp only [Fin.val_last]; omega)
    subst i
    rw [hlast]
    have hj : j.val ≠ h+1 := Nat.ne_of_lt j.isLt
    simp only [WasowShiftReduction.shift, Fin.val_last, if_neg hj]

/-- Diagonal translation of a normalized shift row. -/
def ShiftRows {h : ℕ} (N : Matrix (Fin (h+1)) (Fin (h+1)) ℂ) (α : ℂ) : Prop :=
  ∀ i j, i.val < h →
    N i j = (if j.val = i.val+1 then 1 else 0) - (if i=j then α else 0)

/-- Powers of the translated matrix form a triangular Krylov family with
unit diagonal; no characteristic-polynomial calculation is assumed. -/
theorem pow_first_row_triangular {h : ℕ}
    (N : Matrix (Fin (h+1)) (Fin (h+1)) ℂ) (α : ℂ) (hrows : ShiftRows N α)
    (k : ℕ) (hk : k ≤ h) :
    (∀ j, k < j.val → (N^k) 0 j = 0) ∧
      (N^k) 0 ⟨k,by omega⟩ = 1 := by
  induction k with
  | zero =>
    constructor
    · intro j hj
      simp only [pow_zero, Matrix.one_apply]
      rw [if_neg (fun he => by have := congrArg Fin.val he; simp at this; omega)]
    · simp
  | succ k ih =>
    have hkh : k ≤ h := by omega
    obtain ⟨hupper,hdiag⟩ := ih hkh
    constructor
    · intro j hj
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l.val ≤ k
      · have hlj : l ≠ j := by intro he; subst l; omega
        have hlj' : j.val ≠ l.val+1 := by omega
        rw [hrows l j (by omega), if_neg hlj', if_neg hlj]
        simp
      · rw [hupper l (by omega), zero_mul]
    · rw [pow_succ, Matrix.mul_apply]
      rw [Fintype.sum_eq_single (⟨k,by omega⟩ : Fin (h+1))]
      · rw [hdiag, one_mul, hrows _ _ (by simp; omega)]
        simp
      · intro l hlne
        by_cases hl : l.val ≤ k
        · have hlt : l.val < k := by
            have hne : l.val ≠ k := fun he => hlne (Fin.ext he)
            omega
          have hlj : l ≠ (⟨k+1,by omega⟩ : Fin (h+1)) := by
            intro he
            have heval : l.val = k+1 := congrArg Fin.val he
            omega
          have hlj' : k+1 ≠ l.val+1 := by omega
          rw [hrows l _ (by omega)]
          simp only [if_neg hlj', if_neg hlj, sub_self, mul_zero]
        · rw [hupper l (by omega), zero_mul]

def krylovRows {h : ℕ} (N : Matrix (Fin (h+1)) (Fin (h+1)) ℂ) :
    Matrix (Fin (h+1)) (Fin (h+1)) ℂ := fun i j => (N^i.val) 0 j

theorem krylovRows_det_one {h : ℕ}
    (N : Matrix (Fin (h+1)) (Fin (h+1)) ℂ) (α : ℂ) (hrows : ShiftRows N α) :
    (krylovRows N).det = 1 := by
  have ht : (krylovRows N).IsLowerTriangular := by
    intro i j hij
    exact (pow_first_row_triangular N α hrows i.val (by omega)).1 j hij
  rw [Matrix.det_of_isLowerTriangular _ ht]
  have hd : ∀ i, krylovRows N i i = 1 := by
    intro i
    exact (pow_first_row_triangular N α hrows i.val (by omega)).2
  simp only [hd, Finset.prod_const_one]

theorem krylovRows_last_column {h : ℕ}
    (N : Matrix (Fin (h+1)) (Fin (h+1)) ℂ) (α : ℂ) (hrows : ShiftRows N α)
    (i : Fin (h+1)) : krylovRows N i (Fin.last h) = if i=Fin.last h then 1 else 0 := by
  by_cases hi : i=Fin.last h
  · subst i
    rw [if_pos rfl]
    exact (pow_first_row_triangular N α hrows h le_rfl).2
  · rw [if_neg hi]
    apply (pow_first_row_triangular N α hrows i.val (by omega)).1
    have hne : i.val ≠ h := fun he => hi (Fin.ext he)
    simp only [Fin.val_last]
    omega

theorem krylovRows_intertwines {h : ℕ}
    (N : Matrix (Fin (h+1)) (Fin (h+1)) ℂ) (hN : IsNilpotent N) :
    krylovRows N * N = WasowShiftReduction.shift h * krylovRows N := by
  ext i j
  rw [WasowShiftReduction.shift_mul_apply]
  change (∑ l, (N^i.val) 0 l * N l j) = _
  rw [← Matrix.mul_apply, ← pow_succ]
  split_ifs with hi
  · rfl
  · have he : i.val=h := by omega
    rw [he, nilpotent_pow_size N hN]
    rfl

/-- A normalized block with one eigenvalue has a concrete determinant-one
similarity to the shift after subtracting that eigenvalue. The final-column
identity is included to preserve off-diagonal last-row normalizations. -/
theorem normalized_single_eigenvalue_similarity {h : ℕ}
    (C : Matrix (Fin (h+1)) (Fin (h+1)) ℂ) (α : ℂ)
    (hrows : ∀ i j, i.val < h →
      C i j = if j.val = i.val+1 then 1 else 0)
    (hN : IsNilpotent (C - α • 1)) :
    ∃ P Q : Matrix (Fin (h+1)) (Fin (h+1)) ℂ,
      P*Q=1 ∧ Q*P=1 ∧ P*(C-α • 1)*Q=WasowShiftReduction.shift h ∧
      (∀ i, P i (Fin.last h)=if i=Fin.last h then 1 else 0) := by
  let N := C-α • 1
  have hr : ShiftRows N α := by
    intro i j hi
    simp only [N, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      hrows i j hi]
    split_ifs <;> simp
  let P := krylovRows N
  have hdet : IsUnit P.det := by rw [krylovRows_det_one N α hr]; exact isUnit_one
  have hPQ : P*P⁻¹=1 := Matrix.mul_nonsing_inv _ hdet
  have hQP : P⁻¹*P=1 := Matrix.nonsing_inv_mul _ hdet
  refine ⟨P,P⁻¹,hPQ,hQP,?_,fun i => krylovRows_last_column N α hr i⟩
  change krylovRows N * N * P⁻¹ = _
  rw [krylovRows_intertwines N hN, Matrix.mul_assoc, hPQ, Matrix.mul_one]

/-- The explicit similarity preserves a rectangular last-row block on
its left, because its final column is the last standard vector. -/
theorem left_mul_last_row {h k : ℕ}
    (P : Matrix (Fin (h+1)) (Fin (h+1)) ℂ)
    (hP : ∀ i, P i (Fin.last h)=if i=Fin.last h then 1 else 0)
    (F : Matrix (Fin (h+1)) (Fin (k+1)) ℂ)
    (hF : ∀ i j, i.val < h → F i j=0) : P*F=F := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_eq_single (Fin.last h)]
  · rw [hP]
    split_ifs with hi
    · subst i; simp
    · have hilt : i.val < h := by
        have hne : i.val ≠ h := fun he => hi (Fin.ext he)
        omega
      rw [zero_mul,hF i j hilt]
  · intro l hl
    have hlt : l.val < h := by
      have hne : l.val ≠ h := fun he => hl (Fin.ext he)
      omega
    rw [hF l j hlt,mul_zero]

theorem right_mul_last_row {h k : ℕ}
    (F : Matrix (Fin (h+1)) (Fin (k+1)) ℂ)
    (Q : Matrix (Fin (k+1)) (Fin (k+1)) ℂ)
    (hF : ∀ i j, i.val < h → F i j=0) :
    ∀ i j, i.val < h → (F*Q) i j=0 := by
  intro i j hi
  simp only [Matrix.mul_apply,hF i _ hi,zero_mul,Finset.sum_const_zero]

theorem right_mul_nonzero {h k : ℕ}
    (F : Matrix (Fin (h+1)) (Fin (k+1)) ℂ)
    (Q P : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) (hQP : Q*P=1)
    (hF : F≠0) : F*Q≠0 := by
  intro hz
  apply hF
  calc
    F = F*(Q*P) := by rw [hQP,Matrix.mul_one]
    _ = 0 := by rw [← Matrix.mul_assoc,hz,Matrix.zero_mul]

#print axioms left_mul_last_row
#print axioms right_mul_last_row
#print axioms right_mul_nonzero
#print axioms pow_first_row_triangular
#print axioms krylovRows_det_one
#print axioms krylovRows_last_column
#print axioms krylovRows_intertwines
#print axioms normalized_single_eigenvalue_similarity
#print axioms nilpotent_pow_size
#print axioms pow_first_row
#print axioms nilpotent_normalized_eq_shift
end WasowNilpotentNormalized
