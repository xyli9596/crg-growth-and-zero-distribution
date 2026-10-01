import WasowRecurrencePrinciple

/-! A constructive resonant normalization for one nilpotent shift block.
The rectangular solver works with an arbitrary matrix on the right. It fixes
the first gauge row to zero and allows the last transformed row to absorb the
remaining residual. Only the needed existence claim is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowShiftReduction

/-- The nilpotent Jordan shift of size `h+1`, with ones on the superdiagonal. -/
def shift (h : ℕ) : Matrix (Fin (h + 1)) (Fin (h + 1)) ℂ :=
  fun i j => if j.val = i.val + 1 then 1 else 0

theorem shift_mul_apply {h k : ℕ}
    (P : Matrix (Fin (h + 1)) (Fin k) ℂ) (i : Fin (h + 1)) (j : Fin k) :
    (shift h * P) i j = if hi : i.val < h then P ⟨i.val + 1, by omega⟩ j else 0 := by
  split_ifs with hi
  · let next : Fin (h + 1) := ⟨i.val + 1, by omega⟩
    rw [Matrix.mul_apply, Finset.sum_eq_single next]
    · simp [shift, next]
    · intro l hl hlnext
      have hval : l.val ≠ i.val + 1 := by
        intro heq
        apply hlnext
        exact Fin.ext heq
      simp [shift, hval]
    · simp
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l hl
    have hval : l.val ≠ i.val + 1 := by omega
    simp [shift, hval]

/-- Successive gauge rows are obtained by a finite forward recurrence. The
clipped source index only totalizes this function beyond the rows used below. -/
def rows {h k : ℕ} (K : Matrix (Fin k) (Fin k) ℂ)
    (H : Matrix (Fin (h + 1)) (Fin k) ℂ) : ℕ → (Fin k → ℂ)
  | 0 => 0
  | r + 1 => Matrix.vecMul (rows K H r) K + H ⟨min r h, by omega⟩

/-- Every rectangular residual admits a normalized resonant coefficient step.
There is no spectral or Jordan assumption on the right coefficient `K`. -/
theorem exists_rectangular_step {h k : ℕ} (K : Matrix (Fin k) (Fin k) ℂ)
    (H : Matrix (Fin (h + 1)) (Fin k) ℂ) :
    ∃ P B : Matrix (Fin (h + 1)) (Fin k) ℂ,
      (∀ j, P 0 j = 0) ∧
      (∀ i j, i.val < h → B i j = 0) ∧
      shift h * P - P * K = B + H := by
  let P : Matrix (Fin (h + 1)) (Fin k) ℂ := fun i => rows K H i.val
  let B : Matrix (Fin (h + 1)) (Fin k) ℂ := fun i j =>
    if i.val = h then -(Matrix.vecMul (rows K H h) K) j - H i j else 0
  refine ⟨P, B, ?_, ?_, ?_⟩
  · intro j
    rfl
  · intro i j hi
    simp [B, ne_of_lt hi]
  · ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    rw [shift_mul_apply]
    have hmul : (P * K) i j = (Matrix.vecMul (rows K H i.val) K) j := rfl
    rw [hmul]
    by_cases hi : i.val < h
    · rw [dif_pos hi]
      have hmin : min i.val h = i.val := min_eq_left hi.le
      have hindex : (⟨min i.val h, by omega⟩ : Fin (h + 1)) = i := Fin.ext hmin
      simp only [P, rows, Pi.add_apply, hindex]
      simp [B, ne_of_lt hi]
    · rw [dif_neg hi]
      have heq : i.val = h := by omega
      simp [B, heq]

/-- The actual single-shift version of Wasow's formal row normalization, to
all orders. The leading shift is retained; only positive transformed orders
are constrained to their last row. -/
theorem exists_formal_shift_reduction {h : ℕ}
    (A : ℕ → Matrix (Fin (h + 1)) (Fin (h + 1)) ℂ)
    (hA : A 0 = shift h) {q : ℕ} (hq : 0 < q) :
    ∃ P B : ℕ → Matrix (Fin (h + 1)) (Fin (h + 1)) ℂ,
      P 0 = 1 ∧ B 0 = A 0 ∧
      (∀ k j, P (k + 1) 0 j = 0) ∧
      (∀ k i j, i.val < h → B (k + 1) i j = 0) ∧
      ∀ k, (∑ i ∈ Finset.range (k + 1),
        (A (k - i) * P i - P i * B (k - i))) =
          -WasowFormalRecurrence.derivativeCoeff q P k := by
  apply WasowRecurrencePrinciple.exists_formal_reduction_of_step A hq
    (fun p => ∀ j, p 0 j = 0) (fun b => ∀ i j, i.val < h → b i j = 0)
  intro H
  simpa only [hA] using exists_rectangular_step (shift h) H

end WasowShiftReduction
#print axioms WasowShiftReduction.shift_mul_apply
#print axioms WasowShiftReduction.exists_rectangular_step
#print axioms WasowShiftReduction.exists_formal_shift_reduction
