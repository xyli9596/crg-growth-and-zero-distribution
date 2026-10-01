import WasowFormalSylvester

/-! All-order formal two-block reduction by well-founded coefficient recursion.
The parameter `q ≥ 1` is the Poincare rank: Wasow's §11 parameter is `q - 1`.
Under `t = 1/x`, the equation is `A P - P B = -t^(q+1) dP/dt`.
The sequences below are actually constructed by strong recursion; no existence
of a formal gauge or recurrence solution is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowFormalRecurrence

section Recursion
variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The strictly lower-order product terms in Wasow's coefficient equation. -/
def lowerSum (A P B : ℕ → R) (k : ℕ) : R :=
  ∑ i ∈ Finset.Ico 1 k, (P i * B (k - i) - A (k - i) * P i)

/-- Coefficient of `t^(q+1) P'`. The branch at and below degree `q` is zero. -/
def derivativeCoeff (q : ℕ) (P : ℕ → R) (k : ℕ) : R :=
  if q < k then ((k - q : ℕ) : ℂ) • P (k - q) else 0

/-- Known residual at order `k > 0`, before solving the Sylvester equation. -/
def residual (A : ℕ → R) (q : ℕ) (P B : ℕ → R) (k : ℕ) : R :=
  lowerSum A P B k - A k - derivativeCoeff q P k

theorem residual_congr {A : ℕ → R} {q k : ℕ} (hq : 0 < q)
    {P B P' B' : ℕ → R} (hP : ∀ i < k, P i = P' i)
    (hB : ∀ i < k, B i = B' i) :
    residual A q P B k = residual A q P' B' k := by
  have hsum : lowerSum A P B k = lowerSum A P' B' k := by
    unfold lowerSum
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi1, hik⟩ := Finset.mem_Ico.mp hi
    rw [hP i hik, hB (k - i) (Nat.sub_lt (by omega) (by omega))]
  have hderiv : derivativeCoeff q P k = derivativeCoeff q P' k := by
    unfold derivativeCoeff
    split_ifs with hqk
    · rw [hP (k - q) (Nat.sub_lt (by omega) hq)]
    · rfl
  simp only [residual, hsum, hderiv]

/-- At order `k`, only values with indices strictly less than `k` are supplied
by the well-founded recursor. Values outside this history are zero fillers. -/
def coefficients (A : ℕ → R) (q : ℕ) (step : R → R × R) : ℕ → R × R :=
  Nat.strongRec fun k previous =>
    if k = 0 then (1, A 0) else
      step (residual A q
        (fun i => if hi : i < k then (previous i hi).1 else 0)
        (fun i => if hi : i < k then (previous i hi).2 else 0) k)

@[simp] theorem coefficients_zero (A : ℕ → R) (q : ℕ) (step : R → R × R) :
    coefficients A q step 0 = (1, A 0) := by
  rw [coefficients, Nat.strongRec_eq]
  simp

theorem coefficients_pos (A : ℕ → R) {q k : ℕ} (hq : 0 < q) (hk : 0 < k)
    (step : R → R × R) :
    coefficients A q step k = step (residual A q
      (fun i => (coefficients A q step i).1)
      (fun i => (coefficients A q step i).2) k) := by
  rw [coefficients, Nat.strongRec_eq, if_neg (by omega : k ≠ 0)]
  congr 1
  apply residual_congr hq
  · intro i hi
    simp only [hi, dite_true]
    rfl
  · intro i hi
    simp only [hi, dite_true]
    rfl

/-- The Sylvester equation at order `k` implies the full convolution identity
at that order, including the derivative term and both endpoint coefficients. -/
theorem coefficient_identity_of_step (A P B : ℕ → R) (q k : ℕ)
    (hk : 0 < k) (hP : P 0 = 1) (hB : B 0 = A 0)
    (hstep : A 0 * P k - P k * A 0 = B k + residual A q P B k) :
    (∑ i ∈ Finset.range (k + 1), (A (k - i) * P i - P i * B (k - i))) =
      -derivativeCoeff q P k := by
  let f : ℕ → R := fun i => P i * B (k - i) - A (k - i) * P i
  have hmid := Finset.sum_Ico_eq_sub f (show 1 ≤ k by omega)
  have hmid' : lowerSum A P B k =
      (∑ i ∈ Finset.range k, f i) - (B k - A k) := by
    simpa [lowerSum, f, hP] using hmid
  have hend : f k = -(B k + residual A q P B k) := by
    simp only [f, Nat.sub_self, hB]
    rw [← neg_sub, hstep]
  have htotal : (∑ i ∈ Finset.range (k + 1), f i) = derivativeCoeff q P k := by
    rw [Finset.sum_range_succ, hend]
    have hrange : (∑ i ∈ Finset.range k, f i) = lowerSum A P B k + (B k - A k) := by
      rw [hmid']
      abel
    rw [hrange]
    unfold residual
    abel
  calc
    _ = -(∑ i ∈ Finset.range (k + 1), f i) := by
      simp only [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [f]
      abel
    _ = _ := congrArg Neg.neg htotal

end Recursion
section Blocks
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The exact single-step solver supplied by the proved nilpotent-block
Sylvester theorem, with the required diagonal/off-diagonal normalizations. -/
theorem exists_step {α β : ℂ} (hαβ : α ≠ β)
    {N : Matrix m m ℂ} {M : Matrix n n ℂ}
    (hN : IsNilpotent N) (hM : IsNilpotent M)
    (H : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    ∃ s : Matrix (m ⊕ n) (m ⊕ n) ℂ × Matrix (m ⊕ n) (m ⊕ n) ℂ,
      s.1.toBlocks₁₁ = 0 ∧ s.1.toBlocks₂₂ = 0 ∧
      s.2.toBlocks₁₂ = 0 ∧ s.2.toBlocks₂₁ = 0 ∧
      Matrix.fromBlocks (α • 1 + N) 0 0 (β • 1 + M) * s.1 -
        s.1 * Matrix.fromBlocks (α • 1 + N) 0 0 (β • 1 + M) = s.2 + H := by
  obtain ⟨X, Y, hXY⟩ := WasowFormalSylvester.exists_block_coefficient hαβ hN hM H
  exact ⟨(Matrix.fromBlocks 0 X Y 0,
    Matrix.fromBlocks (-H.toBlocks₁₁) 0 0 (-H.toBlocks₂₂)),
    rfl, rfl, rfl, rfl, hXY⟩

/-- Formal two-block reduction to all orders. The gauge has constant term one,
all its higher coefficients are off diagonal, and the transformed series is
block diagonal. The convolution equation is exactly the coefficient equation
of `A(t) P(t) - P(t) B(t) = -t^(q+1) P'(t)`, for every natural degree. -/
theorem exists_formal_block_reduction {α β : ℂ} (hαβ : α ≠ β)
    {N : Matrix m m ℂ} {M : Matrix n n ℂ}
    (hN : IsNilpotent N) (hM : IsNilpotent M)
    (A : ℕ → Matrix (m ⊕ n) (m ⊕ n) ℂ)
    (hA : A 0 = Matrix.fromBlocks (α • 1 + N) 0 0 (β • 1 + M))
    {q : ℕ} (hq : 0 < q) :
    ∃ P B : ℕ → Matrix (m ⊕ n) (m ⊕ n) ℂ,
      P 0 = 1 ∧ B 0 = A 0 ∧
      (∀ k, (P (k + 1)).toBlocks₁₁ = 0 ∧ (P (k + 1)).toBlocks₂₂ = 0) ∧
      (∀ k, (B k).toBlocks₁₂ = 0 ∧ (B k).toBlocks₂₁ = 0) ∧
      ∀ k, (∑ i ∈ Finset.range (k + 1),
        (A (k - i) * P i - P i * B (k - i))) = -derivativeCoeff q P k := by
  choose step hs using fun H => exists_step hαβ hN hM H
  let P : ℕ → Matrix (m ⊕ n) (m ⊕ n) ℂ := fun k => (coefficients A q step k).1
  let B : ℕ → Matrix (m ⊕ n) (m ⊕ n) ℂ := fun k => (coefficients A q step k).2
  have hP0 : P 0 = 1 := by simp [P]
  have hB0 : B 0 = A 0 := by simp [B]
  have hrec (k : ℕ) (hk : 0 < k) :
      P k = (step (residual A q P B k)).1 ∧
      B k = (step (residual A q P B k)).2 := by
    have hh := coefficients_pos A hq hk step
    exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  refine ⟨P, B, hP0, hB0, ?_, ?_, ?_⟩
  · intro k
    rw [(hrec (k + 1) (by omega)).1]
    exact ⟨(hs _).1, (hs _).2.1⟩
  · intro k
    cases k with
    | zero => rw [hB0, hA]; exact ⟨rfl, rfl⟩
    | succ k =>
      rw [(hrec (k + 1) (by omega)).2]
      exact ⟨(hs _).2.2.1, (hs _).2.2.2.1⟩
  · intro k
    cases k with
    | zero => simp [derivativeCoeff, hP0, hB0]
    | succ k =>
      apply coefficient_identity_of_step A P B q (k + 1) (by omega) hP0 hB0
      rw [(hrec (k + 1) (by omega)).1, (hrec (k + 1) (by omega)).2, hA]
      exact (hs _).2.2.2.2

end Blocks
end WasowFormalRecurrence

#print axioms WasowFormalRecurrence.residual_congr
#print axioms WasowFormalRecurrence.coefficients_zero
#print axioms WasowFormalRecurrence.coefficients_pos
#print axioms WasowFormalRecurrence.coefficient_identity_of_step

#print axioms WasowFormalRecurrence.exists_step
#print axioms WasowFormalRecurrence.exists_formal_block_reduction
