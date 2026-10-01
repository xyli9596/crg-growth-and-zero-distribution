import WasowShearingLeading
import WasowNilpotentNormalized

/-! The fractional branch has actual last-row feedback, zero diagonal, and
zero trace. Hence a unique eigenvalue, when represented by a nilpotent scalar
translate, is necessarily zero. These are the entry-level conclusions needed
before applying the determinantal-divisor descent. -/
set_option autoImplicit false
noncomputable section
namespace WasowShearingExceptional
open WasowShearingLeading
variable {n : ℕ}

theorem fractional_leading_trace_zero
    (A : ℕ → Matrix (Fin n) (Fin n) ℂ) (σ : ℚ)
    (hfrac : ∀ k : ℕ, σ  ≠  k) : (leadingMatrix A σ).trace=0 := by
  simp only [Matrix.trace,Matrix.diag,leadingMatrix_diagonal_zero A σ hfrac,Finset.sum_const_zero]

/-- A scalar translate of a nilpotent complex matrix has that scalar as
its mean trace. In positive dimension, zero trace forces the scalar to vanish. -/
theorem scalar_part_zero_of_trace_zero (C : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) (α : ℂ) (htr : C.trace=0)
    (hN : IsNilpotent (C-α • 1)) : α=0 ∧ IsNilpotent C := by
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  rw [Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_one,htr,Fintype.card_fin] at ht
  have hn' : (n : ℂ)  ≠  0 := by exact_mod_cast Nat.ne_of_gt hn
  have hα : α=0 := by
    have hm : α*(n : ℂ)=0 := by simpa only [smul_eq_mul,zero_sub,neg_eq_zero] using ht
    exact (mul_eq_zero.mp hm).resolve_right hn'
  refine ⟨hα,?_⟩
  simpa only [hα,zero_smul,sub_zero] using hN

/-- Non-stopping fractional feedback must lie in an allowed last row and
strictly below the diagonal. Both claims are deduced from actual coefficients. -/
theorem fractional_feedback_last_row
    (A : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hshape : ∀ i j, A 0 i j  ≠  0 → j.val=i.val+1)
    (lastRows : Set (Fin n))
    (hnorm : ∀ k, 0 < k → ∀ i j, i ∉ lastRows → A k i j=0)
    {σ : ℚ} (hσ : 0 < σ) (hfrac : ∀ k : ℕ, σ ≠ k)
    (hfeedback : ∃ i j, j ≤ i ∧ leadingMatrix A σ i j ≠ 0) :
    ∃ i j, j < i ∧ i  ∈  lastRows ∧ leadingMatrix A σ i j ≠ 0 := by
  obtain ⟨i,j,hji,hne⟩ := hfeedback
  have hij : j ≠ i := by
    intro he
    subst j
    exact hne (leadingMatrix_diagonal_zero A σ hfrac i)
  refine ⟨i,j,lt_of_le_of_ne hji hij,?_,hne⟩
  by_contra hi
  rw [leadingMatrix_normalized_rows A hshape lastRows hnorm hσ i j hi] at hne
  have := hshape i j hne
  omega

/-- The actual slope selection separates the integral branch from a
fractional branch with the concrete exceptional-entry properties. -/
theorem exists_slope_integral_or_exceptional
    (A : ℕ → Matrix (Fin n) (Fin n) ℂ) (q : ℕ)
    (hshape : ∀ i j, A 0 i j  ≠  0 → j.val=i.val+1)
    (lastRows : Set (Fin n))
    (hnorm : ∀ k, 0 < k → ∀ i j, i ∉ lastRows → A k i j=0) :
    ∃ σ : ℚ, 0 < σ ∧ σ  ≤  (q+1 : ℕ) ∧
      (∀ k i j, A k i j ≠ 0 → 0 ≤ weightedDegree σ k i j) ∧
      ((∃ m : ℕ, σ=m) ∨
        (σ < (q+1 : ℕ) ∧ (∀ i, leadingMatrix A σ i i=0) ∧
          ∃ i j, j < i ∧ i  ∈  lastRows ∧ leadingMatrix A σ i j ≠ 0)) := by
  classical
  obtain ⟨σ,hσ,hcap,hbound,hfb⟩ := exists_slope_with_leading_feedback A q hshape
  refine ⟨σ,hσ,hcap,hbound,?_⟩
  by_cases hint : ∃ m : ℕ, σ=m
  · exact Or.inl hint
  · have hfrac : ∀ k : ℕ, σ ≠ k := by simpa only [not_exists] using hint
    have hnecap : σ ≠ (q+1 : ℕ) := hfrac _
    refine Or.inr ⟨lt_of_le_of_ne hcap hnecap,
      leadingMatrix_diagonal_zero A σ hfrac,?_⟩
    exact fractional_feedback_last_row A hshape lastRows hnorm hσ hfrac
      (hfb.resolve_left hnecap)

#print axioms fractional_leading_trace_zero
#print axioms scalar_part_zero_of_trace_zero
#print axioms fractional_feedback_last_row
#print axioms exists_slope_integral_or_exceptional
end WasowShearingExceptional
