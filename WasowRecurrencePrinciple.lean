import WasowFormalRecurrence

/-! A reusable all-order recursion principle for formal gauge normalization.
The single-step algebraic solver and its normalization predicates are explicit
inputs. The formal sequences are constructed by the well-founded recursion
already used in the actual two-block theorem; no sequence or formal solution
is assumed. This allows independent proved solvers to reuse the recursion. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowRecurrencePrinciple
open WasowFormalRecurrence

/-- Any actual linear coefficient solver lifts to all formal orders. The
normalization predicates apply to positive orders; the constant transformed
coefficient remains `A 0` and need not satisfy either predicate. -/
theorem exists_formal_reduction_of_step {R : Type*} [Ring R] [Algebra ℂ R]
    (A : ℕ → R) {q : ℕ} (hq : 0 < q) (pNorm bNorm : R → Prop)
    (hstep : ∀ H : R, ∃ p b : R,
      pNorm p ∧ bNorm b ∧ A 0 * p - p * A 0 = b + H) :
    ∃ P B : ℕ → R,
      P 0 = 1 ∧ B 0 = A 0 ∧
      (∀ k, pNorm (P (k + 1))) ∧ (∀ k, bNorm (B (k + 1))) ∧
      ∀ k, (∑ i ∈ Finset.range (k + 1),
        (A (k - i) * P i - P i * B (k - i))) = -derivativeCoeff q P k := by
  choose p b hp hb hs using hstep
  let step : R → R × R := fun H => (p H, b H)
  let P : ℕ → R := fun k => (coefficients A q step k).1
  let B : ℕ → R := fun k => (coefficients A q step k).2
  have hPzero : P 0 = 1 := by simp [P]
  have hBzero : B 0 = A 0 := by simp [B]
  have hrec (k : ℕ) (hk : 0 < k) :
      P k = p (residual A q P B k) ∧ B k = b (residual A q P B k) := by
    have hh := coefficients_pos A hq hk step
    exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  refine ⟨P, B, hPzero, hBzero, ?_, ?_, ?_⟩
  · intro k
    rw [(hrec (k + 1) (by omega)).1]
    exact hp _
  · intro k
    rw [(hrec (k + 1) (by omega)).2]
    exact hb _
  · intro k
    cases k with
    | zero => simp [derivativeCoeff, hPzero, hBzero]
    | succ k =>
      apply coefficient_identity_of_step A P B q (k + 1) (by omega) hPzero hBzero
      rw [(hrec (k + 1) (by omega)).1, (hrec (k + 1) (by omega)).2]
      exact hs _

end WasowRecurrencePrinciple
#print axioms WasowRecurrencePrinciple.exists_formal_reduction_of_step
