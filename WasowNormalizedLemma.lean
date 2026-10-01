import WasowMultiShiftReduction

/-! A normalized replacement for the uniqueness assertion in Wasow Lemma 19.1.
Fixing the first row of the unknown rectangular gauge to zero determines both
the gauge and the last transformed row uniquely. The right matrix is arbitrary.
The normalization applies only to positive formal coefficients, not P_0 = I. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowNormalizedLemma
open WasowShiftReduction

def NormalizedStep {h k : ℕ} (K : Matrix (Fin k) (Fin k) ℂ)
    (H : Matrix (Fin (h+1)) (Fin k) ℂ)
    (s : Matrix (Fin (h+1)) (Fin k) ℂ × Matrix (Fin (h+1)) (Fin k) ℂ) : Prop :=
  (∀ j, s.1 0 j = 0) ∧ (∀ i j, i.val < h → s.2 i j = 0) ∧
    shift h * s.1 - s.1 * K = s.2 + H

/-- The first row and the equations in all preceding rows uniquely propagate
every gauge row. The final equation then uniquely determines the residual row. -/
theorem normalized_step_unique {h k : ℕ} (K : Matrix (Fin k) (Fin k) ℂ)
    (H : Matrix (Fin (h+1)) (Fin k) ℂ)
    {s t : Matrix (Fin (h+1)) (Fin k) ℂ × Matrix (Fin (h+1)) (Fin k) ℂ}
    (hs : NormalizedStep K H s) (ht : NormalizedStep K H t) : s = t := by
  obtain ⟨hs0, hsB, hsEq⟩ := hs
  obtain ⟨ht0, htB, htEq⟩ := ht
  have hrows : ∀ r (hr : r ≤ h) (j : Fin k),
      s.1 ⟨r, by omega⟩ j = t.1 ⟨r, by omega⟩ j := by
    intro r
    induction r with
    | zero =>
      intro hr j
      exact (hs0 j).trans (ht0 j).symm
    | succ r ih =>
      intro hr j
      let i : Fin (h+1) := ⟨r, by omega⟩
      have hi : i.val < h := by dsimp [i]; omega
      have hmul : (s.1*K) i j = (t.1*K) i j := by
        simp only [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro l hl
        rw [ih (by omega) l]
      have he := congrFun (congrFun hsEq i) j
      have hf := congrFun (congrFun htEq i) j
      simp only [Matrix.sub_apply, Matrix.add_apply, shift_mul_apply, dif_pos hi,
        hsB i j hi, htB i j hi, zero_add] at he hf
      rw [hmul] at he
      exact sub_left_inj.mp (he.trans hf.symm)
  have hP : s.1 = t.1 := by
    ext i j
    exact hrows i.val (by omega) j
  have hB : s.2 = t.2 := by
    rw [hP] at hsEq
    exact add_right_cancel (hsEq.symm.trans htEq)
  exact Prod.ext hP hB

/-- Normalized coefficient solver: existence and uniqueness of the entire
pair, without a spectral assumption on the right matrix. -/
theorem existsUnique_normalized_step {h k : ℕ} (K : Matrix (Fin k) (Fin k) ℂ)
    (H : Matrix (Fin (h+1)) (Fin k) ℂ) : ∃! s, NormalizedStep K H s := by
  obtain ⟨P,B,hP,hB,heq⟩ := exists_rectangular_step K H
  refine ⟨(P,B), ⟨hP,hB,heq⟩, ?_⟩
  intro s hs
  exact normalized_step_unique K H hs ⟨hP,hB,heq⟩

/-- The corrected book statement. The first `h` rows of `M` are prescribed
by `D`; its last row is free. Requiring the first row of `X` to vanish yields
one and only one pair `(X,M)` solving `shift h * X - X * K = M`.
The actual row count is `h+1`, so this includes the one-row boundary case. -/
theorem existsUnique_normalized_lemma_19_1 {h k : ℕ}
    (K : Matrix (Fin k) (Fin k) ℂ) (D : Matrix (Fin (h+1)) (Fin k) ℂ) :
    ∃! s : Matrix (Fin (h+1)) (Fin k) ℂ × Matrix (Fin (h+1)) (Fin k) ℂ,
      (∀ j, s.1 0 j = 0) ∧
      (∀ i j, i.val < h → s.2 i j = D i j) ∧
      shift h * s.1 - s.1 * K = s.2 := by
  obtain ⟨s,hs,huniq⟩ := existsUnique_normalized_step K D
  refine ⟨(s.1,s.2+D), ⟨hs.1, ?_, hs.2.2⟩, ?_⟩
  · intro i j hi
    simp only [Matrix.add_apply, hs.2.1 i j hi, zero_add]
  · intro t ht
    have htstep : NormalizedStep K D (t.1,t.2-D) := by
      refine ⟨ht.1, ?_, ?_⟩
      · intro i j hi
        simp only [Matrix.sub_apply, ht.2.1 i j hi, sub_self]
      · simpa only [sub_add_cancel] using ht.2.2
    have heq := huniq (t.1,t.2-D) htstep
    apply Prod.ext
    · simpa only using congrArg Prod.fst heq
    · have hh := congrArg Prod.snd heq
      change t.2 - D = s.2 at hh
      exact (sub_eq_iff_eq_add).mp hh

open WasowMultiShiftReduction

def NormalizedMultiStep {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h : σ → ℕ) (H : Matrix (Index h) (Index h) ℂ)
    (s : Matrix (Index h) (Index h) ℂ × Matrix (Index h) (Index h) ℂ) : Prop :=
  (∀ a b j, s.1 ⟨a,0⟩ ⟨b,j⟩ = 0) ∧
  (∀ a b i j, i.val < h a → s.2 ⟨a,i⟩ ⟨b,j⟩ = 0) ∧
  jordanShift h * s.1 - s.1 * jordanShift h = s.2 + H

/-- The normalized rectangular uniqueness theorem applies simultaneously
to every block of the actual matrix coefficient equation. -/
theorem normalized_multishift_step_unique {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h : σ → ℕ) (H : Matrix (Index h) (Index h) ℂ)
    {s t : Matrix (Index h) (Index h) ℂ × Matrix (Index h) (Index h) ℂ}
    (hs : NormalizedMultiStep h H s) (ht : NormalizedMultiStep h H t) : s = t := by
  have toBlock (u : Matrix (Index h) (Index h) ℂ × Matrix (Index h) (Index h) ℂ)
      (hu : NormalizedMultiStep h H u) (a b : σ) :
      NormalizedStep (shift (h b)) (block H a b) (block u.1 a b, block u.2 a b) := by
    refine ⟨hu.1 a b, hu.2.1 a b, ?_⟩
    have he := congrArg (fun M => block M a b) hu.2.2
    change block (jordanShift h * u.1) a b - block (u.1 * jordanShift h) a b =
      block u.2 a b + block H a b at he
    simpa only [block_jordanShift_mul, block_mul_jordanShift] using he
  have blocks (a b : σ) : (block s.1 a b, block s.2 a b) =
      (block t.1 a b, block t.2 a b) :=
    normalized_step_unique (shift (h b)) (block H a b) (toBlock s hs a b) (toBlock t ht a b)
  apply Prod.ext
  · ext ⟨a,i⟩ ⟨b,j⟩
    exact congrFun (congrFun (congrArg Prod.fst (blocks a b)) i) j
  · ext ⟨a,i⟩ ⟨b,j⟩
    exact congrFun (congrFun (congrArg Prod.snd (blocks a b)) i) j

/-- A unique normalized coefficient pair for an arbitrary finite family
of Jordan shift blocks, with arbitrary block sizes and multiplicities. -/
theorem existsUnique_normalized_multishift_step {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h : σ → ℕ) (H : Matrix (Index h) (Index h) ℂ) :
    ∃! s, NormalizedMultiStep h H s := by
  obtain ⟨P,B,hP,hB,heq⟩ := exists_multishift_step h H
  refine ⟨(P,B), ⟨hP,hB,heq⟩, ?_⟩
  intro s hs
  exact normalized_multishift_step_unique h H hs ⟨hP,hB,heq⟩

#print axioms normalized_step_unique
#print axioms existsUnique_normalized_step
#print axioms existsUnique_normalized_lemma_19_1
#print axioms normalized_multishift_step_unique
#print axioms existsUnique_normalized_multishift_step
end WasowNormalizedLemma
