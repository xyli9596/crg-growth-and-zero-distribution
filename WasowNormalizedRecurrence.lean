import WasowNormalizedLemma
import WasowFormalSeries

/-!
Uniqueness of the all-order normalized coefficient construction.  The input is
the full convolution equation, not a separately assumed coefficient recurrence.
The single-step commutator is recovered from that equation, and uniqueness is
proved by strong induction using only strictly lower coefficients.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace WasowNormalizedRecurrence
open WasowFormalRecurrence WasowNormalizedLemma WasowShiftReduction

section General
variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- Recover the coefficient step from the full convolution equation. -/
theorem step_of_coefficient_identity (A P B : ℕ → R) (q k : ℕ)
    (hk : 0 < k) (hP : P 0 = 1) (hB : B 0 = A 0)
    (hfull : (∑ i ∈ Finset.range (k+1),
      (A (k-i) * P i - P i * B (k-i))) = -derivativeCoeff q P k) :
    A 0 * P k - P k * A 0 = B k + residual A q P B k := by
  let f : ℕ → R := fun i => P i * B (k-i) - A (k-i) * P i
  have hmid : lowerSum A P B k =
      (∑ i ∈ Finset.range k, f i) - (B k - A k) := by
    simpa [lowerSum, f, hP] using Finset.sum_Ico_eq_sub f (show 1 ≤ k by omega)
  have hrange : (∑ i ∈ Finset.range k, f i) = lowerSum A P B k + (B k-A k) := by
    rw [hmid]
    abel
  have htotal : (∑ i ∈ Finset.range (k+1), f i) = derivativeCoeff q P k := by
    calc
      _ = -(∑ i ∈ Finset.range (k+1), (A (k-i)*P i-P i*B (k-i))) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [f]
        abel
      _ = _ := by rw [hfull, neg_neg]
  rw [Finset.sum_range_succ, hrange] at htotal
  simp only [f, Nat.sub_self, hB] at htotal
  unfold WasowFormalRecurrence.residual
  rw [← htotal]
  abel

/-- Normalizations apply to positive coefficients only. -/
def NormalizedFormalSolution (A : ℕ → R) (q : ℕ) (pNorm bNorm : R → Prop)
    (s : (ℕ → R) × (ℕ → R)) : Prop :=
  s.1 0 = 1 ∧ s.2 0 = A 0 ∧
  (∀ k, pNorm (s.1 (k+1))) ∧ (∀ k, bNorm (s.2 (k+1))) ∧
  ∀ k, (∑ i ∈ Finset.range (k+1),
    (A (k-i) * s.1 i - s.1 i * s.2 (k-i))) = -derivativeCoeff q s.1 k

/-- A proved unique normalized algebraic step implies uniqueness of every
coefficient of any solution of the complete formal convolution equation. -/
theorem normalized_formal_solution_unique (A : ℕ → R) {q : ℕ} (hq : 0 < q)
    (pNorm bNorm : R → Prop)
    (hstep : ∀ H : R, ∀ s t : R × R,
      (pNorm s.1 ∧ bNorm s.2 ∧ A 0*s.1-s.1*A 0 = s.2+H) →
      (pNorm t.1 ∧ bNorm t.2 ∧ A 0*t.1-t.1*A 0 = t.2+H) → s=t)
    {s t : (ℕ → R) × (ℕ → R)}
    (hs : NormalizedFormalSolution A q pNorm bNorm s)
    (ht : NormalizedFormalSolution A q pNorm bNorm t) : s=t := by
  have hcoeff : ∀ k, s.1 k=t.1 k ∧ s.2 k=t.2 k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => exact ⟨hs.1.trans ht.1.symm, hs.2.1.trans ht.2.1.symm⟩
      | succ k =>
        have hr : residual A q s.1 s.2 (k+1) = residual A q t.1 t.2 (k+1) :=
          residual_congr hq (fun i hi => (ih i hi).1) (fun i hi => (ih i hi).2)
        have heqs := step_of_coefficient_identity A s.1 s.2 q (k+1) (by omega)
          hs.1 hs.2.1 (hs.2.2.2.2 (k+1))
        have heqt := step_of_coefficient_identity A t.1 t.2 q (k+1) (by omega)
          ht.1 ht.2.1 (ht.2.2.2.2 (k+1))
        rw [← hr] at heqt
        have he := hstep (residual A q s.1 s.2 (k+1))
          (s.1 (k+1),s.2 (k+1)) (t.1 (k+1),t.2 (k+1))
          ⟨hs.2.2.1 k, hs.2.2.2.1 k, heqs⟩
          ⟨ht.2.2.1 k, ht.2.2.2.1 k, heqt⟩
        exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  exact Prod.ext (funext fun k => (hcoeff k).1) (funext fun k => (hcoeff k).2)

end General

/-- The single nilpotent shift has one and only one normalized all-order
formal solution, with identity constant gauge coefficient. -/
theorem existsUnique_formal_shift_reduction {h : ℕ}
    (A : ℕ → Matrix (Fin (h+1)) (Fin (h+1)) ℂ)
    (hA : A 0 = shift h) {q : ℕ} (hq : 0 < q) :
    ∃! s, NormalizedFormalSolution A q
      (fun p => ∀ j, p 0 j=0)
      (fun b => ∀ i j, i.val<h → b i j=0) s := by
  obtain ⟨P,B,hP,hB,hpn,hbn,heq⟩ := exists_formal_shift_reduction A hA hq
  refine ⟨(P,B), ⟨hP,hB,hpn,hbn,heq⟩, ?_⟩
  intro t ht
  refine normalized_formal_solution_unique A hq
    (fun p => ∀ j, p 0 j=0) (fun b => ∀ i j, i.val<h → b i j=0)
    ?_ ht ⟨hP,hB,hpn,hbn,heq⟩
  intro H s t hs ht
  exact normalized_step_unique (shift h) H
    ⟨hs.1,hs.2.1,by simpa only [hA] using hs.2.2⟩
    ⟨ht.1,ht.2.1,by simpa only [hA] using ht.2.2⟩

open WasowMultiShiftReduction

/-- The unique normalized formal solution for an arbitrary finite family of
shift blocks, including all off-diagonal rectangular blocks. -/
theorem existsUnique_formal_multishift_reduction {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h : σ → ℕ) (A : ℕ → Matrix (Index h) (Index h) ℂ)
    (hA : A 0 = jordanShift h) {q : ℕ} (hq : 0 < q) :
    ∃! s, NormalizedFormalSolution A q
      (fun p => ∀ a b j, p ⟨a,0⟩ ⟨b,j⟩=0)
      (fun b => ∀ a c i j, i.val<h a → b ⟨a,i⟩ ⟨c,j⟩=0) s := by
  obtain ⟨P,B,hP,hB,hpn,hbn,heq⟩ := exists_formal_multishift_reduction h A hA hq
  refine ⟨(P,B), ⟨hP,hB,hpn,hbn,heq⟩, ?_⟩
  intro t ht
  refine normalized_formal_solution_unique A hq
    (fun p => ∀ a b j, p ⟨a,0⟩ ⟨b,j⟩=0)
    (fun b => ∀ a c i j, i.val<h a → b ⟨a,i⟩ ⟨c,j⟩=0)
    ?_ ht ⟨hP,hB,hpn,hbn,heq⟩
  intro H s t hs ht
  exact normalized_multishift_step_unique h H
    ⟨hs.1,hs.2.1,by simpa only [hA] using hs.2.2⟩
    ⟨ht.1,ht.2.1,by simpa only [hA] using ht.2.2⟩

def NormalizedPowerSeriesSolution {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h : σ → ℕ) (A : PowerSeries (Matrix (Index h) (Index h) ℂ)) (q : ℕ)
    (s : PowerSeries (Matrix (Index h) (Index h) ℂ) ×
      PowerSeries (Matrix (Index h) (Index h) ℂ)) : Prop :=
  PowerSeries.constantCoeff s.1 = 1 ∧
  PowerSeries.constantCoeff s.2 = PowerSeries.constantCoeff A ∧
  (∀ k a b j, (PowerSeries.coeff (k+1) s.1) ⟨a,0⟩ ⟨b,j⟩=0) ∧
  (∀ k a b i j, i.val<h a → (PowerSeries.coeff (k+1) s.2) ⟨a,i⟩ ⟨b,j⟩=0) ∧
  A*s.1-s.1*s.2 = -(PowerSeries.X^(q+1)*WasowPowerSeries.derivative s.1)

/-- Extract the full coefficient equation from an equality in the actual
noncommutative power-series ring. -/
theorem powerSeries_solution_coefficients {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h : σ → ℕ) (A : PowerSeries (Matrix (Index h) (Index h) ℂ)) (q : ℕ)
    {s : PowerSeries (Matrix (Index h) (Index h) ℂ) ×
      PowerSeries (Matrix (Index h) (Index h) ℂ)}
    (hs : NormalizedPowerSeriesSolution h A q s) :
    NormalizedFormalSolution (fun k => PowerSeries.coeff k A) q
      (fun p => ∀ a b j, p ⟨a,0⟩ ⟨b,j⟩=0)
      (fun b => ∀ a c i j, i.val<h a → b ⟨a,i⟩ ⟨c,j⟩=0)
      ((fun k => PowerSeries.coeff k s.1),(fun k => PowerSeries.coeff k s.2)) := by
  refine ⟨?_, ?_, hs.2.2.1, hs.2.2.2.1, ?_⟩
  · simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hs.1
  · simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hs.2.1
  · intro k
    have hk := congrArg (PowerSeries.coeff k) hs.2.2.2.2
    rw [map_sub, WasowPowerSeries.coeff_mul_range_right,
      WasowPowerSeries.coeff_mul_range_left, WasowPowerSeries.coeff_rank_derivative] at hk
    simpa only [derivativeCoeff, ← Finset.sum_sub_distrib] using hk

theorem normalized_multishift_powerSeries_unique {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h : σ → ℕ) (A : PowerSeries (Matrix (Index h) (Index h) ℂ))
    (hA : PowerSeries.constantCoeff A = jordanShift h) {q : ℕ} (hq : 0<q)
    {s t : PowerSeries (Matrix (Index h) (Index h) ℂ) ×
      PowerSeries (Matrix (Index h) (Index h) ℂ)}
    (hs : NormalizedPowerSeriesSolution h A q s)
    (ht : NormalizedPowerSeriesSolution h A q t) : s=t := by
  have hAc : (fun k => PowerSeries.coeff k A) 0 = jordanShift h := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hA
  have hu := existsUnique_formal_multishift_reduction h (fun k => PowerSeries.coeff k A) hAc hq
  have he := hu.unique (powerSeries_solution_coefficients h A q hs)
    (powerSeries_solution_coefficients h A q ht)
  apply Prod.ext
  · apply PowerSeries.ext
    intro k
    exact congrFun (congrArg Prod.fst he) k
  · apply PowerSeries.ext
    intro k
    exact congrFun (congrArg Prod.snd he) k

/-- Unique normalized formal power-series pair. Existence is supplied by the
proved multishift construction, which also gives a genuine formal inverse. -/
theorem existsUnique_normalized_multishift_powerSeries {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h : σ → ℕ) (A : PowerSeries (Matrix (Index h) (Index h) ℂ))
    (hA : PowerSeries.constantCoeff A = jordanShift h) {q : ℕ} (hq : 0<q) :
    ∃! s, NormalizedPowerSeriesSolution h A q s ∧ IsUnit s.1 := by
  obtain ⟨P,B,_S,hP,hunit,hB,hpn,hbn,_hSP,_hPS,heq⟩ :=
    WasowFormalSeries.exists_multishift_powerSeries h A hA hq
  refine ⟨(P,B), ⟨⟨hP,hB,hpn,hbn,heq⟩,hunit⟩, ?_⟩
  intro t ht
  exact normalized_multishift_powerSeries_unique h A hA hq ht.1 ⟨hP,hB,hpn,hbn,heq⟩

end WasowNormalizedRecurrence

#print axioms WasowNormalizedRecurrence.step_of_coefficient_identity
#print axioms WasowNormalizedRecurrence.normalized_formal_solution_unique
#print axioms WasowNormalizedRecurrence.existsUnique_formal_shift_reduction
#print axioms WasowNormalizedRecurrence.existsUnique_formal_multishift_reduction
#print axioms WasowNormalizedRecurrence.powerSeries_solution_coefficients
#print axioms WasowNormalizedRecurrence.normalized_multishift_powerSeries_unique
#print axioms WasowNormalizedRecurrence.existsUnique_normalized_multishift_powerSeries
