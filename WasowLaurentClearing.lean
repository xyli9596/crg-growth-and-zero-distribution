import WasowLaurentTruncation
import WasowLaurentResidual

/-! A common coefficient pole and both gauge poles are chosen from the actual
Laurent matrices. All cleared products and differential equations follow from
their true Laurent identities; no cleared equation is supplied as a hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace WasowLaurentClearing
open WasowLaurentGauge WasowLaurentTruncation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Clear at a prescribed order by adding a nonnegative power to the already
constructed common-pole clearing. The exact recovery theorem assumes h is sufficient. -/
def clearAt (h : ℕ) (G : Matrix ι ι L) : PowerSeries (Matrix ι ι ℂ) :=
  PowerSeries.X^(h-poleOrder G) * cleared G

@[simp] theorem clearAt_poleOrder (G : Matrix ι ι L) :
    clearAt (poleOrder G) G = cleared G := by simp [clearAt]

theorem toLaurent_clearAt (h : ℕ) (G : Matrix ι ι L) (hh : poleOrder G ≤ h) :
    toLaurent (clearAt h G) = (HahnSeries.single (h : ℤ) 1 : L) • G := by
  rw [clearAt, map_mul, toLaurent_X_pow, toLaurent_cleared]
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    mul_ite, ite_mul, mul_one (M := L), mul_zero (M₀ := L), zero_mul (M₀ := L), Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← mul_assoc, HahnSeries.single_mul_single, one_mul]
  rw [← Nat.cast_add, Nat.sub_add_cancel hh]

theorem recover_clearAt (h : ℕ) (G : Matrix ι ι L) (hh : poleOrder G ≤ h) :
    (HahnSeries.single (-(h : ℤ)) 1 : L) • toLaurent (clearAt h G) = G := by
  rw [toLaurent_clearAt h G hh, smul_smul]
  simp

/-- A common pole order also positive enough for the cleared derivative term. -/
def commonOrder (A B : Matrix ι ι L) : ℕ := max 1 (max (poleOrder A) (poleOrder B))

omit [DecidableEq ι] in
theorem commonOrder_bounds (A B : Matrix ι ι L) :
    0 < commonOrder A B ∧ poleOrder A ≤ commonOrder A B ∧
      poleOrder B ≤ commonOrder A B := by
  unfold commonOrder
  omega

/-- The prescribed common-order clearing is forced to satisfy the exact
power-series differential equation by the genuine Laurent gauge identity. -/
theorem equation_clearAt (h : ℕ) (hh : 0 < h) (A B G : Matrix ι ι L)
    (hA : poleOrder A ≤ h) (hB : poleOrder B ≤ h)
    (heq : GaugeEquation A G B) :
    WasowClearedResidual.Equation (poleOrder G) h (clearAt h A) (cleared G) (clearAt h B) := by
  apply WasowLaurentResidual.equation_of_laurent (poleOrder G) h hh
  simpa only [WasowLaurentResidual.monomial, recover_clearAt h A hA,
    recover_clearAt h B hB, recover_cleared] using heq

/-- All data needed for the actual truncation estimates is constructed from
an arbitrary true Laurent gauge and its two-sided inverse. The pole orders
are fixed before a truncation degree is chosen. -/
theorem automatic_cleared_data (A B G H : Matrix ι ι L)
    (hGH : G*H=1) (hHG : H*G=1) (heq : GaugeEquation A G B) :
    let h := commonOrder A B
    let a := poleOrder G
    let b := poleOrder H
    let A₀ := clearAt h A
    let B₀ := clearAt h B
    let P := cleared G
    let Q := cleared H
    0 < h ∧
      (HahnSeries.single (-(h : ℤ)) 1 : L) • toLaurent A₀ = A ∧
      (HahnSeries.single (-(h : ℤ)) 1 : L) • toLaurent B₀ = B ∧
      (HahnSeries.single (-(a : ℤ)) 1 : L) • toLaurent P = G ∧
      (HahnSeries.single (-(b : ℤ)) 1 : L) • toLaurent Q = H ∧
      P*Q=PowerSeries.X^(a+b) ∧ Q*P=PowerSeries.X^(a+b) ∧
      WasowClearedResidual.Equation a h A₀ P B₀ := by
  obtain ⟨hh,hA,hB⟩ := commonOrder_bounds A B
  obtain ⟨hPQ,hQP⟩ := cleared_inverse_pair G H hGH hHG
  exact ⟨hh, recover_clearAt _ A hA, recover_clearAt _ B hB,
    recover_cleared G, recover_cleared H, hPQ, hQP,
    equation_clearAt _ hh A B G hA hB heq⟩

#print axioms clearAt_poleOrder
#print axioms toLaurent_clearAt
#print axioms recover_clearAt
#print axioms commonOrder_bounds
#print axioms equation_clearAt
#print axioms automatic_cleared_data
end WasowLaurentClearing
