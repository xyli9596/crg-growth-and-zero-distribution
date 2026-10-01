import WasowGlobalFormalRegular
import WasowLaurentClearing

/-! The actual ramified coefficient has an explicitly known scalar pole.
A sufficiently high common clearing is the same shifted, expanded original
power series, so the analytic input can be transported without choosing a new
unrelated Taylor expansion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace WasowRamifiedCoefficient
open WasowLaurentGauge WasowLaurentRamification WasowGlobalFormalRegular
open WasowLaurentClearing WasowLaurentTruncation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pole (p q : ℕ) : ℕ := p*(q+1)+1

theorem pullback_coefficient (p q : ℕ) (hp : 0<p)
    (A : PowerSeries (Matrix ι ι ℂ)) :
    pullback p hp (differentialCoefficient q A) =
      (HahnSeries.single (-(pole p q : ℤ)) 1 : L) •
        toLaurent ((-(p:ℂ)) • expandSeries p A) := by
  apply Matrix.ext
  intro i j
  simp only [pullback, differentialCoefficient, Matrix.smul_apply, smul_eq_mul,
    map_mul, ramify_single, toLaurent_smul_entry, toLaurent_expandSeries p hp A, ramifyMatrix]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  simp only [jacobian, HahnSeries.C_apply, HahnSeries.single_mul_single]
  congr 1
  · simp only [pole, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring_nf
  · ring_nf

/-- A common coefficient pole above the explicit ramified pole has this
concrete shifted series; both sides represent the entire coefficient. -/
theorem clearAt_pullback (p q h : ℕ) (hp : 0<p)
    (A : PowerSeries (Matrix ι ι ℂ))
    (hA : poleOrder (pullback p hp (differentialCoefficient q A)) ≤ h)
    (hh : pole p q ≤ h) :
    clearAt h (pullback p hp (differentialCoefficient q A)) =
      PowerSeries.X^(h-pole p q) * ((-(p:ℂ)) • expandSeries p A) := by
  apply WasowLaurentResidual.toLaurent_injective
  rw [toLaurent_clearAt h _ hA, pullback_coefficient, smul_smul,
    map_mul, toLaurent_X_pow]
  have hm (v : L) (M : Matrix ι ι L) : (v • (1 : Matrix ι ι L))*M = v•M := by
    apply Matrix.ext
    intro i j
    simp [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_ite, ite_mul]
  rw [hm]
  have hs : (HahnSeries.single (h : ℤ) 1 : L) * HahnSeries.single (-(pole p q : ℤ)) 1 =
      HahnSeries.single ((h-pole p q : ℕ) : ℤ) 1 := by
    rw [HahnSeries.single_mul_single, one_mul, Nat.cast_sub hh]
    congr 1
  rw [hs]

#print axioms pullback_coefficient
#print axioms clearAt_pullback
end WasowRamifiedCoefficient
