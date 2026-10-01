import WasowLaurentInverse
import WasowLaurentActualResidual

/-! Actual transformed residual estimates for finite Laurent gauges. The
original coefficient pole and both formal inverse-pair pole orders are paid
for explicitly; the cleared leading matrix may be singular. -/
set_option autoImplicit false
noncomputable section
open Set Filter Asymptotics
open scoped Topology Matrix.Norms.Operator
namespace WasowLaurentRemainder
open WasowMatrixPolynomial WasowLaurentInverse
variable {m : ℕ}
abbrev Series := PowerSeries (Matrix (Fin m) (Fin m) ℂ)

theorem finiteGauge_eq (P : Series (m := m)) (a N : ℕ) :
    WasowLaurentActualResidual.finiteGauge a N P = finiteGauge P a N := by
  funext z
  simp only [WasowLaurentActualResidual.finiteGauge, finiteGauge, zpow_neg, zpow_natCast]

def remainder (a h N : ℕ) (c : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (P B : Series (m := m)) (z : ℂ) :=
  (finiteGauge P a N z)⁻¹ * WasowLaurentActualResidual.rawDefect a h N c P B z

/-- The genuine inverse-normalized residual has the predicted high order.
All three pole losses occur in the exponent, and no error bound is assumed. -/
theorem eventually_remainder_bound (a b h N : ℕ) (hh : 0 < h)
    {c : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hc : HasFPowerSeriesAt c s 0) (A P Q B : Series (m := m))
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n A)
    (hPQ : P * Q = PowerSeries.X ^ (a+b))
    (heq : WasowClearedResidual.Equation a h A P B) (hN : a+b+h ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      ‖remainder a h N c P B z‖ ≤ C * ‖z‖ ^ (N-(a+b+h)) := by
  obtain ⟨CG, hCG, hG⟩ := eventually_inverse_bounds P Q a b N hPQ (by omega)
  obtain ⟨CE, hCE, hE⟩ :=
    (WasowClearedResidual.actualDefect_isBigO a h N hh hc A P B hcoeff heq).exists_pos
  refine ⟨CG * CE, mul_pos hCG hCE, ?_⟩
  filter_upwards [hG, hE.bound.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hg he hz
  have hz' : z ≠ 0 := hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz'
  have hraw : ‖WasowLaurentActualResidual.rawDefect a h N c P B z‖ =
      ‖WasowClearedResidual.actualDefect a h N c P B z‖ / ‖z‖ ^ (a+h) := by
    rw [WasowLaurentActualResidual.rawDefect_eq a h N hh c P B hz']
    simp only [norm_smul, zpow_neg, zpow_natCast, norm_inv, norm_pow, div_eq_mul_inv, mul_comm]
  have he' : ‖WasowClearedResidual.actualDefect a h N c P B z‖ ≤ CE * ‖z‖ ^ N := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg z) N)] using he
  calc
    _ ≤ ‖(finiteGauge P a N z)⁻¹‖ * ‖WasowLaurentActualResidual.rawDefect a h N c P B z‖ :=
      norm_mul_le _ _
    _ ≤ (CG / ‖z‖ ^ b) * (CE * ‖z‖ ^ N / ‖z‖ ^ (a+h)) := by
      rw [hraw]
      apply mul_le_mul hg.2.2.2.2
        (div_le_div_of_nonneg_right he' (pow_nonneg (norm_nonneg z) _))
        (div_nonneg (norm_nonneg _) (by positivity)) (div_nonneg hCG.le (by positivity))
    _ = _ := by
      have hp : ‖z‖ ^ N = ‖z‖ ^ (a+b+h) * ‖z‖ ^ (N-(a+b+h)) := by
        rw [← pow_add, Nat.add_sub_of_le hN]
      rw [hp]
      simp only [pow_add]
      field_simp

/-- An arbitrary desired residual order is achieved after the fixed pole
losses, without any leading-identity hypothesis on the gauge. -/
theorem remainder_isBigO (a b h k : ℕ) (hh : 0 < h)
    {c : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hc : HasFPowerSeriesAt c s 0) (A P Q B : Series (m := m))
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n A)
    (hPQ : P * Q = PowerSeries.X ^ (a+b))
    (heq : WasowClearedResidual.Equation a h A P B) :
    remainder a h (a+b+h+k) c P B =O[𝓝[≠] (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ k) := by
  obtain ⟨C, _, hb⟩ := eventually_remainder_bound a b h (a+b+h+k) hh hc A P Q B
    hcoeff hPQ heq (by omega)
  apply IsBigO.of_bound C
  simpa only [Nat.add_sub_cancel_left, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hb

#print axioms finiteGauge_eq
#print axioms eventually_remainder_bound
#print axioms remainder_isBigO
end WasowLaurentRemainder
