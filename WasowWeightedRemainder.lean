import WasowActualTail
import WasowTruncatedGauge

/-! The actual transformed truncation remainder, including the true inverse
finite gauge and the `r^(q-1)` factor from `t=1/r`. The truncation order is chosen
after this loss: `N ≥ q+1` gives an integrable `O(r^-2)` remainder. No residual
estimate or integrability is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology Matrix.Norms.Operator
open Filter Asymptotics Set MeasureTheory
namespace WasowWeightedRemainder
open WasowMatrixPolynomial WasowActualTruncation WasowActualTail WasowTruncatedGauge

variable {m : ℕ}

local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by
    simp_rw [Matrix.linfty_opNNNorm_def]
    fun_prop

/-- The raw finite defect multiplied by the actual inverse finite gauge. -/
def normalizedDefect (a : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (q N : ℕ) (z : ℂ) :=
  (gauge P N z)⁻¹ * actualDefect a P B q N z

/-- The genuine transformed remainder in the inverse real variable. -/
def remainder (a : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (q N : ℕ) (r : ℝ) :=
  (r : ℂ) ^ (q - 1) • normalizedDefect a P B q N ((r : ℂ)⁻¹)

/-- Local invertibility of the actual finite gauge preserves the proved
vanishing order, and provides actual continuity on a whole neighborhood. -/
theorem normalizedDefect_control
    {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt a p 0)
    (A P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hc : ∀ n, p.coeff n = PowerSeries.coeff n A)
    (q N : ℕ) (hN : 0 < N) (hP : PowerSeries.constantCoeff P = 1)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P)) :
    (normalizedDefect a P B q N =O[𝓝 (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ N)) ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), ContinuousAt (normalizedDefect a P B q N) z := by
  have hg : Tendsto (gauge P N) (𝓝 (0 : ℂ)) (𝓝 1) := by
    have hh := (continuous_eval (PowerSeries.trunc N P)).tendsto 0
    change Tendsto (gauge P N) (𝓝 (0 : ℂ)) (𝓝 (gauge P N 0)) at hh
    rwa [gauge_zero P hN, hP] at hh
  have hinv : (fun z => (gauge P N z)⁻¹) =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) :=
    isBigO_const_of_tendsto (WasowMatrixBounds.tendsto_inv_of_tendsto_one hg) (by norm_num)
  refine ⟨?_, ?_⟩
  · exact (hinv.mul (actualDefect_isBigO ha A P B hc q N heq)).congr_right
      (fun z => one_mul (‖z‖ ^ N))
  · filter_upwards [ha.analyticAt.eventually_continuousAt,
      WasowMatrixBounds.eventually_det_ne_zero hg] with z hz hdet
    have hi : ContinuousAt (Inv.inv : Matrix (Fin m) (Fin m) ℂ → _) (gauge P N z) :=
      continuousAt_matrix_inv _ (by
        rw [Ring.inverse_eq_inv']
        exact continuousAt_inv₀ hdet)
    exact (hi.comp (continuous_eval (PowerSeries.trunc N P)).continuousAt).mul
      (actualDefect_continuousAt hz P B q N)

section WeightedTail
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Multiplication by the inverse-variable rank weight loses exactly `d`
powers. The retained two powers yield an actual continuous decaying tail. -/
theorem exists_weighted_inverse_tail_bound {f : ℂ → E} {N d : ℕ}
    (hf : ∀ᶠ z in 𝓝 (0 : ℂ), ContinuousAt f z)
    (hO : f =O[𝓝 (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ N)) (hN : d + 2 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (fun r : ℝ => (r : ℂ) ^ d • f ((r : ℂ)⁻¹)) (Ici R) ∧
      ∀ r : ℝ, R ≤ r → ‖(r : ℂ) ^ d • f ((r : ℂ)⁻¹)‖ ≤ C / r ^ 2 := by
  obtain ⟨C, hC, R, hR, hcont, hb⟩ := exists_inverse_tail_bound_of_isBigO hf hO
  refine ⟨C, hC, R, hR,
    (Complex.continuous_ofReal.pow d).continuousOn.smul hcont, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := hR.trans hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hpow : r ^ (d + 2) ≤ r ^ N := pow_le_pow_right₀ hr1 hN
  calc
    ‖(r : ℂ) ^ d • f ((r : ℂ)⁻¹)‖ = r ^ d * ‖f ((r : ℂ)⁻¹)‖ := by
      rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
    _ ≤ r ^ d * (C / r ^ N) := mul_le_mul_of_nonneg_left (hb r hr) (pow_nonneg hrpos.le _)
    _ ≤ r ^ d * (C / r ^ (d + 2)) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hC.le (pow_pos hrpos _) hpow) (pow_nonneg hrpos.le _)
    _ = C / r ^ 2 := by
      rw [pow_add]
      field_simp

/-- Genuine arbitrarily small tails, after the rank loss, beyond any requested
starting radius. Integrability follows from the explicit `C/r²` majorant. -/
theorem exists_small_weighted_inverse_tail {f : ℂ → E} {N d : ℕ}
    (hf : ∀ᶠ z in 𝓝 (0 : ℂ), ContinuousAt f z)
    (hO : f =O[𝓝 (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ N)) (hN : d + 2 ≤ N)
    (Rmin : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ Rmin ≤ R ∧
      ContinuousOn (fun r : ℝ => (r : ℂ) ^ d • f ((r : ℂ)⁻¹)) (Ici R) ∧
      IntegrableOn (fun r : ℝ => (r : ℂ) ^ d • f ((r : ℂ)⁻¹)) (Ici R) ∧
      (∫ r in Ici R, ‖(r : ℂ) ^ d • f ((r : ℂ)⁻¹)‖) < ε := by
  obtain ⟨C, _, a, ha, hc, hb⟩ := exists_weighted_inverse_tail_bound hf hO hN
  have hi : IntegrableOn (fun r : ℝ => (r : ℂ) ^ d • f ((r : ℂ)⁻¹)) (Ici a) := by
    refine Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi ?_
    have hmajor : IntegrableOn (fun r : ℝ => C * r ^ (-2 : ℝ)) (Ioi a) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        (lt_of_lt_of_le zero_lt_one ha)).const_mul C
    apply hmajor.mono' ((hc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [Real.rpow_neg (le_of_lt (lt_of_lt_of_le zero_lt_one (ha.trans hr.le))),
      Real.rpow_two, div_eq_mul_inv] using hb r hr.le
  let b := max a Rmin
  have hbi : IntegrableOn (fun r : ℝ => (r : ℂ) ^ d • f ((r : ℂ)⁻¹)) (Ioi b) :=
    hi.mono_set (by
      intro r hr
      change a ≤ r
      exact (le_max_left a Rmin).trans (le_of_lt hr))
  obtain ⟨R, hR, hs⟩ := CRGProgress.exists_small_tail
    (fun r : ℝ => (r : ℂ) ^ d • f ((r : ℂ)⁻¹)) b ε hbi hε
  have haR : a ≤ R := (le_max_left a Rmin).trans hR
  refine ⟨R, ha.trans haR, (le_max_right a Rmin).trans hR,
    hc.mono (Ici_subset_Ici.mpr haR), hi.mono_set (Ici_subset_Ici.mpr haR), ?_⟩
  rwa [integral_Ici_eq_integral_Ioi]

end WeightedTail

/-- The true inverse-gauge, rank-weighted remainder has a common continuous
and arbitrarily small integrable tail. All estimates are derived from the
actual coefficient expansion and the complete formal gauge equation. -/
theorem exists_small_remainder_tail
    {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt a p 0)
    (A P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hc : ∀ n, p.coeff n = PowerSeries.coeff n A)
    (q N : ℕ) (hq : 0 < q) (hN : q + 1 ≤ N) (hP : PowerSeries.constantCoeff P = 1)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P))
    (Rmin : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ Rmin ≤ R ∧
      ContinuousOn (remainder a P B q N) (Ici R) ∧
      IntegrableOn (remainder a P B q N) (Ici R) ∧
      (∫ r in Ici R, ‖remainder a P B q N r‖) < ε := by
  obtain ⟨hO, hcont⟩ := normalizedDefect_control ha A P B hc q N (by omega) hP heq
  exact exists_small_weighted_inverse_tail hcont hO (by omega : q - 1 + 2 ≤ N) Rmin hε

end WasowWeightedRemainder
#print axioms WasowWeightedRemainder.normalizedDefect_control
#print axioms WasowWeightedRemainder.exists_weighted_inverse_tail_bound
#print axioms WasowWeightedRemainder.exists_small_weighted_inverse_tail
#print axioms WasowWeightedRemainder.exists_small_remainder_tail
