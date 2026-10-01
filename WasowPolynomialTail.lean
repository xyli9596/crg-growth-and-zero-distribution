import WasowRegularTail

/-! Finite truncation pays for any actual polynomially bounded regular gauge.
In particular the regular coefficient need not be the constant matrix G/r.
Only the genuine T and S bounds and continuity are used in the tail estimate. -/
set_option autoImplicit false
noncomputable section
open Set Filter Asymptotics MeasureTheory
open scoped Topology Matrix.Norms.Operator
namespace WasowPolynomialTail
open WasowGaugeAssembly WasowWeightedRemainder WasowActualTail
variable {m : ℕ}
local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin m → ℂ))
local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by simp_rw [Matrix.linfty_opNNNorm_def]; fun_prop

structure Control (T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (L : ℕ) where
  C : ℝ
  C_pos : 0 < C
  R : ℝ
  R_one : 1 ≤ R
  T_continuous : ContinuousOn T (Ici R)
  S_continuous : ContinuousOn S (Ici R)
  T_bound : ∀ r ≥ R, ‖T r‖ ≤ C * r ^ L
  S_bound : ∀ r ≥ R, ‖S r‖ ≤ C * r ^ L

def conjugatedRemainder (T S : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (a : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (q N : ℕ) (r : ℝ) :=
  S r * remainder a P B q N r * T r

theorem conjugation_norm_bound (T S : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (L d : ℕ) (h : Control T S L) {r : ℝ} (hr : h.R ≤ r)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    ‖S r * ((r : ℂ) ^ d • M) * T r‖ ≤ h.C ^ 2 * ‖(r : ℂ) ^ (d + 2 * L) • M‖ := by
  have hn : 0 ≤ r := zero_le_one.trans (h.R_one.trans hr)
  calc
    _ ≤ ‖S r‖ * ‖(r : ℂ) ^ d • M‖ * ‖T r‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (h.C * r ^ L) * ‖(r : ℂ) ^ d • M‖ * (h.C * r ^ L) := by
      gcongr
      · exact mul_nonneg (mul_nonneg h.C_pos.le (pow_nonneg hn _)) (norm_nonneg _)
      · exact h.S_bound r hr
      · exact h.T_bound r hr
    _ = _ := by
      simp only [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hn,
        pow_add, pow_mul, norm_mul]
      ring

/-- A full analytic-to-formal coefficient match produces an actual inverse
square majorant after both polynomially bounded factors. -/
theorem conjugated_remainder_control
    (T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (L : ℕ) (h : Control T S L)
    {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt a p 0)
    (A P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hc : ∀ n, p.coeff n = PowerSeries.coeff n A)
    (q N : ℕ) (hq : 0 < q) (hN : q + 2 * L + 1 ≤ N)
    (hP : PowerSeries.constantCoeff P = 1)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P)) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (conjugatedRemainder T S a P B q N) (Ici R) ∧
      ∀ r : ℝ, R ≤ r → ‖conjugatedRemainder T S a P B q N r‖ ≤ C / r ^ 2 := by
  obtain ⟨hO, hf⟩ := normalizedDefect_control ha A P B hc q N (by omega) hP heq
  obtain ⟨C, hC, R₁, hR₁, _, hb⟩ := exists_weighted_inverse_tail_bound hf hO
    (by omega : q - 1 + 2 * L + 2 ≤ N)
  obtain ⟨_, _, R₂, _, hfc, _⟩ := exists_inverse_tail_bound_of_isBigO hf hO
  let R := max h.R (max R₁ R₂)
  have hR : h.R ≤ R := le_max_left _ _
  have hR₁' : R₁ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR₂' : R₂ ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨h.C ^ 2 * C, mul_pos (sq_pos_of_pos h.C_pos) hC, R,
    h.R_one.trans hR, ?_, ?_⟩
  · exact ((h.S_continuous.mono (Ici_subset_Ici.mpr hR)).mul
      ((Complex.continuous_ofReal.pow (q - 1)).continuousOn.smul
        (hfc.mono (Ici_subset_Ici.mpr hR₂')))).mul
      (h.T_continuous.mono (Ici_subset_Ici.mpr hR))
  · intro r hr
    calc
      _ ≤ h.C ^ 2 * ‖(r : ℂ) ^ (q - 1 + 2 * L) • normalizedDefect a P B q N ((r : ℂ)⁻¹)‖ :=
        conjugation_norm_bound T S L (q - 1) h (hR.trans hr) _
      _ ≤ h.C ^ 2 * (C / r ^ 2) := mul_le_mul_of_nonneg_left
        (hb r (hR₁'.trans hr)) (sq_nonneg _)
      _ = _ := by ring

/-- Arbitrarily small true conjugated tails follow beyond any chosen radius. -/
theorem exists_small_conjugated_tail
    (T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (L : ℕ) (h : Control T S L)
    {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt a p 0)
    (A P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hc : ∀ n, p.coeff n = PowerSeries.coeff n A)
    (q N : ℕ) (hq : 0 < q) (hN : q + 2 * L + 1 ≤ N)
    (hP : PowerSeries.constantCoeff P = 1)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P))
    (Rmin : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ Rmin ≤ R ∧
      ContinuousOn (conjugatedRemainder T S a P B q N) (Ici R) ∧
      IntegrableOn (conjugatedRemainder T S a P B q N) (Ici R) ∧
      (∫ r in Ici R, ‖conjugatedRemainder T S a P B q N r‖) < ε := by
  obtain ⟨C, _, a₀, ha₀, hcont, hb⟩ :=
    conjugated_remainder_control T S L h ha A P B hc q N hq hN hP heq
  have hi : IntegrableOn (conjugatedRemainder T S a P B q N) (Ici a₀) := by
    rw [IntegrableOn, ← restrict_Ioi_eq_restrict_Ici]
    have hmajor : IntegrableOn (fun r : ℝ => C * r ^ (-2 : ℝ)) (Ioi a₀) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        (zero_lt_one.trans_le ha₀)).const_mul C
    apply hmajor.mono' (f := conjugatedRemainder T S a P B q N)
      ((hcont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [Real.rpow_neg (zero_le_one.trans (ha₀.trans hr.le)),
      Real.rpow_two, div_eq_mul_inv] using hb r hr.le
  let b := max a₀ Rmin
  have hbi : IntegrableOn (conjugatedRemainder T S a P B q N) (Ioi b) :=
    hi.mono_set (by
      intro r hr
      change a₀ ≤ r
      exact (le_max_left a₀ Rmin).trans (le_of_lt hr))
  obtain ⟨R, hR, hs⟩ := CRGProgress.exists_small_tail
    (conjugatedRemainder T S a P B q N) b ε hbi hε
  have haR : a₀ ≤ R := (le_max_left _ _).trans hR
  refine ⟨R, ha₀.trans haR, (le_max_right _ _).trans hR,
    hcont.mono (Ici_subset_Ici.mpr haR), hi.mono_set (Ici_subset_Ici.mpr haR), ?_⟩
  rwa [integral_Ici_eq_integral_Ioi]

#print axioms conjugation_norm_bound
#print axioms conjugated_remainder_control
#print axioms exists_small_conjugated_tail
end WasowPolynomialTail
