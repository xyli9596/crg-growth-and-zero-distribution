import WasowGaugeAssembly
import WasowRegularGauge

/-! Polynomial losses from conjugation by a genuine regular-singular gauge.
The truncation order is increased before constructing the actual small tail. -/
set_option autoImplicit false
noncomputable section
open Set Filter Asymptotics MeasureTheory
open scoped Topology Matrix.Norms.Operator
namespace WasowRegularTail
open WasowRegularSingular WasowGaugeAssembly WasowWeightedRemainder WasowActualTail
variable {m : ℕ}

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin m → ℂ))

local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by
    simp_rw [Matrix.linfty_opNNNorm_def]
    fun_prop

/-- The matrix operator norm follows directly from its action bound. -/
theorem matrix_norm_le_of_mulVec_bound (M : Matrix (Fin m) (Fin m) ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hM : ∀ x, ‖M.mulVec x‖ ≤ C * ‖x‖) : ‖M‖ ≤ C := by
  rw [← norm_toOperator]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  exact hM

/-- An integer exponent bounds both actual regular-singular factors. -/
theorem regular_norm_bounds [NeZero m] (G : Matrix (Fin m) (Fin m) ℂ) (θ : ℝ)
    (L : ℕ) (hL : ‖matrixOperator G‖ ≤ L) {r : ℝ} (hr : 1 ≤ r) :
    ‖rayPower G θ r‖ ≤ Real.exp (|θ| * ‖matrixOperator G‖) * r ^ L ∧
    ‖rayPowerInverse G θ r‖ ≤ Real.exp (|θ| * ‖matrixOperator G‖) * r ^ L := by
  have hp : r ^ ‖matrixOperator G‖ ≤ r ^ L := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hr hL
  have hc : 0 ≤ Real.exp (|θ| * ‖matrixOperator G‖) := (Real.exp_pos _).le
  have hb : Real.exp (|θ| * ‖matrixOperator G‖) * r ^ ‖matrixOperator G‖ ≤
      Real.exp (|θ| * ‖matrixOperator G‖) * r ^ L := mul_le_mul_of_nonneg_left hp hc
  constructor <;> apply matrix_norm_le_of_mulVec_bound _ (mul_nonneg hc (pow_nonneg (zero_le_one.trans hr) _))
  · intro x
    exact (rayPower_mulVec_bound G θ hr x).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  · intro x
    exact (rayPowerInverse_mulVec_bound G θ hr x).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- The concrete remainder after the constant regular-singular factor. -/
def conjugatedRemainder [NeZero m] (G : Matrix (Fin m) (Fin m) ℂ) (θ : ℝ)
    (a : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (q N : ℕ) (r : ℝ) :=
  rayPowerInverse G θ r * remainder a P B q N r * rayPower G θ r

/-- Pointwise conjugation costs at most the two integer growth exponents. -/
theorem conjugation_norm_bound [NeZero m] (G : Matrix (Fin m) (Fin m) ℂ) (θ : ℝ)
    (L d : ℕ) (hL : ‖matrixOperator G‖ ≤ L) {r : ℝ} (hr : 1 ≤ r)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    ‖rayPowerInverse G θ r * ((r : ℂ) ^ d • M) * rayPower G θ r‖ ≤
      (Real.exp (|θ| * ‖matrixOperator G‖)) ^ 2 *
        ‖(r : ℂ) ^ (d + 2 * L) • M‖ := by
  obtain ⟨ht, hs⟩ := regular_norm_bounds G θ L hL hr
  have hn : 0 ≤ r := zero_le_one.trans hr
  calc
    _ ≤ ‖rayPowerInverse G θ r‖ * ‖(r : ℂ) ^ d • M‖ * ‖rayPower G θ r‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (Real.exp (|θ| * ‖matrixOperator G‖) * r ^ L) *
        ‖(r : ℂ) ^ d • M‖ * (Real.exp (|θ| * ‖matrixOperator G‖) * r ^ L) := by
      gcongr
    _ = _ := by
      simp only [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hn,
        pow_add, pow_mul, norm_mul]
      ring

/-- Increasing the actual truncation order absorbs both regular-singular
polynomial losses and yields a continuous `C/r²` majorant. -/
theorem conjugated_remainder_control [NeZero m]
    (G : Matrix (Fin m) (Fin m) ℂ) (θ : ℝ) (L : ℕ)
    (hL : ‖matrixOperator G‖ ≤ L)
    {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt a p 0)
    (A P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hc : ∀ n, p.coeff n = PowerSeries.coeff n A)
    (q N : ℕ) (hq : 0 < q) (hN : q + 2 * L + 1 ≤ N)
    (hP : PowerSeries.constantCoeff P = 1)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P)) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (conjugatedRemainder G θ a P B q N) (Ici R) ∧
      ∀ r : ℝ, R ≤ r → ‖conjugatedRemainder G θ a P B q N r‖ ≤ C / r ^ 2 := by
  obtain ⟨hO, hf⟩ := normalizedDefect_control ha A P B hc q N (by omega) hP heq
  obtain ⟨C, hC, R₁, hR₁, _, hb⟩ := exists_weighted_inverse_tail_bound hf hO
    (by omega : q - 1 + 2 * L + 2 ≤ N)
  obtain ⟨_, _, R₂, _, hfc, _⟩ := exists_inverse_tail_bound_of_isBigO hf hO
  let K := (Real.exp (|θ| * ‖matrixOperator G‖)) ^ 2
  have hK : 0 < K := sq_pos_of_pos (Real.exp_pos _)
  refine ⟨K * C, mul_pos hK hC, max R₁ R₂,
    hR₁.trans (le_max_left _ _), ?_, ?_⟩
  · intro r hr
    have hr1 : 1 ≤ r := hR₁.trans ((le_max_left _ _).trans hr)
    have hrne : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le hr1)
    exact (((WasowRegularGauge.rayPowerInverse_continuousAt G θ hrne).continuousWithinAt.mul
      ((Complex.continuous_ofReal.pow (q - 1)).continuousAt.continuousWithinAt.smul
        ((hfc r (show R₂ ≤ r from (le_max_right R₁ R₂).trans hr)).mono
          (Ici_subset_Ici.mpr (le_max_right R₁ R₂))))).mul
          (WasowRegularGauge.rayPower_continuousAt G θ hrne).continuousWithinAt)
  · intro r hr
    have hr1 : 1 ≤ r := hR₁.trans ((le_max_left _ _).trans hr)
    calc
      _ ≤ K * ‖(r : ℂ) ^ (q - 1 + 2 * L) • normalizedDefect a P B q N ((r : ℂ)⁻¹)‖ :=
        conjugation_norm_bound G θ L (q - 1) hL hr1 _
      _ ≤ K * (C / r ^ 2) := mul_le_mul_of_nonneg_left
        (hb r ((le_max_left _ _).trans hr)) hK.le
      _ = _ := by ring

/-- The genuinely conjugated remainder has an arbitrarily small integrable
tail beyond every requested starting radius. No integrability is assumed. -/
theorem exists_small_conjugated_tail [NeZero m]
    (G : Matrix (Fin m) (Fin m) ℂ) (θ : ℝ) (L : ℕ)
    (hL : ‖matrixOperator G‖ ≤ L)
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
      ContinuousOn (conjugatedRemainder G θ a P B q N) (Ici R) ∧
      IntegrableOn (conjugatedRemainder G θ a P B q N) (Ici R) ∧
      (∫ r in Ici R, ‖conjugatedRemainder G θ a P B q N r‖) < ε := by
  obtain ⟨C, _, a₀, ha₀, hcont, hb⟩ :=
    conjugated_remainder_control G θ L hL ha A P B hc q N hq hN hP heq
  have hi : IntegrableOn (conjugatedRemainder G θ a P B q N) (Ici a₀) := by
    rw [IntegrableOn, ← restrict_Ioi_eq_restrict_Ici]
    have hmajor : IntegrableOn (fun r : ℝ => C * r ^ (-2 : ℝ)) (Ioi a₀) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        (zero_lt_one.trans_le ha₀)).const_mul C
    apply hmajor.mono' (f := conjugatedRemainder G θ a P B q N)
      ((hcont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [Real.rpow_neg (zero_le_one.trans (ha₀.trans hr.le)),
      Real.rpow_two, div_eq_mul_inv] using hb r hr.le
  let b := max a₀ Rmin
  have hbi : IntegrableOn (conjugatedRemainder G θ a P B q N) (Ioi b) :=
    hi.mono_set (by
      intro r hr
      change a₀ ≤ r
      exact (le_max_left a₀ Rmin).trans (le_of_lt hr))
  obtain ⟨R, hR, hs⟩ := CRGProgress.exists_small_tail
    (conjugatedRemainder G θ a P B q N) b ε hbi hε
  have haR : a₀ ≤ R := (le_max_left _ _).trans hR
  refine ⟨R, ha₀.trans haR, (le_max_right _ _).trans hR,
    hcont.mono (Ici_subset_Ici.mpr haR), hi.mono_set (Ici_subset_Ici.mpr haR), ?_⟩
  rwa [integral_Ici_eq_integral_Ioi]

end WasowRegularTail
#print axioms WasowRegularTail.matrix_norm_le_of_mulVec_bound
#print axioms WasowRegularTail.regular_norm_bounds
#print axioms WasowRegularTail.conjugation_norm_bound

#print axioms WasowRegularTail.conjugated_remainder_control
#print axioms WasowRegularTail.exists_small_conjugated_tail
