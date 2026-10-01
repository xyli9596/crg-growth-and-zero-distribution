import LevinAnnulus
import LevinExceptional
import LevinIndicatorOrigin
import LevinZeroFree
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! The indicator inherits the quantitative logarithmic angular modulus from
actual annular integral majorants. The final result allows a zero at the origin. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Metric Real Complex
open scoped Topology
open LevinGrowth LevinDensity
namespace LevinIndicatorModulus

/-- The logarithmic modulus is strictly positive at every allowed scale,
including the endpoint `δ = 1`. -/
theorem modulus_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < LevinAnnulus.modulus δ := by
  have hl : Real.log (δ / 8) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  unfold LevinAnnulus.modulus
  exact add_pos_of_pos_of_nonneg hδ (mul_nonneg hδ.le (by linarith))

/-- An exceptional set occupying at most one quarter of a shell cannot cover
all of the radii where a nonnegative majorant is below twice its mean bound. -/
theorem exists_good_radius {E : Set ℝ} {P : ℝ → ℝ} {R c : ℝ}
    (hR : 0 < R) (hc : 0 < c)
    (hPm : Measurable P) (hPi : IntervalIntegrable P volume R (2 * R))
    (hPnonneg : ∀ r, 0 ≤ P r)
    (hPbound : (∫ r in R..(2 * R), P r) ≤ R * c)
    (hEbound : volume (E ∩ Icc 0 (2 * R)) ≤ ENNReal.ofReal (R / 4)) :
    ∃ r ∈ Ico R (2 * R), r ∉ E ∧ P r < 2 * c := by
  have hbad : volume (Ico R (2 * R) ∩ {r : ℝ | 2 * c ≤ P r}) ≤
      ENNReal.ofReal (R / 2) := by
    have hmarkov := LevinExceptional.shell_markov P hR.le (by positivity : 0 < 2 * c)
      hPm hPi hPnonneg (β := 1 / 2) (by nlinarith [hPbound])
    convert hmarkov using 1
    congr 1
    ring
  have hnot : ¬ Ico R (2 * R) ⊆
      (E ∩ Icc 0 (2 * R)) ∪ (Ico R (2 * R) ∩ {r : ℝ | 2 * c ≤ P r}) := by
    intro hsub
    have hmeasure := (measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add hEbound hbad))
    rw [Real.volume_Ico, ← ENNReal.ofReal_add (by positivity : 0 ≤ R / 4)
      (by positivity : 0 ≤ R / 2)] at hmeasure
    have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ R / 4 + R / 2)).mp hmeasure
    linarith
  obtain ⟨r, hr, hn⟩ := Set.not_subset.mp hnot
  refine ⟨r, hr, ?_, ?_⟩
  · intro hrE
    exact hn (Or.inl ⟨hrE, hR.le.trans hr.1, hr.2.le⟩)
  · by_contra h
    exact hn (Or.inr ⟨hr, le_of_not_gt h⟩)

/-- Uniform radial limits inherit the annular logarithmic modulus. This first
form has a nonzero value at the origin, as required by the local factorization. -/
theorem exists_indicator_modulus_of_ne_zero {f : ℂ → ℂ} {ρ : ℝ}
    {h : Direction → ℝ} (hf : Differentiable ℂ f) (hρ : 0 < ρ)
    (htype : FinitePositiveType f ρ) (hf0 : f 0 ≠ 0)
    (hreg : RadialRegular f ρ h) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ v w : Direction,
      dist v w ≤ δ → |h v - h w| ≤ K * LevinAnnulus.modulus δ := by
  obtain ⟨C, hC, hmajorant⟩ := LevinAnnulus.exists_annular_majorant hf hρ htype hf0
  obtain ⟨_, E, _, hEz, hlim⟩ := hreg
  let E' := E ∪ zeroRadii f
  have hE' : ZeroRadialDensity E' := hEz.union (zeroRadii_zero_density hf ⟨0, hf0⟩)
  obtain ⟨R₁, hR₁, hEsmall⟩ := hE' (1 / 8) (by norm_num)
  refine ⟨2 * C, by positivity, ?_⟩
  intro δ hδ hδ1 v w hvw
  have hmod : 0 < LevinAnnulus.modulus δ := modulus_pos hδ hδ1
  by_contra hn
  have hgap : 0 < |h v - h w| - (2 * C) * LevinAnnulus.modulus δ :=
    sub_pos.mpr (lt_of_not_ge hn)
  let ε := (|h v - h w| - (2 * C) * LevinAnnulus.modulus δ) / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨R₀, _, hgood⟩ := hlim ε hε
  let R := max 1 (max R₀ R₁)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR1
  have hRR₀ : R₀ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRR₁ : R₁ ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨P, hPm, hPi, hPnonneg, hPbound, hPosc⟩ := hmajorant R hR1 δ hδ hδ1
  have hmeasure : volume (E' ∩ Icc 0 (2 * R)) ≤ ENNReal.ofReal (R / 4) := by
    convert hEsmall (2 * R) (by linarith) using 1
    congr 1
    ring
  obtain ⟨r, hr, hrE, hPr⟩ := exists_good_radius hR0 (mul_pos hC hmod)
    hPm hPi hPnonneg (by nlinarith [hPbound]) hmeasure
  have hrE₀ : r ∉ E := fun he => hrE (Or.inl he)
  have hrZ : r ∉ zeroRadii f := fun hz => hrE (Or.inr hz)
  have hv := (hgood r (hRR₀.trans hr.1) hrE₀ v).2
  have hw := (hgood r (hRR₀.trans hr.1) hrE₀ w).2
  have hosc := hPosc r ⟨hr.1, hr.2.le⟩ hrZ v w hvw
  have htriangle : |h v - h w| ≤ |normalizedLog f ρ r v - h v| +
      |normalizedLog f ρ r v - normalizedLog f ρ r w| +
      |normalizedLog f ρ r w - h w| := by
    have ht₁ := abs_sub_le (h v) (normalizedLog f ρ r v) (h w)
    have ht₂ := abs_sub_le (normalizedLog f ρ r v) (normalizedLog f ρ r w) (h w)
    rw [abs_sub_comm (h v) (normalizedLog f ρ r v)] at ht₁
    linarith
  dsimp [ε] at hv hw
  nlinarith

/-- Every radial regular indicator of an entire function of finite positive
type has one fixed quantitative angular modulus, also when the origin is a zero. -/
theorem exists_indicator_modulus {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hreg : RadialRegular f ρ h) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ v w : Direction,
      dist v w ≤ δ → |h v - h w| ≤ K * LevinAnnulus.modulus δ := by
  obtain ⟨m, F, hF, hF0, hfactor, hFtype, _, _⟩ :=
    LevinOrigin.exists_origin_reduction hf hρ htype
  exact exists_indicator_modulus_of_ne_zero hF hρ hFtype hF0
    (LevinIndicatorOrigin.radialRegular_remove_monomial hρ hfactor hreg)

/-- The direction of a complex point, with the positive real direction chosen
at zero. Every use of its modulus below stays in an annulus away from zero. -/
def normalizedDirection (z : ℂ) : Direction :=
  if hz : z = 0 then ⟨1, norm_one⟩ else
    ⟨z / (‖z‖ : ℂ), by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hz)]⟩

/-- The homogeneous extension of the angular indicator to the complex plane. -/
def homogeneousIndicator (ρ : ℝ) (h : Direction → ℝ) (z : ℂ) : ℝ :=
  ‖z‖ ^ ρ * h (normalizedDirection z)

/-- Polar reconstruction, valid also under the chosen convention at zero. -/
theorem rayPoint_normalizedDirection (z : ℂ) :
    rayPoint ‖z‖ (normalizedDirection z) = z := by
  by_cases hz : z = 0
  · simp [normalizedDirection, rayPoint, hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    simp [normalizedDirection, rayPoint, hz, mul_div_cancel₀, hn]

/-- Radial normalization is quantitatively continuous away from zero. -/
theorem normalizedDirection_dist_le {z w : ℂ} (hz : 1 / 4 ≤ ‖z‖) :
    dist (normalizedDirection z) (normalizedDirection w) ≤ 8 * ‖z - w‖ := by
  let v := normalizedDirection z
  let u := normalizedDirection w
  have hzrepr : (‖z‖ : ℂ) * (v : ℂ) = z := rayPoint_normalizedDirection z
  have hwrepr : (‖w‖ : ℂ) * (u : ℂ) = w := rayPoint_normalizedDirection w
  have heq : (‖z‖ : ℂ) * ((v : ℂ) - (u : ℂ)) =
      z - w + ((‖w‖ : ℂ) - (‖z‖ : ℂ)) * (u : ℂ) := by
    linear_combination hzrepr - hwrepr
  have htri := norm_add_le (z - w) (((‖w‖ : ℂ) - (‖z‖ : ℂ)) * (u : ℂ))
  rw [← heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    norm_mul, u.property, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at htri
  have hrad := abs_norm_sub_norm_le w z
  rw [norm_sub_rev w z] at hrad
  have hprod : ‖z‖ * ‖(v : ℂ) - (u : ℂ)‖ ≤ 2 * ‖z - w‖ := by linarith
  have hnorm : 0 ≤ ‖(v : ℂ) - (u : ℂ)‖ := norm_nonneg _
  change dist v u ≤ _
  rw [Subtype.dist_eq, dist_eq_norm]
  nlinarith

/-- A real power has a fixed Lipschitz bound on the enlarged positive annulus. -/
theorem exists_rpow_lipschitz (ρ : ℝ) : ∃ D : ℝ, 0 < D ∧
    ∀ s ∈ Icc (1 / 4 : ℝ) 4, ∀ t ∈ Icc (1 / 4 : ℝ) 4,
      |s ^ ρ - t ^ ρ| ≤ D * |s - t| := by
  have hc : ContinuousOn (fun x : ℝ => ρ * x ^ (ρ - 1)) (Icc (1 / 4 : ℝ) 4) := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const x (ρ - 1)
      (Or.inl hx0))).continuousWithinAt
  obtain ⟨D, hD, hb⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  refine ⟨D, hD, fun s hs t ht => ?_⟩
  have hder (x : ℝ) (hx : x ∈ Icc (1 / 4 : ℝ) 4) :
      HasDerivWithinAt (fun x : ℝ => x ^ ρ) (ρ * x ^ (ρ - 1))
        (Icc (1 / 4 : ℝ) 4) x :=
    (Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1] : x ≠ 0))).hasDerivWithinAt
  have hbound (x : ℝ) (hx : x ∈ Icc (1 / 4 : ℝ) 4) : ‖ρ * x ^ (ρ - 1)‖ ≤ D :=
    hb _ (mem_image_of_mem _ hx)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc _ _) ht hs

/-- A quantitative polar modulus on the enlarged annulus. The same constant
handles angular variation and variation of the radial homogeneity factor. -/
theorem exists_polar_modulus {ρ : ℝ} {h : Direction → ℝ} (hρ : 0 ≤ ρ)
    (hh : Continuous h) {K : ℝ} (hK : 0 < K)
    (hmod : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ v w : Direction,
      dist v w ≤ δ → |h v - h w| ≤ K * LevinAnnulus.modulus δ) :
    ∃ L : ℝ, 0 < L ∧ ∀ s ∈ Icc (1 / 4 : ℝ) 4,
      ∀ t ∈ Icc (1 / 4 : ℝ) 4, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ v w : Direction, dist v w ≤ δ →
        |s ^ ρ * h v - t ^ ρ * h w| ≤ L * (|s - t| + LevinAnnulus.modulus δ) := by
  obtain ⟨M, hM, hb⟩ := (isCompact_range hh).isBounded.exists_pos_norm_le
  have hMh (w : Direction) : |h w| ≤ M := by
    simpa only [Real.norm_eq_abs] using hb (h w) (mem_range_self w)
  obtain ⟨D, hD, hpow⟩ := exists_rpow_lipschitz ρ
  let A := (4 : ℝ) ^ ρ * K
  let B := D * M
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := mul_pos hD hM
  refine ⟨A + B, by positivity, ?_⟩
  intro s hs t ht δ hδ hδ1 v w hvw
  have hs0 : 0 < s := by linarith [hs.1]
  have hsp : 0 ≤ s ^ ρ := Real.rpow_nonneg hs0.le _
  have hs4 : s ^ ρ ≤ (4 : ℝ) ^ ρ := Real.rpow_le_rpow hs0.le hs.2 hρ
  have hδ0 : 0 ≤ LevinAnnulus.modulus δ := (modulus_pos hδ hδ1).le
  have hangle := hmod δ hδ hδ1 v w hvw
  have hradial := hpow s hs t ht
  have hfirst : s ^ ρ * |h v - h w| ≤ A * LevinAnnulus.modulus δ := by
    calc
      _ ≤ (4 : ℝ) ^ ρ * (K * LevinAnnulus.modulus δ) :=
        mul_le_mul hs4 hangle (abs_nonneg _) (by positivity)
      _ = _ := by dsimp [A]; ring
  have hsecond : |s ^ ρ - t ^ ρ| * |h w| ≤ B * |s - t| := by
    calc
      _ ≤ (D * |s - t|) * M :=
        mul_le_mul hradial (hMh w) (abs_nonneg _) (by positivity)
      _ = _ := by dsimp [B]; ring
  have hsplit : |s ^ ρ * h v - t ^ ρ * h w| ≤
      s ^ ρ * |h v - h w| + |s ^ ρ - t ^ ρ| * |h w| := by
    calc
      _ = |s ^ ρ * (h v - h w) + (s ^ ρ - t ^ ρ) * h w| := by ring_nf
      _ ≤ |s ^ ρ * (h v - h w)| + |(s ^ ρ - t ^ ρ) * h w| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hsp]
  have hcross := add_nonneg (mul_nonneg hA.le (abs_nonneg (s - t)))
    (mul_nonneg hB.le hδ0)
  nlinarith

/-- The actual homogeneous indicator has a quantitative Euclidean modulus on
`1/4 ≤ ‖z‖, ‖w‖ ≤ 4`, with an angular normalization factor of eight. -/
theorem exists_homogeneous_modulus {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hreg : RadialRegular f ρ h) :
    ∃ L : ℝ, 0 < L ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 8 →
      ∀ z w : ℂ, ‖z‖ ∈ Icc (1 / 4 : ℝ) 4 → ‖w‖ ∈ Icc (1 / 4 : ℝ) 4 →
      ‖z - w‖ ≤ δ →
      |homogeneousIndicator ρ h z - homogeneousIndicator ρ h w| ≤
        L * (δ + LevinAnnulus.modulus (8 * δ)) := by
  obtain ⟨K, hK, hmod⟩ := exists_indicator_modulus hf hρ htype hreg
  obtain ⟨L, hL, hpolar⟩ := exists_polar_modulus hρ.le hreg.1 hK hmod
  refine ⟨L, hL, ?_⟩
  intro δ hδ hδ1 z w hz hw hzw
  have hdir : dist (normalizedDirection z) (normalizedDirection w) ≤ 8 * δ :=
    (normalizedDirection_dist_le hz.1).trans (mul_le_mul_of_nonneg_left hzw (by norm_num))
  have hrad : |‖z‖ - ‖w‖| ≤ δ := (abs_norm_sub_norm_le z w).trans hzw
  have hb := hpolar ‖z‖ hz ‖w‖ hw (8 * δ) (by positivity) (by linarith)
    (normalizedDirection z) (normalizedDirection w) hdir
  exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add hrad le_rfl) hL.le)

#print axioms modulus_pos
#print axioms exists_good_radius
#print axioms exists_indicator_modulus_of_ne_zero
#print axioms exists_indicator_modulus
#print axioms rayPoint_normalizedDirection
#print axioms normalizedDirection_dist_le
#print axioms exists_rpow_lipschitz
#print axioms exists_polar_modulus
#print axioms exists_homogeneous_modulus
end LevinIndicatorModulus
