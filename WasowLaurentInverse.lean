import WasowLaurentTruncation
import WasowTruncatedGauge

/-! True inverses of finite Laurent gauges with possibly singular cleared
leading matrices. The true formal inverse supplies the near-identity product;
its two pole orders, and thus both growth exponents, precede truncation. -/
set_option autoImplicit false
noncomputable section
open Set Filter Asymptotics
open scoped Topology Matrix.Norms.Operator
namespace WasowLaurentInverse
open WasowLaurentTruncation WasowMatrixPolynomial WasowTruncatedGauge
variable {m : ℕ}

def finiteGauge (P : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (a N : ℕ)
    (z : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (z ^ a)⁻¹ • eval (PowerSeries.trunc N P) z

/-- Exact actual finite-product error after both scalar pole factors. -/
theorem exists_product_error
    (P Q : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (a b N : ℕ)
    (hPQ : P * Q = PowerSeries.X ^ (a + b)) (hN : a + b ≤ N) :
    ∃ E : Polynomial (Matrix (Fin m) (Fin m) ℂ), ∀ z : ℂ, z ≠ 0 →
      finiteGauge P a N z * finiteGauge Q b N z =
        1 + z ^ (N - (a + b)) • eval E z := by
  obtain ⟨E, hE⟩ := trunc_product_divisible P Q (a + b) N hPQ
  refine ⟨E, fun z hz => ?_⟩
  have hev := congrArg (fun U => eval U z) hE
  rw [eval_sub, eval_mul, eval_X_pow_mul] at hev
  have hx : eval (Polynomial.X ^ (a + b) : Polynomial (Matrix (Fin m) (Fin m) ℂ)) z =
      z ^ (a + b) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    change evaluation z (Polynomial.X ^ (a + b)) = _
    rw [map_pow]
    change eval Polynomial.X z ^ (a + b) = _
    rw [eval_X, smul_pow, one_pow]
  rw [hx] at hev
  have hp : eval (PowerSeries.trunc N P) z * eval (PowerSeries.trunc N Q) z =
      z ^ (a + b) • (1 : Matrix (Fin m) (Fin m) ℂ) + z ^ N • eval E z := by
    rw [sub_eq_iff_eq_add] at hev
    simpa only [add_comm] using hev
  unfold finiteGauge
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (z ^ a)⁻¹ * (z ^ b)⁻¹ = (z ^ (a + b))⁻¹ by rw [pow_add, mul_inv]]
  rw [hp, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hz), one_smul]
  congr 2
  have hpow : z ^ N = z ^ (a + b) * z ^ (N - (a + b)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hz), one_mul]

/-- Sufficient finite truncation makes the actual product tend to identity
on the punctured complex neighborhood, without convergence of P or Q. -/
theorem finiteGauge_product_tendsto
    (P Q : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (a b N : ℕ)
    (hPQ : P * Q = PowerSeries.X ^ (a + b)) (hN : a + b < N) :
    Tendsto (fun z => finiteGauge P a N z * finiteGauge Q b N z)
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  obtain ⟨E, hE⟩ := exists_product_error P Q a b N hPQ hN.le
  have hn : N - (a + b) ≠ 0 := by omega
  have hc : Continuous (fun z : ℂ => (1 : Matrix (Fin m) (Fin m) ℂ) +
      z ^ (N - (a + b)) • eval E z) :=
    continuous_const.add ((continuous_id.pow _).smul (continuous_eval E))
  have hh : Tendsto (fun z : ℂ => (1 : Matrix (Fin m) (Fin m) ℂ) +
      z ^ (N - (a + b)) • eval E z) (𝓝[≠] (0 : ℂ))
      (𝓝 (1 + (0 : ℂ) ^ (N - (a + b)) • eval E 0)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  simp only [zero_pow hn, zero_smul, add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hE z hz).symm

/-- A product close to identity yields the true inverse through its right
factor. No inverse of a possibly singular leading coefficient is used. -/
theorem inverse_eq_right_factor (U V : Matrix (Fin m) (Fin m) ℂ)
    (hUV : (U * V).det ≠ 0) : U⁻¹ = V * (U * V)⁻¹ := by
  have hU : U.det ≠ 0 := by
    intro h
    apply hUV
    rw [Matrix.det_mul, h, zero_mul]
  calc
    U⁻¹ = U⁻¹ * ((U * V) * (U * V)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hUV), Matrix.mul_one]
    _ = (U⁻¹ * U) * (V * (U * V)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = V * (U * V)⁻¹ := by
      rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hU), Matrix.one_mul]

/-- Both pole exponents remain the original formal pole orders. The bound
constant and the punctured neighborhood may depend on the finite order N. -/
theorem eventually_inverse_bounds
    (P Q : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (a b N : ℕ)
    (hPQ : P * Q = PowerSeries.X ^ (a + b)) (hN : a + b < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      (finiteGauge P a N z).det ≠ 0 ∧
      (finiteGauge P a N z)⁻¹ * finiteGauge P a N z = 1 ∧
      finiteGauge P a N z * (finiteGauge P a N z)⁻¹ = 1 ∧
      ‖finiteGauge P a N z‖ ≤ C / ‖z‖ ^ a ∧
      ‖(finiteGauge P a N z)⁻¹‖ ≤ C / ‖z‖ ^ b := by
  let CP : ℝ := ‖eval (PowerSeries.trunc N P) 0‖ + 1
  let CQ : ℝ := ‖eval (PowerSeries.trunc N Q) 0‖ + 1
  let CI : ℝ := ‖(1 : Matrix (Fin m) (Fin m) ℂ)‖ + 1
  have hCP : 0 < CP := by dsimp [CP]; positivity
  have hCQ : 0 < CQ := by dsimp [CQ]; positivity
  have hCI : 0 < CI := by dsimp [CI]; positivity
  have hp : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖eval (PowerSeries.trunc N P) z‖ < CP :=
    (((continuous_eval (PowerSeries.trunc N P)).tendsto 0).norm.eventually
      (gt_mem_nhds (lt_add_one _))).filter_mono nhdsWithin_le_nhds
  have hq : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖eval (PowerSeries.trunc N Q) z‖ < CQ :=
    (((continuous_eval (PowerSeries.trunc N Q)).tendsto 0).norm.eventually
      (gt_mem_nhds (lt_add_one _))).filter_mono nhdsWithin_le_nhds
  have hlim := finiteGauge_product_tendsto P Q a b N hPQ hN
  have hi : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      ‖(finiteGauge P a N z * finiteGauge Q b N z)⁻¹‖ < CI :=
    (WasowMatrixBounds.tendsto_inv_of_tendsto_one hlim).norm.eventually
      (gt_mem_nhds (lt_add_one _))
  let C := CP + CQ * CI + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hp, hq, hi, WasowMatrixBounds.eventually_det_ne_zero hlim] with z hpz hqz hiz hdz
  have hd : (finiteGauge P a N z).det ≠ 0 := by
    intro hz
    apply hdz
    rw [Matrix.det_mul, hz, zero_mul]
  have hqp : ‖finiteGauge Q b N z‖ ≤ CQ / ‖z‖ ^ b := by
    calc
      _ = ‖eval (PowerSeries.trunc N Q) z‖ / ‖z‖ ^ b := by
        simp only [finiteGauge, norm_smul, norm_inv, norm_pow, div_eq_mul_inv, mul_comm]
      _ ≤ _ := div_le_div_of_nonneg_right hqz.le (by positivity)
  refine ⟨hd, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), ?_, ?_⟩
  · calc
      _ = ‖eval (PowerSeries.trunc N P) z‖ / ‖z‖ ^ a := by
        simp only [finiteGauge, norm_smul, norm_inv, norm_pow, div_eq_mul_inv, mul_comm]
      _ ≤ CP / ‖z‖ ^ a := div_le_div_of_nonneg_right hpz.le (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_right (by dsimp [C]; nlinarith [mul_pos hCQ hCI]) (by positivity)
  · rw [inverse_eq_right_factor _ _ hdz]
    calc
      _ ≤ ‖finiteGauge Q b N z‖ * ‖(finiteGauge P a N z * finiteGauge Q b N z)⁻¹‖ := norm_mul_le _ _
      _ ≤ (CQ / ‖z‖ ^ b) * CI :=
        mul_le_mul hqp hiz.le (norm_nonneg _) (div_nonneg hCQ.le (by positivity))
      _ = (CQ * CI) / ‖z‖ ^ b := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by dsimp [C]; linarith) (by positivity)

/-- The finite Laurent gauge has its actual complex derivative away from zero. -/
theorem finiteGauge_hasDerivAt
    (P : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (a N : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (finiteGauge P a N)
      ((z ^ a)⁻¹ • eval (PowerSeries.trunc N P).derivative z +
        (-(a : ℂ) * (z ^ (a + 1))⁻¹) • eval (PowerSeries.trunc N P) z) z := by
  have he : -(a : ℤ) - 1 = -((a + 1 : ℕ) : ℤ) := by omega
  have hh := (hasDerivAt_zpow (-(a : ℤ)) z (Or.inl hz)).smul
    (hasDerivAt_eval (PowerSeries.trunc N P) z)
  convert! hh using 1 <;>
    simp only [he, Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast]
  rfl

/-- The true inverse grows with the formal inverse's pole order, not the
cleared leading determinant's potentially larger vanishing order. -/
theorem finiteGauge_inverse_isBigO
    (P Q : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (a b N : ℕ)
    (hPQ : P * Q = PowerSeries.X ^ (a + b)) (hN : a + b < N) :
    (fun z => (finiteGauge P a N z)⁻¹) =O[𝓝[≠] (0 : ℂ)]
      (fun z : ℂ => (‖z‖ ^ b)⁻¹) := by
  obtain ⟨C, _, hh⟩ := eventually_inverse_bounds P Q a b N hPQ hN
  apply IsBigO.of_bound C
  filter_upwards [hh] with z hz
  simpa only [norm_inv, norm_pow, norm_norm, div_eq_mul_inv] using hz.2.2.2.2

/-- Actual inverse continuity holds on a punctured neighborhood, with no
convergence hypothesis on the original formal matrices. -/
theorem eventually_inverse_continuousAt
    (P Q : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (a b N : ℕ)
    (hPQ : P * Q = PowerSeries.X ^ (a + b)) (hN : a + b < N) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), ContinuousAt (fun w => (finiteGauge P a N w)⁻¹) z := by
  obtain ⟨_, _, hh⟩ := eventually_inverse_bounds P Q a b N hPQ hN
  filter_upwards [hh, self_mem_nhdsWithin] with z hz hzne
  have hi : ContinuousAt (Inv.inv : Matrix (Fin m) (Fin m) ℂ → _) (finiteGauge P a N z) :=
    continuousAt_matrix_inv _ (by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hz.1)
  exact hi.comp (finiteGauge_hasDerivAt P a N hzne).continuousAt

/-- The actual Laurent pair itself supplies every formal premise of the
finite-inverse bound. The pole orders are fixed functions of G and Q. -/
theorem eventually_inverse_bounds_of_laurent
    (G Q : Matrix (Fin m) (Fin m) WasowLaurentGauge.L)
    (hGQ : G * Q = 1) (hQG : Q * G = 1) (N : ℕ)
    (hN : poleOrder G + poleOrder Q < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      (finiteGauge (cleared G) (poleOrder G) N z).det ≠ 0 ∧
      (finiteGauge (cleared G) (poleOrder G) N z)⁻¹ *
        finiteGauge (cleared G) (poleOrder G) N z = 1 ∧
      finiteGauge (cleared G) (poleOrder G) N z *
        (finiteGauge (cleared G) (poleOrder G) N z)⁻¹ = 1 ∧
      ‖finiteGauge (cleared G) (poleOrder G) N z‖ ≤ C / ‖z‖ ^ poleOrder G ∧
      ‖(finiteGauge (cleared G) (poleOrder G) N z)⁻¹‖ ≤ C / ‖z‖ ^ poleOrder Q :=
  eventually_inverse_bounds (cleared G) (cleared Q) (poleOrder G) (poleOrder Q) N
    (cleared_inverse_pair G Q hGQ hQG).1 hN

/-- The inverse real variable approaches the punctured complex origin. -/
theorem inverse_real_tendsto_punctured :
    Tendsto (fun r : ℝ => (r : ℂ)⁻¹) atTop (𝓝[≠] (0 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨WasowAnalyticRemainder.inverse_real_tendsto_zero, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')

/-- Actual finite Laurent gauges and their true inverses have polynomial
bounds on a real tail, with the two fixed formal pole orders as exponents. -/
theorem exists_inverse_real_tail_bounds
    (P Q : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (a b N : ℕ)
    (hPQ : P * Q = PowerSeries.X ^ (a + b)) (hN : a + b < N) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧ ∀ r ≥ R,
      (finiteGauge P a N (r : ℂ)⁻¹).det ≠ 0 ∧
      (finiteGauge P a N (r : ℂ)⁻¹)⁻¹ * finiteGauge P a N (r : ℂ)⁻¹ = 1 ∧
      finiteGauge P a N (r : ℂ)⁻¹ * (finiteGauge P a N (r : ℂ)⁻¹)⁻¹ = 1 ∧
      ‖finiteGauge P a N (r : ℂ)⁻¹‖ ≤ C * r ^ a ∧
      ‖(finiteGauge P a N (r : ℂ)⁻¹)⁻¹‖ ≤ C * r ^ b := by
  obtain ⟨C, hC, hb⟩ := eventually_inverse_bounds P Q a b N hPQ hN
  obtain ⟨R, hR⟩ := eventually_atTop.mp (inverse_real_tendsto_punctured.eventually hb)
  refine ⟨C, hC, max 1 R, le_max_left _ _, fun r hr => ?_⟩
  have hn : 0 ≤ r := zero_le_one.trans ((le_max_left 1 R).trans hr)
  have hh := hR r ((le_max_right 1 R).trans hr)
  simpa only [norm_inv, Complex.norm_real, Real.norm_of_nonneg hn,
    inv_pow, div_inv_eq_mul] using hh

#print axioms inverse_real_tendsto_punctured
#print axioms exists_inverse_real_tail_bounds

#print axioms finiteGauge_hasDerivAt
#print axioms finiteGauge_inverse_isBigO
#print axioms eventually_inverse_continuousAt
#print axioms eventually_inverse_bounds_of_laurent

#print axioms inverse_eq_right_factor
#print axioms eventually_inverse_bounds

#print axioms exists_product_error
#print axioms finiteGauge_product_tendsto
end WasowLaurentInverse
