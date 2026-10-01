import LevinLocalFactor
import LevinFiniteProduct
import LevinAnalytic

/-! Uniform L¹ angular oscillation control on dyadic annuli, derived from entire
finite-type growth, Jensen's inequality and actual finite Blaschke factorizations. -/
set_option autoImplicit false
noncomputable section
open Set Metric Real Complex MeasureTheory intervalIntegral MeromorphicOn Filter
open scoped Topology
namespace LevinAnnulus

/-- The logarithmic modulus of continuity used for the radial integral estimate. -/
def modulus (δ : ℝ) : ℝ := δ + δ * (2 - Real.log (δ / 8))

theorem modulus_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ modulus δ := by
  have hl : Real.log (δ / 8) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  exact add_nonneg hδ.le (mul_nonneg hδ.le (by linarith))

theorem modulus_tendsto_zero : Tendsto modulus (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun δ : ℝ => 3 * δ - 8 * ((δ / 8) * Real.log (δ / 8))) :=
    (continuous_const.mul continuous_id).sub
      (continuous_const.mul (Real.continuous_mul_log.comp (continuous_id.div_const 8)))
  have heq : modulus = fun δ : ℝ => 3 * δ - 8 * ((δ / 8) * Real.log (δ / 8)) := by
    funext δ
    unfold modulus
    ring
  rw [heq]
  simpa using hc.tendsto 0

/-- Jensen supplies one polynomial bound for all local divisor counts at every
large radius. The radius of the local finite factor may vary with the scale. -/
theorem exists_uniform_zeroCount_bound {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 ≤ ρ)
    (htype : LevinGrowth.FinitePositiveType f ρ) (hf0 : f 0 ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R → ∀ S : ℝ, S ≤ 16 * R →
      ∀ hfS : AnalyticOnNhd ℂ f (closedBall 0 S),
        LevinFiniteProduct.zeroCount hfS ≤ K * R ^ ρ := by
  obtain ⟨B, hB, hb⟩ := LevinFiniteType.scaled_exp_bound hf.continuous hρ htype
  let K := (B * (8 : ℝ) ^ ρ + |Real.log ‖f 0‖|) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := div_pos (add_pos_of_pos_of_nonneg
    (mul_pos hB (Real.rpow_pos_of_pos (by norm_num) _)) (abs_nonneg _)) hlog2
  refine ⟨K, hK, fun R hR S hS hfS => ?_⟩
  have hR0 : 0 < R := by linarith
  have hf32 : AnalyticOnNhd ℂ f (closedBall 0 (32 * R)) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).mono (subset_univ _)
  have hf16 : AnalyticOnNhd ℂ f (closedBall 0 (16 * R)) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).mono (subset_univ _)
  have hball : ball (0 : ℂ) S ⊆ closedBall 0 (16 * R) := by
    intro z hz
    exact mem_closedBall_zero_iff.mpr ((mem_ball_zero_iff.mp hz).le.trans hS)
  have hmono : (∑ᶠ z, divisor f (ball 0 S) z : ℤ) ≤
      ∑ᶠ z, divisor f (closedBall 0 (16 * R)) z := by
    apply finsum_le_finsum' hfS.meromorphicOn.divisor_ball_support_finite
      ((divisor f (closedBall 0 (16 * R))).finiteSupport (isCompact_closedBall _ _))
    intro z
    by_cases hz : z ∈ ball 0 S
    · rw [divisor_apply ((hfS.mono ball_subset_closedBall).meromorphicOn) hz,
        divisor_apply hf16.meromorphicOn (hball hz)]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
      exact hf16.divisor_nonneg z
  have hj := CRGLevinAnalytic.zero_count_exp_bound (f := f) (c := 0)
    (r := 16 * R) (A := B * (8 * R) ^ ρ) (by positivity)
    (by positivity) (by
      have heq : 2 * (16 * R) = 32 * R := by ring
      simpa only [heq] using hf32) hf0 (by
      intro z hz
      apply hb (8 * R) (by linarith) z
      have hz' : ‖z‖ = 2 * (16 * R) := by simpa only [mem_sphere, dist_zero_right] using hz
      linarith)
  have hN : LevinFiniteProduct.zeroCount hfS ≤
      (B * (8 * R) ^ ρ - Real.log ‖f 0‖) / Real.log 2 := by
    rw [LevinFiniteProduct.zeroCount_eq_divisor_sum]
    exact (Int.cast_le.mpr hmono).trans hj
  have hp : 1 ≤ R ^ ρ := Real.one_le_rpow hR hρ
  have habs : -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| * R ^ ρ := by
    exact (neg_le_abs _).trans (le_mul_of_one_le_right (abs_nonneg _) hp)
  apply hN.trans
  rw [Real.mul_rpow (by norm_num) hR0.le]
  calc
    _ ≤ ((B * (8 : ℝ) ^ ρ + |Real.log ‖f 0‖|) * R ^ ρ) / Real.log 2 := by
      apply div_le_div_of_nonneg_right _ hlog2.le
      nlinarith
    _ = K * R ^ ρ := by dsimp [K]; ring

/-- Divisor support really consists of zeros; this direction does not need a
separate nontriviality hypothesis. -/
theorem zero_of_mem_zeroSupport {f : ℂ → ℂ} {S : ℝ}
    (hfS : AnalyticOnNhd ℂ f (closedBall 0 S)) {z : ℂ}
    (hz : z ∈ LevinFiniteProduct.zeroSupport hfS) : f z = 0 := by
  by_contra hne
  have hzdiv := (LevinFiniteProduct.mem_zeroSupport hfS).mp hz
  have hzball := (divisor f (ball 0 S)).supportWithinDomain hzdiv
  apply hzdiv
  rw [divisor_apply (hfS.mono ball_subset_closedBall).meromorphicOn hzball,
    (hfS z (ball_subset_closedBall hzball)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hne]
  simp

/-- The finite radial potential is globally measurable, including its convention
at the finite set of singular radii. -/
theorem measurable_radialPotential {f : ℂ → ℂ} {S : ℝ}
    (hfS : AnalyticOnNhd ℂ f (closedBall 0 S)) (R δ : ℝ) :
    Measurable (LevinFiniteProduct.radialPotential hfS R δ) := by
  unfold LevinFiniteProduct.radialPotential CRGLevinLogKernel.radialKernel
  fun_prop

/-- The zero-free local factor has a uniform angular bound throughout one annulus.
The larger disk has radius 8R, so the same factor is used for every r in [R,2R]. -/
theorem zero_free_annular_oscillation {g : ℂ → ℂ} {R r A ρ δ : ℝ} {v w : ℂ}
    (hR : 0 < R) (hr : r ∈ Icc R (2 * R)) (hA : 0 ≤ A) (_hδ : 0 ≤ δ)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 (8 * R)))
    (hgnz : ∀ z ∈ closedBall 0 (8 * R), g z ≠ 0)
    (hbound : ∀ z ∈ closedBall 0 (8 * R), Real.log ‖g z‖ ≤ A * (2 * R) ^ ρ)
    (hcenter : -(A * (2 * R) ^ ρ) ≤ Real.log ‖g 0‖)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : ‖v - w‖ ≤ δ) :
    |Real.log ‖g ((r : ℂ) * v)‖ - Real.log ‖g ((r : ℂ) * w)‖| ≤
      20 * A * (2 * R) ^ ρ * δ := by
  have hr0 : 0 < r := hR.trans_le hr.1
  have hv' : ‖(r : ℂ) * v‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hv]
  have hw' : ‖(r : ℂ) * w‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hw]
  have h := CRGLevinAnalytic.log_norm_quarter_disk_oscillation
    (R := 8 * R) (M := A * (2 * R) ^ ρ) (by positivity) (by positivity) hg hgnz
    (by rw [mem_closedBall_zero_iff, hv']; linarith [hr.2])
    (by rw [mem_closedBall_zero_iff, hw']; linarith [hr.2]) hbound hcenter
  have heq : ‖(r : ℂ) * v - (r : ℂ) * w‖ = r * ‖v - w‖ := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  rw [heq] at h
  have hdist : r * ‖v - w‖ ≤ 2 * R * δ :=
    mul_le_mul hr.2 hvw (norm_nonneg _) (by positivity)
  calc
    _ ≤ _ := h
    _ ≤ (80 * (A * (2 * R) ^ ρ) / (8 * R)) * (2 * R * δ) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = _ := by field_simp; ring

/-- Explicit nonnegative majorant: one uniform angular term plus the actual
finite divisor potential normalized at the annulus scale. -/
def majorant {f : ℂ → ℂ} {S : ℝ} (hfS : AnalyticOnNhd ℂ f (closedBall 0 S))
    (G R ρ δ r : ℝ) : ℝ := G * δ + LevinFiniteProduct.radialPotential hfS R δ r / R ^ ρ

theorem measurable_majorant {f : ℂ → ℂ} {S : ℝ}
    (hfS : AnalyticOnNhd ℂ f (closedBall 0 S)) (G R ρ δ : ℝ) :
    Measurable (majorant hfS G R ρ δ) := by
  exact measurable_const.add ((measurable_radialPotential hfS R δ).div_const _)

theorem majorant_nonneg {f : ℂ → ℂ} {S G R ρ δ r : ℝ}
    (hfS : AnalyticOnNhd ℂ f (closedBall 0 S)) (hG : 0 ≤ G) (hR : 0 < R) (hδ : 0 ≤ δ) :
    0 ≤ majorant hfS G R ρ δ r := by
  exact add_nonneg (mul_nonneg hG hδ) (div_nonneg
    (LevinFiniteProduct.radialPotential_nonneg hfS hR.le hδ) (Real.rpow_nonneg hR.le _))

theorem majorant_intervalIntegrable {f : ℂ → ℂ} {S G R ρ δ : ℝ}
    (hfS : AnalyticOnNhd ℂ f (closedBall 0 S)) (hR : 0 < R) (hδ : 0 < δ) :
    IntervalIntegrable (majorant hfS G R ρ δ) volume R (2 * R) := by
  exact intervalIntegrable_const.add
    ((LevinFiniteProduct.radialPotential_intervalIntegrable hfS hR hδ).div_const _)

theorem integral_majorant_bound {f : ℂ → ℂ} {S G K R ρ δ : ℝ}
    (hfS : AnalyticOnNhd ℂ f (closedBall 0 S)) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hS : S ≤ 16 * R)
    (hN : LevinFiniteProduct.zeroCount hfS ≤ K * R ^ ρ) :
    (∫ r in R..(2 * R), majorant hfS G R ρ δ r) ≤
      (G + 4 * K) * R * modulus δ := by
  have hp : 0 < R ^ ρ := Real.rpow_pos_of_pos hR _
  have hl : 0 ≤ 2 - Real.log (δ / 8) := by
    have h := Real.log_nonpos (by positivity : 0 ≤ δ / 8) (by linarith : δ / 8 ≤ 1)
    linarith
  have hb := LevinFiniteProduct.integral_radialPotential_bound hfS hR hδ hδ1 hS
  have hBN := mul_le_mul_of_nonneg_right hN
    (show 0 ≤ R * δ + 4 * R * δ * (2 - Real.log (δ / 8)) by positivity)
  have hdiv : (∫ r in R..(2 * R), LevinFiniteProduct.radialPotential hfS R δ r) / R ^ ρ ≤
      K * (R * δ + 4 * R * δ * (2 - Real.log (δ / 8))) := by
    apply (div_le_iff₀ hp).mpr
    calc
      _ ≤ _ := hb.trans hBN
      _ = _ := by ring
  change (∫ r in R..(2 * R), G * δ + LevinFiniteProduct.radialPotential hfS R δ r / R ^ ρ) ≤ _
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((LevinFiniteProduct.radialPotential_intervalIntegrable hfS hR hδ).div_const _),
    intervalIntegral.integral_const, intervalIntegral.integral_div, smul_eq_mul]
  calc
    _ ≤ (2 * R - R) * (G * δ) + K * (R * δ + 4 * R * δ * (2 - Real.log (δ / 8))) :=
      add_le_add_right hdiv _
    _ ≤ _ := by
      unfold modulus
      nlinarith [mul_nonneg (mul_nonneg hG (mul_nonneg hR.le hδ.le)) hl,
        mul_nonneg (mul_nonneg hK hR.le) hδ.le]

/-- Annular angular control for general entire finite-type functions with zeros.
For every large annulus and angular tolerance, the measurable nonnegative
majorant is constructed from a genuine finite Blaschke factorization. Its L¹
cost is uniform over all scales. -/
theorem exists_annular_majorant {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ)
    (htype : LevinGrowth.FinitePositiveType f ρ) (hf0 : f 0 ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ P : ℝ → ℝ, Measurable P ∧ IntervalIntegrable P volume R (2 * R) ∧
        (∀ r : ℝ, 0 ≤ P r) ∧ (∫ r in R..(2 * R), P r) ≤ C * R * modulus δ ∧
        ∀ r ∈ Icc R (2 * R), r ∉ LevinGrowth.zeroRadii f →
          ∀ v w : LevinGrowth.Direction, dist v w ≤ δ →
            |LevinGrowth.normalizedLog f ρ r v - LevinGrowth.normalizedLog f ρ r w| ≤ P r := by
  obtain ⟨A, hA, hlocal⟩ := LevinLocalFactor.exists_scaled_local_factor hf hρ.le htype hf0
  obtain ⟨K, hK, hcount⟩ := exists_uniform_zeroCount_bound hf hρ.le htype hf0
  let G : ℝ := 20 * A * (2 : ℝ) ^ ρ
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨G + 4 * K, by positivity, fun R hR δ hδ hδ1 => ?_⟩
  have hR0 : 0 < R := by linarith
  obtain ⟨S, hSlow, hSup, g, D, hg, hgnz, heq, hbound, hcenter⟩ :=
    hlocal (2 * R) (by linarith)
  have hS8 : 8 * R < S := by linarith
  have hS16 : S < 16 * R := by linarith
  have hS0 : 0 < S := by linarith
  have hfS : AnalyticOnNhd ℂ f (closedBall 0 S) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).mono (subset_univ _)
  have hboundary : ∀ z ∈ sphere 0 S, f z ≠ 0 := by
    intro z hz
    rw [heq z (sphere_subset_closedBall hz)]
    apply mul_ne_zero _ (hgnz z (sphere_subset_closedBall hz))
    apply norm_ne_zero_iff.mp
    rw [LevinFactorization.norm_finiteBlaschke_on_sphere hfS hz]
    norm_num
  have hsmall : closedBall (0 : ℂ) (8 * R) ⊆ closedBall 0 S :=
    closedBall_subset_closedBall hS8.le
  refine ⟨majorant hfS G R ρ δ, measurable_majorant hfS G R ρ δ,
    majorant_intervalIntegrable hfS hR0 hδ,
    fun r => majorant_nonneg hfS hG.le hR0 hδ.le,
    integral_majorant_bound hfS hG.le hK.le hR0 hδ hδ1 hS16.le (hcount R hR S hS16.le hfS), ?_⟩
  intro r hr hnot v w hvw
  have hr0 : 0 < r := hR0.trans_le hr.1
  have hdist : ‖v.val - w.val‖ ≤ δ := by simpa only [Subtype.dist_eq, dist_eq_norm] using hvw
  have hgap : ∀ a ∈ LevinFiniteProduct.zeroSupport hfS, r ≠ ‖a‖ := by
    intro a ha heqr
    exact hnot ⟨a, zero_of_mem_zeroSupport hfS ha, heqr.symm⟩
  have hraw := LevinFiniteProduct.log_norm_angular_bound hS0 hfS hf0 hboundary D
    hr0 (by linarith [hr.2]) hr.2 hδ.le v.property w.property hdist hgap
  have hgraw := zero_free_annular_oscillation hR0 hr hA.le hδ.le
    (hg.mono hsmall) (fun z hz => hgnz z (hsmall hz))
    (fun z hz => hbound z (hsmall hz)) hcenter v.property w.property hdist
  have hraw' : |Real.log ‖f ((r : ℂ) * v.val)‖ - Real.log ‖f ((r : ℂ) * w.val)‖| ≤
      20 * A * (2 * R) ^ ρ * δ + LevinFiniteProduct.radialPotential hfS R δ r :=
    hraw.trans (add_le_add_left hgraw _)
  have hpot : 0 ≤ LevinFiniteProduct.radialPotential hfS R δ r :=
    LevinFiniteProduct.radialPotential_nonneg hfS hR0.le hδ.le
  have hRp : 0 < R ^ ρ := Real.rpow_pos_of_pos hR0 _
  have hrp : 0 < r ^ ρ := Real.rpow_pos_of_pos hr0 _
  have hpow : R ^ ρ ≤ r ^ ρ := Real.rpow_le_rpow hR0.le hr.1 hρ.le
  change |Real.log ‖f ((r : ℂ) * v.val)‖ / r ^ ρ -
    Real.log ‖f ((r : ℂ) * w.val)‖ / r ^ ρ| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hrp]
  calc
    _ ≤ (20 * A * (2 * R) ^ ρ * δ + LevinFiniteProduct.radialPotential hfS R δ r) / r ^ ρ :=
      div_le_div_of_nonneg_right hraw' hrp.le
    _ ≤ (20 * A * (2 * R) ^ ρ * δ + LevinFiniteProduct.radialPotential hfS R δ r) / R ^ ρ :=
      div_le_div_of_nonneg_left (by positivity) hRp hpow
    _ = majorant hfS G R ρ δ r := by
      rw [Real.mul_rpow (by norm_num) hR0.le]
      dsimp [majorant, G]
      field_simp

#print axioms modulus_nonneg
#print axioms modulus_tendsto_zero
#print axioms exists_uniform_zeroCount_bound
#print axioms zero_of_mem_zeroSupport
#print axioms measurable_radialPotential
#print axioms zero_free_annular_oscillation
#print axioms measurable_majorant
#print axioms majorant_nonneg
#print axioms majorant_intervalIntegrable
#print axioms integral_majorant_bound
#print axioms exists_annular_majorant
end LevinAnnulus
