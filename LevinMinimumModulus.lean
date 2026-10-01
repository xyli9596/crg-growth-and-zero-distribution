import LevinAnnulus
import LevinCartan

/-! Local minimum-modulus estimates using the actual analytic zero divisor.
The finite point covering theorem is kept separate from these analytic estimates. -/
noncomputable section
open Set Metric Real Complex ComplexConjugate MeromorphicOn
namespace LevinMinimumModulus

/-- Each analytic zero appears as many times as its actual multiplicity. -/
abbrev ZeroIndex {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) :=
  Σ a : LevinFiniteProduct.zeroSupport hf, Fin ((divisor f (ball 0 S) a).toNat)

theorem zeroIndex_prod {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (P : ℂ → ℝ) :
    (∏ i : ZeroIndex hf, P i.1.val) =
      ∏ a ∈ LevinFiniteProduct.zeroSupport hf, P a ^ (divisor f (ball 0 S) a).toNat := by
  classical
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact Finset.prod_coe_sort (LevinFiniteProduct.zeroSupport hf)
    (fun a => P a ^ (divisor f (ball 0 S) a).toNat)

theorem zeroIndex_card {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) :
    (Fintype.card (ZeroIndex hf) : ℝ) = LevinFiniteProduct.zeroCount hf := by
  classical
  simp only [ZeroIndex, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum,
    LevinFiniteProduct.zeroCount, LevinFiniteProduct.multiplicity]
  rw [Finset.sum_coe_sort (LevinFiniteProduct.zeroSupport hf)
    (fun a => ((divisor f (ball 0 S) a).toNat : ℝ))]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Int.cast_natCast, Int.toNat_of_nonneg ((hf.mono ball_subset_closedBall).divisor_nonneg a)]

theorem norm_finiteBlaschke_eq_prod {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (z : ℂ) :
    ‖LevinFactorization.finiteBlaschke f S z‖ =
      ∏ i : ZeroIndex hf, ‖(canonicalFactor S i.1.val z)⁻¹‖ := by
  classical
  rw [LevinFactorization.finiteBlaschke,
    finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop)
      hf.meromorphicOn.divisor_ball_support_finite,
    Finset.prod_apply, norm_prod,
    zeroIndex_prod hf (fun a => ‖(canonicalFactor S a z)⁻¹‖)]
  apply Finset.prod_congr rfl
  intro a ha
  have hn := (hf.mono ball_subset_closedBall).divisor_nonneg a
  simp only [Pi.pow_apply, zpow_neg, norm_inv, norm_zpow]
  rw [← zpow_natCast, Int.toNat_of_nonneg hn, inv_zpow]

/-- A single genuine Blaschke factor is bounded below by a scaled distance. -/
theorem inverse_canonical_lower {S : ℝ} {a z : ℂ}
    (hS : 0 < S) (ha : a ∈ ball 0 S) (hz : z ∈ closedBall 0 S) :
    ‖z - a‖ / (2 * S) ≤ ‖(canonicalFactor S a z)⁻¹‖ := by
  have haS : ‖a‖ ≤ S := (mem_ball_zero_iff.mp ha).le
  have hzS : ‖z‖ ≤ S := mem_closedBall_zero_iff.mp hz
  have hden : 0 < ‖(S : ℂ)^2 - conj a * z‖ :=
    norm_pos_iff.mpr (LevinFactorization.canonical_numerator_ne_zero ha hz)
  have hb : ‖(S : ℂ)^2 - conj a * z‖ ≤ 2 * S^2 := by
    calc
      _ ≤ ‖(S : ℂ)^2‖ + ‖conj a * z‖ := norm_sub_le _ _
      _ = S^2 + ‖a‖ * ‖z‖ := by
        simp [Complex.norm_real, abs_of_pos hS]
      _ ≤ 2 * S^2 := by nlinarith [mul_le_mul haS hzS (norm_nonneg _) hS.le]
  rw [canonicalFactor_apply, inv_div, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  calc
    ‖z-a‖ / (2*S) = S * ‖z-a‖ / (2*S^2) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden hb

theorem finiteBlaschke_product_lower {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (hS : 0 < S)
    {z : ℂ} (hz : z ∈ closedBall 0 S) :
    (∏ i : ZeroIndex hf, ‖z - i.1.val‖) / (2*S) ^ Fintype.card (ZeroIndex hf) ≤
      ‖LevinFactorization.finiteBlaschke f S z‖ := by
  classical
  rw [norm_finiteBlaschke_eq_prod hf]
  have heq : (∏ i : ZeroIndex hf, ‖z - i.1.val‖ / (2*S)) =
      (∏ i : ZeroIndex hf, ‖z - i.1.val‖) / (2*S)^Fintype.card (ZeroIndex hf) := by
    rw [Finset.prod_div_distrib]; simp
  rw [← heq]
  apply Finset.prod_le_prod
  · intro i _; positivity
  · intro i _
    apply inverse_canonical_lower hS _ hz
    exact (divisor f (ball 0 S)).supportWithinDomain
      ((LevinFiniteProduct.mem_zeroSupport hf).mp i.1.property)

/-- Jensen counts the actual local zeros using the outer disk bound. -/
theorem zeroCount_local_bound {f : ℂ → ℂ} {R S M : ℝ}
    (hf : Differentiable ℂ f) (hR : 0 < R) (hM : 0 ≤ M)
    (hf0 : f 0 = 1) (hS : S ≤ 4*R)
    (hbound : ∀ z ∈ closedBall 0 (8*R), ‖f z‖ ≤ Real.exp M)
    (hfS : AnalyticOnNhd ℂ f (closedBall 0 S)) :
    LevinFiniteProduct.zeroCount hfS ≤ M / Real.log 2 := by
  have ha := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hf4 : AnalyticOnNhd ℂ f (closedBall 0 (4*R)) := ha.mono (subset_univ _)
  have hsub : ball (0 : ℂ) S ⊆ closedBall 0 (4*R) := by
    intro z hz
    exact mem_closedBall_zero_iff.mpr ((mem_ball_zero_iff.mp hz).le.trans hS)
  have hmono : (∑ᶠ z, divisor f (ball 0 S) z : ℤ) ≤
      ∑ᶠ z, divisor f (closedBall 0 (4*R)) z := by
    apply finsum_le_finsum' hfS.meromorphicOn.divisor_ball_support_finite
      ((divisor f (closedBall 0 (4*R))).finiteSupport (isCompact_closedBall _ _))
    intro z
    by_cases hz : z ∈ ball 0 S
    · rw [divisor_apply (hfS.mono ball_subset_closedBall).meromorphicOn hz,
        divisor_apply hf4.meromorphicOn (hsub hz)]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
      exact hf4.divisor_nonneg z
  have hj := CRGLevinAnalytic.zero_count_exp_bound (f := f) (c := 0)
    (r := 4*R) (A := M) (by positivity) hM (ha.mono (subset_univ _))
    (by simp [hf0]) (by
      intro z hz
      apply hbound z
      have hz' : ‖z‖ = 2*(4*R) := by simpa [mem_sphere, dist_zero_right] using hz
      rw [mem_closedBall_zero_iff, hz']; linarith)
  rw [LevinFiniteProduct.zeroCount_eq_divisor_sum]
  exact (Int.cast_le.mpr hmono).trans (by simpa [hf0] using hj)

/-- Actual local factorization and its lower bound; no minimum-modulus estimate
for the original function is assumed here. -/
theorem exists_local_decomposition {f : ℂ → ℂ} {R M : ℝ}
    (hf : Differentiable ℂ f) (hR : 0 < R) (hM : 0 ≤ M)
    (hf0 : f 0 = 1)
    (hbound : ∀ z ∈ closedBall 0 (8*R), ‖f z‖ ≤ Real.exp M) :
    ∃ S : ℝ, 2*R < S ∧ S < 4*R ∧
      ∃ (hfS : AnalyticOnNhd ℂ f (closedBall 0 S)) (g : ℂ → ℂ),
        (∀ z ∈ closedBall 0 S, g z ≠ 0) ∧
        (∀ z ∈ closedBall 0 S, f z = LevinFactorization.finiteBlaschke f S z * g z) ∧
        LevinFiniteProduct.zeroCount hfS ≤ M / Real.log 2 ∧
        (∀ z ∈ closedBall 0 R, -2*M ≤ Real.log ‖g z‖) := by
  obtain ⟨S, hS, hboundary⟩ := LevinGrowth.exists_zero_free_sphere_between
    hf ⟨0, by simp [hf0]⟩ (show 2*R < 4*R by linarith)
  have hS0 : 0 < S := by linarith [hS.1]
  have hfS : AnalyticOnNhd ℂ f (closedBall 0 S) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).mono (subset_univ _)
  have hbd : ∀ z ∈ sphere 0 S, f z ≠ 0 := by
    intro z hz
    exact hboundary z (by simpa [mem_sphere, dist_zero_right] using hz)
  obtain ⟨g, _, hg, hgnz, heq, hgnorm, hg0⟩ :=
    LevinFactorization.exists_zero_free_factorization_with_center_bound
      hS0 hfS (by simp [hf0]) hbd
  have hup : ∀ z ∈ closedBall 0 S, Real.log ‖g z‖ ≤ M := by
    apply LevinLocalFactor.zero_free_factor_log_bound hS0 hg hgnz hgnorm
    intro z hz
    apply hbound z
    have hz' : ‖z‖ = S := by simpa [mem_sphere, dist_zero_right] using hz
    rw [mem_closedBall_zero_iff, hz']; linarith [hS.2]
  have hg0pos : 0 ≤ Real.log ‖g 0‖ := by simpa [hf0] using hg0
  have hg0le : Real.log ‖g 0‖ ≤ M := hup 0 (mem_closedBall_self hS0.le)
  refine ⟨S, hS.1, hS.2, hfS, g, hgnz, heq,
    zeroCount_local_bound hf hR hM hf0 hS.2.le hbound hfS, ?_⟩
  intro z hz
  have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hzS : z ∈ ball 0 S := mem_ball_zero_iff.mpr (by linarith [hS.1])
  have hlo := CRGLevinAnalytic.log_norm_lower_bound hg hgnz hzS
    (fun z hz => hup z (sphere_subset_closedBall hz))
  simp only [sub_zero] at hlo
  have hratio : (S+‖z‖)/(S-‖z‖) ≤ 3 := by
    apply (div_le_iff₀ (by linarith [hS.1])).mpr
    linarith [hS.1]
  have hmul := mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr hg0le)
  linarith

/-- The loss in the local minimum-modulus estimate. -/
def loss (η : ℝ) : ℝ := 2 + Real.log (8 * Real.exp 1 / η) / Real.log 2

theorem loss_pos {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : 0 < loss η := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have harg : 1 ≤ 8 * Real.exp 1 / η := (le_div_iff₀ hη).mpr (by linarith)
  have hlog := Real.log_nonneg harg
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold loss
  positivity

/-- The analytic implication from a finite zero-product lower bound. The next
covering theorem will supply that bound outside its concrete finite disks. -/
theorem log_norm_lower_of_zero_product {f g : ℂ → ℂ} {R S M η : ℝ}
    (hR : 0 < R) (hS : 2*R < S) (hS4 : S < 4*R)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hfS : AnalyticOnNhd ℂ f (closedBall 0 S))
    (hgnz : ∀ z ∈ closedBall 0 S, g z ≠ 0)
    (heq : ∀ z ∈ closedBall 0 S,
      f z = LevinFactorization.finiteBlaschke f S z * g z)
    (hcount : LevinFiniteProduct.zeroCount hfS ≤ M / Real.log 2)
    (hglow : ∀ z ∈ closedBall 0 R, -2*M ≤ Real.log ‖g z‖)
    {z : ℂ} (hz : z ∈ closedBall 0 R)
    (hprod : (η*R / Real.exp 1)^Fintype.card (ZeroIndex hfS) ≤
      ∏ i : ZeroIndex hfS, ‖z-i.1.val‖) :
    f z ≠ 0 ∧ -(loss η * M) ≤ Real.log ‖f z‖ := by
  classical
  have hS0 : 0 < S := by linarith
  have hzS : z ∈ closedBall 0 S :=
    closedBall_subset_closedBall (by linarith) hz
  let N := Fintype.card (ZeroIndex hfS)
  let B := η / (8*Real.exp 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hB1 : B ≤ 1 := by
    dsimp [B]
    apply (div_le_iff₀ (by positivity)).mpr
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have hbase : B ≤ (η*R/Real.exp 1)/(2*S) := by
    dsimp [B]
    apply (le_div_iff₀ (by positivity)).mpr
    apply (le_div_iff₀ (Real.exp_pos 1)).mpr
    field_simp
    nlinarith
  have hp : B^N ≤ ‖LevinFactorization.finiteBlaschke f S z‖ := by
    calc
      B^N ≤ ((η*R/Real.exp 1)/(2*S))^N := pow_le_pow_left₀ hB.le hbase N
      _ = (η*R/Real.exp 1)^N / (2*S)^N := div_pow _ _ _
      _ ≤ (∏ i : ZeroIndex hfS, ‖z-i.1.val‖)/(2*S)^N :=
        div_le_div_of_nonneg_right hprod (by positivity)
      _ ≤ _ := finiteBlaschke_product_lower hfS hS0 hzS
  have hp0 : 0 < ‖LevinFactorization.finiteBlaschke f S z‖ :=
    (pow_pos hB N).trans_le hp
  have hfnz : f z ≠ 0 := by rw [heq z hzS]; exact mul_ne_zero (norm_pos_iff.mp hp0) (hgnz z hzS)
  refine ⟨hfnz, ?_⟩
  have hlp := Real.log_le_log (pow_pos hB N) hp
  rw [Real.log_pow] at hlp
  have hlB : Real.log B = -Real.log (8*Real.exp 1/η) := by
    rw [show B = (8*Real.exp 1/η)⁻¹ by dsimp [B]; field_simp, Real.log_inv]
  have hNc : (N : ℝ) ≤ M/Real.log 2 := by
    dsimp [N]; rw [zeroIndex_card]; exact hcount
  have hlogB : Real.log B ≤ 0 := Real.log_nonpos hB.le hB1
  have hNlog := mul_le_mul_of_nonpos_right hNc hlogB
  have hlogf : Real.log ‖f z‖ =
      Real.log ‖LevinFactorization.finiteBlaschke f S z‖ + Real.log ‖g z‖ := by
    rw [heq z hzS, norm_mul, Real.log_mul hp0.ne' (norm_ne_zero_iff.mpr (hgnz z hzS))]
  rw [hlogf]
  have hglo := hglow z hz
  rw [hlB] at hNlog hlp
  unfold loss
  calc
    _ = M / Real.log 2 * -Real.log (8*Real.exp 1/η) + (-2*M) := by ring
    _ ≤ _ := add_le_add (hNlog.trans hlp) hglo

/-- A fully constructed local minimum-modulus estimate for an entire function
normalized at a nonzero center. Repeated zeros enter the Cartan point cloud with
their exact analytic multiplicities. -/
theorem exists_disks_local_lower {f : ℂ → ℂ} {R M η : ℝ}
    (hf : Differentiable ℂ f) (hR : 0 < R) (hM : 0 ≤ M)
    (hf0 : f 0 = 1)
    (hbound : ∀ z ∈ closedBall 0 (8*R), ‖f z‖ ≤ Real.exp M)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (r : Fin m → ℝ),
      (∀ j, 0 < r j) ∧ (∑ j, r j) ≤ 5*η*R ∧
      ∀ z ∈ closedBall 0 R, (∀ j, z ∉ ball (c j) (r j)) →
        f z ≠ 0 ∧ -(loss η * M) ≤ Real.log ‖f z‖ := by
  classical
  obtain ⟨S, hS, hS4, hfS, g, hgnz, heq, hcount, hglow⟩ :=
    exists_local_decomposition hf hR hM hf0 hbound
  obtain ⟨m, c, r, hr, hsum, hcartan⟩ :=
    LevinCartan.exists_disks_product_bound
      (fun i : ZeroIndex hfS => i.1.val) (show 0 < η*R by positivity)
  refine ⟨m, c, r, hr, by nlinarith [hsum], ?_⟩
  intro z hz hzout
  exact log_norm_lower_of_zero_product hR hS hS4 hη hη1
    hfS hgnz heq hcount hglow hz (hcartan z hzout).2

#print axioms zeroIndex_prod
#print axioms zeroIndex_card
#print axioms norm_finiteBlaschke_eq_prod
#print axioms inverse_canonical_lower
#print axioms finiteBlaschke_product_lower
#print axioms zeroCount_local_bound
#print axioms exists_local_decomposition
#print axioms loss_pos
#print axioms log_norm_lower_of_zero_product
#print axioms exists_disks_local_lower
end LevinMinimumModulus
