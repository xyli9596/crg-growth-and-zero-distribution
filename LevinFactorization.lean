import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Local removal of zeros by a finite canonical product

All multiplicities are the actual meromorphic divisor of the given analytic
function. The zero-free factor is constructed using mathlib's canonical
decomposition theorem, not supplied as an assumption.
-/

open Complex ComplexConjugate Filter Function MeromorphicOn Metric Set Topology

namespace LevinFactorization

/-- The finite Blaschke product with the actual interior zero multiplicities.
`canonicalFactor` in mathlib is the reciprocal canonical factor, hence the
negative divisor in this definition. -/
noncomputable def finiteBlaschke (f : ℂ → ℂ) (R : ℝ) : ℂ → ℂ :=
  ∏ᶠ w, (canonicalFactor R w) ^ (-divisor f (ball 0 R) w)

/-- Boundary nonvanishing kills the boundary divisor. -/
theorem divisor_sphere_eq_zero {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hnz : ∀ z ∈ sphere 0 R, f z ≠ 0) : divisor f (sphere 0 R) = 0 := by
  ext z
  by_cases hz : z ∈ sphere 0 R
  · rw [divisor_apply (hf.meromorphicOn.mono_set sphere_subset_closedBall) hz,
      (hf z (sphere_subset_closedBall hz)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
        (hnz z hz)]
    simp
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz

/-- Nonvanishing at the center excludes infinite analytic order everywhere on
 the connected closed disk. -/
theorem finite_order_on_disk {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0) :
    ∀ z : closedBall (0 : ℂ) R, meromorphicOrderAt f z ≠ ⊤ := by
  apply (hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
    (Metric.isConnected_closedBall hR.le)).mp
  refine ⟨⟨0, mem_closedBall_self hR.le⟩, ?_⟩
  rw [(hf 0 (mem_closedBall_self hR.le)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf0]
  exact WithTop.zero_ne_top

/-- The library's extended decomposition constructs an analytic zero-free factor;
boundary nonvanishing leaves only the interior finite Blaschke product. -/
theorem exists_zero_free_canonical_factor {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hboundary : ∀ z ∈ sphere 0 R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, ECanonicalDecomp f g R ∧
      AnalyticOnNhd ℂ g (closedBall 0 R) ∧ (∀ z ∈ closedBall 0 R, g z ≠ 0) ∧
      f =ᶠ[codiscreteWithin (closedBall 0 R)] (finiteBlaschke f R) * g := by
  obtain ⟨g, hg⟩ := hf.meromorphicOn.exists_ecanonicalDecomp (finite_order_on_disk hR hf hf0)
  refine ⟨g, hg, hg.analyticOnNhd, hg.ne_zero, ?_⟩
  simpa [divisor_sphere_eq_zero hf hboundary, finiteBlaschke, smul_eq_mul] using hg.eventuallyEq

/-- The denominator of an interior Blaschke factor does not vanish anywhere on
 the closed disk. -/
theorem canonical_numerator_ne_zero {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R) :
    (R : ℂ) ^ 2 - conj w * z ≠ 0 := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hw' : ‖w‖ < R := mem_ball_zero_iff.mp hw
  have hz' : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hnorm : ‖conj w * z‖ < ‖(R : ℂ) ^ 2‖ := by
    simp only [norm_mul, norm_conj, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hR]
    calc
      ‖w‖ * ‖z‖ ≤ ‖w‖ * R := mul_le_mul_of_nonneg_left hz' (norm_nonneg _)
      _ < R * R := mul_lt_mul_of_pos_right hw' hR
      _ = R ^ 2 := by ring
  exact sub_ne_zero.mpr fun heq => (ne_of_lt hnorm) (congrArg norm heq.symm)

/-- The reciprocal of a canonical factor is analytic even at its zero. -/
theorem analyticOnNhd_inverse_canonical {R : ℝ} {w : ℂ} (hw : w ∈ ball 0 R) :
    AnalyticOnNhd ℂ (fun z => (canonicalFactor R w z)⁻¹) (closedBall 0 R) := by
  intro z hz
  simp only [canonicalFactor, inv_div]
  exact (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    (canonical_numerator_ne_zero hw hz)

/-- The finite Blaschke factor of an analytic function is analytic on the disk,
including the original zeros. -/
theorem analyticOnNhd_finiteBlaschke {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    AnalyticOnNhd ℂ (finiteBlaschke f R) (closedBall 0 R) := by
  intro z hz
  apply analyticAt_finprod
  intro w
  by_cases hw : w ∈ ball 0 R
  · have hn : 0 ≤ divisor f (ball 0 R) w :=
      (hf.mono ball_subset_closedBall).divisor_nonneg w
    have heq : (canonicalFactor R w) ^ (-divisor f (ball 0 R) w) =
        (fun z => (canonicalFactor R w z)⁻¹) ^ (divisor f (ball 0 R) w).toNat := by
      ext x
      simp only [Pi.pow_apply, zpow_neg]
      rw [← zpow_natCast, Int.toNat_of_nonneg hn, inv_zpow]
    rw [heq]
    exact ((analyticOnNhd_inverse_canonical hw) z hz).pow _
  · simp only [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw, neg_zero, zpow_zero]
    exact analyticAt_const

/-- The finite Blaschke product has modulus one on the boundary. -/
theorem norm_finiteBlaschke_on_sphere {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {z : ℂ} (hz : z ∈ sphere 0 R) :
    ‖finiteBlaschke f R z‖ = 1 := by
  classical
  have hfin := hf.meromorphicOn.divisor_ball_support_finite
  rw [finiteBlaschke,
    finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) hfin,
    Finset.prod_apply, norm_prod]
  apply Finset.prod_eq_one
  intro w hw
  have hwball : w ∈ ball 0 R := (divisor f (ball 0 R)).supportWithinDomain
    (hfin.mem_toFinset.mp hw)
  simp only [Pi.pow_apply, norm_zpow, norm_canonicalFactor_eval_circle_eq_one hwball hz, one_zpow]

/-- Removal of the codiscrete qualification: for analytic functions the
canonical product equality holds at the original zeros as well. -/
theorem eqOn_of_canonical_factor {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (heq : f =ᶠ[codiscreteWithin (closedBall 0 R)] (finiteBlaschke f R) * g) :
    EqOn f ((finiteBlaschke f R) * g) (closedBall 0 R) := by
  intro z hz
  have hprod := ((analyticOnNhd_finiteBlaschke hf) z hz).mul (hg z hz)
  have hne := (hf z hz).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (U := closedBall 0 R) hprod.meromorphicAt hz (by
      rw [← closure_ball 0 hR.ne']
      exact isOpen_ball.perfect_closure.2) heq
  exact ((hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hprod.continuousAt).mp hne |>.eq_of_nhds

/-- A genuine pointwise finite Blaschke factorization on the closed disk,
with the boundary norm of the zero-free factor unchanged. -/
theorem exists_zero_free_factorization {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hboundary : ∀ z ∈ sphere 0 R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, ECanonicalDecomp f g R ∧
      AnalyticOnNhd ℂ g (closedBall 0 R) ∧ (∀ z ∈ closedBall 0 R, g z ≠ 0) ∧
      (∀ z ∈ closedBall 0 R, f z = finiteBlaschke f R z * g z) ∧
      ∀ z ∈ sphere 0 R, ‖g z‖ = ‖f z‖ := by
  obtain ⟨g, hD, hg, hgnz, heq⟩ := exists_zero_free_canonical_factor hR hf hf0 hboundary
  have hpoint := eqOn_of_canonical_factor hR hf hg heq
  refine ⟨g, hD, hg, hgnz, hpoint, ?_⟩
  intro z hz
  rw [hpoint (sphere_subset_closedBall hz), Pi.mul_apply, norm_mul,
    norm_finiteBlaschke_on_sphere hf hz, one_mul]

/-- At a nonzero center-to-zero displacement, the canonical norm is `R / |w|`. -/
theorem norm_canonicalFactor_at_zero {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ≠ 0) :
    ‖canonicalFactor R w 0‖ = R / ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  simp only [canonicalFactor_apply, mul_zero, sub_zero, zero_sub, norm_div,
    norm_pow, norm_mul, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos hR]
  field_simp

/-- Exact logarithmic decomposition at every point where the original function
is nonzero. This gives the finite sum to which radial kernel estimates apply. -/
theorem log_norm_decomposition {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hboundary : ∀ z ∈ sphere 0 R, f z ≠ 0) (D : ECanonicalDecomp f g R)
    {z : ℂ} (hz : z ∈ closedBall 0 R) (hfz : f z ≠ 0) :
    Real.log ‖f z‖ = Real.log ‖g z‖ -
      ∑ᶠ w, (divisor f (ball 0 R) w : ℝ) * Real.log ‖canonicalFactor R w z‖ := by
  have hord := (hf z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfz
  have heq := D.log_norm_eq hz hord hR
  rw [divisor_sphere_eq_zero hf hboundary] at heq
  simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero, zero_mul,
    finsum_zero, sub_zero, (hf z hz).meromorphicTrailingCoeffAt_of_ne_zero hfz] at heq
  linarith

/-- Removing the interior zeros increases the logarithmic modulus at the
nonzero center. This follows from the actual nonnegative zero multiplicities. -/
theorem log_norm_center_le {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hboundary : ∀ z ∈ sphere 0 R, f z ≠ 0) (D : ECanonicalDecomp f g R) :
    Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := by
  have hz : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have heq := log_norm_decomposition hR hf hboundary D hz hf0
  have hd0 : divisor f (ball 0 R) 0 = 0 := by
    rw [divisor_apply (hf.meromorphicOn.mono_set ball_subset_closedBall) (mem_ball_self hR),
      (hf 0 hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf0]
    simp
  have hsum : 0 ≤ ∑ᶠ w, (divisor f (ball 0 R) w : ℝ) *
      Real.log ‖canonicalFactor R w 0‖ := by
    apply finsum_nonneg
    intro w
    by_cases hwzero : divisor f (ball 0 R) w = 0
    · simp [hwzero]
    have hwball : w ∈ ball 0 R := (divisor f (ball 0 R)).supportWithinDomain hwzero
    have hwne : w ≠ 0 := by intro hw; subst w; exact hwzero hd0
    have hnorm : 1 ≤ ‖canonicalFactor R w 0‖ := by
      rw [norm_canonicalFactor_at_zero hR hwne]
      exact (one_le_div (norm_pos_iff.mpr hwne)).mpr (mem_ball_zero_iff.mp hwball).le
    exact mul_nonneg (Int.cast_nonneg ((hf.mono ball_subset_closedBall).divisor_nonneg w))
      (Real.log_nonneg hnorm)
  linarith

/-- Complete local finite Blaschke removal, including the center logarithmic
estimate required to control the zero-free factor. -/
theorem exists_zero_free_factorization_with_center_bound
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hboundary : ∀ z ∈ sphere 0 R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, ECanonicalDecomp f g R ∧
      AnalyticOnNhd ℂ g (closedBall 0 R) ∧ (∀ z ∈ closedBall 0 R, g z ≠ 0) ∧
      (∀ z ∈ closedBall 0 R, f z = finiteBlaschke f R z * g z) ∧
      (∀ z ∈ sphere 0 R, ‖g z‖ = ‖f z‖) ∧ Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := by
  obtain ⟨g, D, hg, hgnz, heq, hb⟩ := exists_zero_free_factorization hR hf hf0 hboundary
  exact ⟨g, D, hg, hgnz, heq, hb, log_norm_center_le hR hf hf0 hboundary D⟩

#print axioms norm_canonicalFactor_at_zero
#print axioms log_norm_decomposition
#print axioms log_norm_center_le
#print axioms exists_zero_free_factorization_with_center_bound
#print axioms norm_finiteBlaschke_on_sphere
#print axioms eqOn_of_canonical_factor
#print axioms exists_zero_free_factorization
#print axioms divisor_sphere_eq_zero
#print axioms finite_order_on_disk
#print axioms exists_zero_free_canonical_factor
#print axioms canonical_numerator_ne_zero
#print axioms analyticOnNhd_inverse_canonical
#print axioms analyticOnNhd_finiteBlaschke

end LevinFactorization
