import LevinFactorization
import LevinCanonicalKernel

/-!
Finite-sum assembly using the actual analytic divisor and finite Blaschke
factorization. The dyadic exceptional-set construction and the final CRG
criterion are not asserted here.
-/
set_option autoImplicit false
noncomputable section
open Set Metric Real Complex MeasureTheory intervalIntegral MeromorphicOn
namespace LevinFiniteProduct

/-- Finite support of the analytic divisor. For a nontrivial analytic function
this is its interior zero set. For an identically zero function mathlib assigns
the zero divisor, so this definition returns the empty set instead. -/
def zeroSupport {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) : Finset ℂ :=
  hf.meromorphicOn.divisor_ball_support_finite.toFinset

lemma mem_zeroSupport {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) {a : ℂ} :
    a ∈ zeroSupport hf ↔ divisor f (ball 0 S) a ≠ 0 := by
  simp [zeroSupport, Function.mem_support]

/-- Real-valued analytic divisor coefficient. It is the usual zero multiplicity
when the analytic germ is not identically zero. -/
def multiplicity (f : ℂ → ℂ) (S : ℝ) (a : ℂ) : ℝ :=
  (divisor f (ball 0 S) a : ℝ)

lemma multiplicity_nonneg {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (a : ℂ) :
    0 ≤ multiplicity f S a := by
  exact Int.cast_nonneg ((hf.mono ball_subset_closedBall).divisor_nonneg a)

/-- Conversion from the actual divisor's finsum to its finite support. -/
theorem weighted_divisor_finsum {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (H : ℂ → ℝ) :
    (∑ᶠ a, multiplicity f S a * H a) = ∑ a ∈ zeroSupport hf, multiplicity f S a * H a := by
  apply finsum_eq_sum_of_support_subset
  intro a ha
  change a ∈ zeroSupport hf
  rw [mem_zeroSupport]
  intro hz
  have hzero : multiplicity f S a * H a = 0 := by simp [multiplicity, hz]
  exact ha hzero

/-- A radius avoiding the support of the actual divisor has no zeros on its circle. -/
theorem nonzero_of_radial_gap {f : ℂ → ℂ} {S r : ℝ} {z : ℂ}
    (hS : 0 < S) (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (hf0 : f 0 ≠ 0)
    (hz : z ∈ ball 0 S) (hzr : ‖z‖ = r)
    (hgap : ∀ a ∈ zeroSupport hf, r ≠ ‖a‖) : f z ≠ 0 := by
  intro heq
  have hfinite := LevinFactorization.finite_order_on_disk hS hf hf0
  have hzero := (hf.mono ball_subset_closedBall).meromorphicNFOn.zero_set_eq_divisor_support
    (fun a => hfinite ⟨a, ball_subset_closedBall a.property⟩)
  have hmem : z ∈ Function.support (divisor f (ball 0 S)) := by
    rw [← hzero]
    exact ⟨hz, heq⟩
  exact hgap z ((mem_zeroSupport hf).mpr hmem) hzr.symm

/-- The radial majorant is a sum over the actual zero multiplicities. -/
def radialPotential {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (R δ r : ℝ) : ℝ :=
  ∑ a ∈ zeroSupport hf, multiplicity f S a *
    (δ + CRGLevinLogKernel.radialKernel (2 * δ * R) (r - ‖a‖))

/-- The complete finite-product angular estimate, before normalization by r^ρ. -/
theorem log_norm_angular_bound {f g : ℂ → ℂ} {S R r δ : ℝ} {v w : ℂ}
    (hS : 0 < S) (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (hf0 : f 0 ≠ 0)
    (hboundary : ∀ z ∈ sphere 0 S, f z ≠ 0) (D : ECanonicalDecomp f g S)
    (hr : 0 < r) (hrS : r ≤ S / 2) (hrR : r ≤ 2 * R) (hδ : 0 ≤ δ)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : ‖v - w‖ ≤ δ)
    (hgap : ∀ a ∈ zeroSupport hf, r ≠ ‖a‖) :
    |Real.log ‖f ((r : ℂ) * v)‖ - Real.log ‖f ((r : ℂ) * w)‖| ≤
      |Real.log ‖g ((r : ℂ) * v)‖ - Real.log ‖g ((r : ℂ) * w)‖| + radialPotential hf R δ r := by
  have hv' : ‖(r : ℂ) * v‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hv]
  have hw' : ‖(r : ℂ) * w‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hw]
  have hvball : (r : ℂ) * v ∈ ball 0 S := by
    rw [mem_ball_zero_iff, hv']; linarith
  have hwball : (r : ℂ) * w ∈ ball 0 S := by
    rw [mem_ball_zero_iff, hw']; linarith
  have hvne := nonzero_of_radial_gap hS hf hf0 hvball hv' hgap
  have hwne := nonzero_of_radial_gap hS hf hf0 hwball hw' hgap
  have hdecv := LevinFactorization.log_norm_decomposition hS hf hboundary D
    (ball_subset_closedBall hvball) hvne
  have hdecw := LevinFactorization.log_norm_decomposition hS hf hboundary D
    (ball_subset_closedBall hwball) hwne
  change Real.log ‖f ((r : ℂ) * v)‖ = Real.log ‖g ((r : ℂ) * v)‖ -
    ∑ᶠ a, multiplicity f S a * Real.log ‖canonicalFactor S a ((r : ℂ) * v)‖ at hdecv
  change Real.log ‖f ((r : ℂ) * w)‖ = Real.log ‖g ((r : ℂ) * w)‖ -
    ∑ᶠ a, multiplicity f S a * Real.log ‖canonicalFactor S a ((r : ℂ) * w)‖ at hdecw
  rw [weighted_divisor_finsum hf] at hdecv hdecw
  let Z := zeroSupport hf
  let Lv := fun a => Real.log ‖canonicalFactor S a ((r : ℂ) * v)‖
  let Lw := fun a => Real.log ‖canonicalFactor S a ((r : ℂ) * w)‖
  have hsum : |(∑ a ∈ Z, multiplicity f S a * Lv a) -
      (∑ a ∈ Z, multiplicity f S a * Lw a)| ≤ radialPotential hf R δ r := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro a ha
    have has : ‖a‖ ≤ S := (mem_ball_zero_iff.mp
      ((divisor f (ball 0 S)).supportWithinDomain ((mem_zeroSupport hf).mp ha))).le
    have hk := CRGLevinCanonicalKernel.canonicalFactor_circle_uniform_bound hS hr hrS hrR
      has hδ hv hw hvw (hgap a ha)
    rw [← mul_sub, abs_mul, abs_of_nonneg (multiplicity_nonneg hf a)]
    exact mul_le_mul_of_nonneg_left hk (multiplicity_nonneg hf a)
  rw [hdecv, hdecw]
  calc
    _ = |(Real.log ‖g ((r : ℂ) * v)‖ - Real.log ‖g ((r : ℂ) * w)‖) -
        ((∑ a ∈ Z, multiplicity f S a * Lv a) - (∑ a ∈ Z, multiplicity f S a * Lw a))| := by
      congr 1
      dsimp [Z, Lv, Lw]
      ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add_right hsum _)

/-- Total mass of the analytic divisor. For a nontrivial analytic function this
is the number of interior zeros with multiplicities. The identically zero
function has zero divisor mass by the library convention. -/
def zeroCount {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) : ℝ :=
  ∑ a ∈ zeroSupport hf, multiplicity f S a

/-- The count is exactly the real cast of the integer divisor sum. -/
theorem zeroCount_eq_divisor_sum {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) :
    zeroCount hf = (∑ᶠ a, divisor f (ball 0 S) a : ℤ) := by
  have h := weighted_divisor_finsum hf (fun _ => 1)
  simp only [mul_one] at h
  rw [zeroCount, ← h]
  exact (map_finsum (Int.castRingHom ℝ) hf.meromorphicOn.divisor_ball_support_finite).symm

/-- Nonnegativity is inherited from the actual analytic zero multiplicities. -/
theorem radialPotential_nonneg {f : ℂ → ℂ} {S R δ r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (hR : 0 ≤ R) (hδ : 0 ≤ δ) :
    0 ≤ radialPotential hf R δ r := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (multiplicity_nonneg hf a)
    (add_nonneg hδ (CRGLevinLogKernel.radialKernel_nonneg (by positivity)))

/-- The entire finite radial majorant, including each logarithmic singularity,
is interval integrable. -/
theorem radialPotential_intervalIntegrable {f : ℂ → ℂ} {S R δ a b : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (hR : 0 < R) (hδ : 0 < δ) :
    IntervalIntegrable (radialPotential hf R δ) volume a b := by
  have hker (z : ℂ) : IntervalIntegrable
      (fun x => CRGLevinLogKernel.radialKernel (2 * δ * R) (x - ‖z‖)) volume a b := by
    have h := CRGLevinLogKernel.radialKernel_intervalIntegrable_all
      (a := a - ‖z‖) (b := b - ‖z‖) (h := 2 * δ * R) (by positivity)
    simpa only [sub_add_cancel] using h.comp_sub_right ‖z‖
  classical
  have hsum (Z : Finset ℂ) : IntervalIntegrable
      (fun r => ∑ z ∈ Z, multiplicity f S z *
        (δ + CRGLevinLogKernel.radialKernel (2 * δ * R) (r - ‖z‖))) volume a b := by
    induction Z using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (intervalIntegrable_const (c := (0 : ℝ)))
    | @insert z Z hz ih =>
      simpa only [Finset.sum_insert hz] using
        (((intervalIntegrable_const (c := δ)).add (hker z)).const_mul (multiplicity f S z)).add ih
  exact hsum (zeroSupport hf)

/-- The dyadic L¹ cost is linear in the analytic divisor mass, which is the
ordinary zero count for a nontrivial analytic function. No separation or regular
distribution of those zeros is assumed. -/
theorem integral_radialPotential_bound {f : ℂ → ℂ} {S R δ : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (hR : 0 < R)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hS : S ≤ 16 * R) :
    (∫ r in R..(2 * R), radialPotential hf R δ r) ≤
      zeroCount hf * (R * δ + 4 * R * δ * (2 - Real.log (δ / 8))) := by
  have hker (z : ℂ) : IntervalIntegrable
      (fun x => CRGLevinLogKernel.radialKernel (2 * δ * R) (x - ‖z‖)) volume R (2 * R) := by
    have h := CRGLevinLogKernel.radialKernel_intervalIntegrable_all
      (a := R - ‖z‖) (b := 2 * R - ‖z‖) (h := 2 * δ * R) (by positivity)
    simpa only [sub_add_cancel] using h.comp_sub_right ‖z‖
  simp only [radialPotential]
  rw [integral_finsetSum (fun z _ =>
    ((intervalIntegrable_const (c := δ)).add (hker z)).const_mul (multiplicity f S z))]
  rw [zeroCount, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z hz
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const (hker z), intervalIntegral.integral_const,
    smul_eq_mul]
  have hzs : ‖z‖ ≤ 16 * R :=
    ((mem_ball_zero_iff.mp ((divisor f (ball 0 S)).supportWithinDomain
      ((mem_zeroSupport hf).mp hz))).le).trans hS
  have ht := CRGLevinLogKernel.integral_radialKernel_shift_bound
    (δ := δ / 8) (L := 16 * R) (a := R) (b := 2 * R) (s := ‖z‖)
    (by positivity) (by linarith) (by positivity) (by linarith)
    (by linarith) (by nlinarith [norm_nonneg z])
  have heq : δ / 8 * (16 * R) = 2 * δ * R := by ring
  rw [heq] at ht
  have h : (∫ x in R..(2 * R), CRGLevinLogKernel.radialKernel (2 * δ * R) (x - ‖z‖)) ≤
      4 * R * δ * (2 - Real.log (δ / 8)) := by
    convert ht using 1
    ring
  apply mul_le_mul_of_nonneg_left _ (multiplicity_nonneg hf z)
  linarith

#print axioms mem_zeroSupport
#print axioms multiplicity_nonneg
#print axioms weighted_divisor_finsum
#print axioms nonzero_of_radial_gap
#print axioms log_norm_angular_bound
#print axioms zeroCount_eq_divisor_sum
#print axioms radialPotential_nonneg
#print axioms radialPotential_intervalIntegrable
#print axioms integral_radialPotential_bound
end LevinFiniteProduct
