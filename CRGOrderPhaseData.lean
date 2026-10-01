import CRGOrderLevin
import CRGPhaseAsymptotics

/-! Conversion of the concrete polynomial-in-fractional-powers phase expansion
into the ray data consumed by the finite phase and Levin criteria. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace CRGOrderPhaseData
open CRGOrderRay CRGNormalFormGoal

/-- A logarithmic error vanishes after division by any positive power. -/
theorem logarithmic_error_limit (u v : ℝ → ℝ) {d : ℝ} (hd : 0 < d)
    (h : ∃ C : ℝ, ∀ᶠ r : ℝ in atTop, |u r - v r| ≤ C * Real.log r) :
    Tendsto (fun r : ℝ => (u r - v r) / r ^ d) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := h
  have hlog := (isLittleO_log_rpow_atTop hd).tendsto_div_nhds_zero
  have hub : ∀ᶠ r : ℝ in atTop,
      |(u r - v r) / r ^ d| ≤ C * (Real.log r / r ^ d) := by
    filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hr0 d), ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hr (Real.rpow_pos_of_pos hr0 d).le
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hub (by simpa using hlog.const_mul C)

/-- The actual fixed phase and its logarithmic scalar error give `RayData`.
The polynomial's zero constant term is used in the zero-degree branch. -/
theorem rayData_of_polynomial_phase {f : ℂ → ℂ} (p : ℕ) (hp : 0 < p)
    (P : Polynomial ℂ) (hP0 : P.coeff 0 = 0) (θ : ℝ) (ℓ : Fin p)
    (hn : ∀ᶠ r : ℝ in atTop, f (CRGPhragmenRay.point θ r) ≠ 0)
    (herror : ∃ C : ℝ, ∀ᶠ r : ℝ in atTop,
      |logValue f θ r - (phaseOnRay p P θ ℓ r).re| ≤ C * Real.log r)
    (hlead : P ≠ 0 → (P.leadingCoeff *
      (Complex.exp (((θ + 2 * Real.pi * (ℓ : ℝ)) / (p : ℝ) : ℝ) * Complex.I)) ^ P.natDegree).re ≠ 0) :
    RayData f θ ((P.natDegree : ℝ) / (p : ℝ))
      (P.leadingCoeff *
        (Complex.exp (((θ + 2 * Real.pi * (ℓ : ℝ)) / (p : ℝ) : ℝ) * Complex.I)) ^ P.natDegree).re := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  refine ⟨hn, by positivity, ?_, ?_⟩
  · intro hd0
    have hn0 : P.natDegree = 0 := by
      have hh : (P.natDegree : ℝ) = 0 := (div_eq_zero_iff).mp hd0 |>.resolve_right hpR.ne'
      exact_mod_cast hh
    have hP : P = 0 := by rw [Polynomial.eq_C_of_natDegree_eq_zero hn0, hP0, Polynomial.C_0]
    obtain ⟨C, hC⟩ := herror
    exact ⟨C, by simpa only [hP, phaseOnRay, Polynomial.eval_zero, Complex.zero_re, sub_zero] using hC⟩
  · intro hd
    have hP : P ≠ 0 := by intro hP; simp [hP] at hd
    refine ⟨hlead hP, ?_⟩
    have hpLim := CRGPhaseAsymptotics.phase_normalized_limit p hp P θ ℓ (hlead hP)
    have herrorLim := logarithmic_error_limit (logValue f θ) (fun r => (phaseOnRay p P θ ℓ r).re) hd herror
    have hh := herrorLim.add hpLim
    simpa only [zero_add, sub_div, sub_add_cancel] using hh

#print axioms logarithmic_error_limit
#print axioms rayData_of_polynomial_phase
end CRGOrderPhaseData
