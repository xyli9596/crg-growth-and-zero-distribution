import CRGFinitePhaseEndgame
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Group.Prod

/-! Angular coverage of ray information obtained on a single revolution.
No measurability of the ray predicate is needed: countably many Lebesgue-
preserving translations transport its actual almost-everywhere witnesses. -/
noncomputable section
open Set Filter MeasureTheory Polynomial
open scoped Topology
namespace CRGIndicatorPeriodicRays
open CRGNormalFormGoal CRGOrderRay

/-- Pull an arbitrary a.e. predicate on one fundamental interval back to the
whole real line by taking its canonical angular representative. -/
theorem ae_toIocMod_of_ae_restrict {T a : ℝ} (hT : 0 < T) {Q : ℝ → Prop}
    (hQ : ∀ᵐ θ : ℝ ∂volume.restrict (Ioc a (a + T)), Q θ) :
    ∀ᵐ θ : ℝ, Q (toIocMod hT a θ) := by
  have hi : ∀ᵐ θ : ℝ, θ ∈ Ioc a (a + T) → Q θ := ae_imp_of_ae_restrict hQ
  have ht : ∀ k : ℤ, ∀ᵐ θ : ℝ,
      θ - k • T ∈ Ioc a (a + T) → Q (θ - k • T) := by
    intro k
    simpa only [sub_eq_add_neg] using
      ((measurePreserving_add_right volume (-(k • T))).quasiMeasurePreserving.tendsto_ae).eventually hi
  have hall : ∀ᵐ θ : ℝ, ∀ k : ℤ,
      θ - k • T ∈ Ioc a (a + T) → Q (θ - k • T) := ae_all_iff.mpr ht
  filter_upwards [hall] with θ hθ
  exact hθ (toIocDiv hT a θ) (sub_toIocDiv_zsmul_mem_Ioc hT a θ)

/-- A periodic proposition which holds a.e. on one revolution holds a.e.
globally. In particular no global angular coverage is an extra hypothesis. -/
theorem ae_of_periodic_of_ae_restrict {T a : ℝ} (hT : 0 < T) {Q : ℝ → Prop}
    (hperiod : Function.Periodic Q T)
    (hQ : ∀ᵐ θ : ℝ ∂volume.restrict (Ioc a (a + T)), Q θ) :
    ∀ᵐ θ : ℝ, Q θ := by
  filter_upwards [ae_toIocMod_of_ae_restrict hT hQ] with θ hθ
  simpa only [toIocMod, hperiod.sub_zsmul_eq] using hθ

/-- The actual complex point on a ray is periodic in its angular parameter. -/
theorem point_periodic (r : ℝ) :
    Function.Periodic (fun θ : ℝ => CRGPhragmenRay.point θ r) (2 * Real.pi) := by
  intro θ
  unfold CRGPhragmenRay.point
  apply congrArg (fun z : ℂ => (r : ℂ) * z)
  simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    Complex.exp_mul_I_periodic (θ : ℂ)

/-- Choosing the angular representative preserves every point on the ray. -/
theorem point_toIocMod (θ r : ℝ) :
    CRGPhragmenRay.point (toIocMod Real.two_pi_pos 0 θ) r =
      CRGPhragmenRay.point θ r := by
  exact (point_periodic r).sub_zsmul_eq (toIocDiv Real.two_pi_pos 0 θ)

/-- Transport genuine ray data from the representative angle. -/
theorem rayData_of_toIocMod {f : ℂ → ℂ} {θ d a : ℝ}
    (h : RayData f (toIocMod Real.two_pi_pos 0 θ) d a) : RayData f θ d a := by
  refine ⟨?_, h.degree_nonneg, ?_, ?_⟩
  · simpa only [point_toIocMod] using h.nonzero
  · intro hd
    simpa only [logValue, point_toIocMod] using h.zero hd
  · intro hd
    simpa only [logValue, point_toIocMod] using h.positive hd

/-- Convert comparisons on one revolution to ray data on that interval.
The exceptional leading directions are proved null rather than postulated. -/
theorem ae_restrict_rayData_of_phase_comparison {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (P : ι → Polynomial ℂ)
    (hP0 : ∀ i, (P i).coeff 0 = 0)
    (hphase : ∀ᵐ θ : ℝ ∂volume.restrict (Ioc 0 (2 * Real.pi)), ∃ i : ι,
      (∀ᶠ r : ℝ in atTop, f (ray θ r) ≠ 0) ∧
      ∃ C : ℝ, ∀ᶠ r : ℝ in atTop,
        |Real.log ‖f (ray θ r)‖ - (phaseOnRay (p i) (P i) θ ⟨0, hp i⟩ r).re| ≤ C * Real.log r) :
    ∀ᵐ θ : ℝ ∂volume.restrict (Ioc 0 (2 * Real.pi)), ∃ i : ι,
      RayData f θ (((P i).natDegree : ℚ) / (p i : ℚ) : ℚ)
        (CRGFinitePhaseEndgame.leading (p i) (P i) θ) := by
  have hlead := ae_restrict_of_ae (s := Ioc 0 (2 * Real.pi))
    (CRGFinitePhaseEndgame.ae_all_leading_ne_zero p hp P hP0)
  filter_upwards [hphase, hlead] with θ hθ hleadθ
  obtain ⟨i, hn, herror⟩ := hθ
  refine ⟨i, ?_⟩
  have hh := CRGOrderPhaseData.rayData_of_polynomial_phase (p i) (hp i) (P i) (hP0 i)
    θ ⟨0, hp i⟩ hn herror (by
      intro hPi
      simpa only [CRGFinitePhaseEndgame.leading, Fin.val_mk, Nat.cast_zero,
        mul_zero, add_zero] using hleadθ i hPi)
  simpa only [CRGFinitePhaseEndgame.leading, Rat.cast_div, Rat.cast_natCast,
    Fin.val_mk, Nat.cast_zero, mul_zero, add_zero] using hh

/-- The finite rational degrees are unchanged after covering all angles.
Only their leading values are composed with the canonical representative. -/
theorem ae_rayData_of_Ioc_phase_comparison {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (P : ι → Polynomial ℂ)
    (hP0 : ∀ i, (P i).coeff 0 = 0)
    (hphase : ∀ᵐ θ : ℝ ∂volume.restrict (Ioc 0 (2 * Real.pi)), ∃ i : ι,
      (∀ᶠ r : ℝ in atTop, f (ray θ r) ≠ 0) ∧
      ∃ C : ℝ, ∀ᶠ r : ℝ in atTop,
        |Real.log ‖f (ray θ r)‖ - (phaseOnRay (p i) (P i) θ ⟨0, hp i⟩ r).re| ≤ C * Real.log r) :
    ∀ᵐ θ : ℝ, ∃ i : ι,
      RayData f θ (((P i).natDegree : ℚ) / (p i : ℚ) : ℚ)
        (CRGFinitePhaseEndgame.leading (p i) (P i) (toIocMod Real.two_pi_pos 0 θ)) := by
  have hi := ae_restrict_rayData_of_phase_comparison p hp P hP0 hphase
  have hg := ae_toIocMod_of_ae_restrict Real.two_pi_pos (a := 0) (by simpa using hi)
  filter_upwards [hg] with θ hθ
  obtain ⟨i, hi⟩ := hθ
  refine ⟨i, ?_⟩
  simpa only [Rat.cast_div, Rat.cast_natCast] using (rayData_of_toIocMod hi)

/-- The full existing order, type, and manuscript CRG endpoint requires
comparison only on (0,2π], which is the actual sector coverage of the paper. -/
theorem complete_of_Ioc_finite_phases {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z)
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (P : ι → Polynomial ℂ)
    (hP0 : ∀ i, (P i).coeff 0 = 0)
    (hphase : ∀ᵐ θ : ℝ ∂volume.restrict (Ioc 0 (2 * Real.pi)), ∃ i : ι,
      (∀ᶠ r : ℝ in atTop, f (ray θ r) ≠ 0) ∧
      ∃ C : ℝ, ∀ᶠ r : ℝ in atTop,
        |Real.log ‖f (ray θ r)‖ - (phaseOnRay (p i) (P i) θ ⟨0, hp i⟩ r).re| ≤ C * Real.log r) :
    ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ : ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ : ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ : ℝ) := by
  exact CRGOrderAE.complete_of_ae_rayData hf hfinite htrans
    (fun i => ((P i).natDegree : ℚ) / (p i : ℚ))
    (fun i θ => CRGFinitePhaseEndgame.leading (p i) (P i) (toIocMod Real.two_pi_pos 0 θ))
    (ae_rayData_of_Ioc_phase_comparison p hp P hP0 hphase)

#print axioms ae_toIocMod_of_ae_restrict
#print axioms ae_of_periodic_of_ae_restrict
#print axioms point_periodic
#print axioms point_toIocMod
#print axioms rayData_of_toIocMod
#print axioms ae_restrict_rayData_of_phase_comparison
#print axioms ae_rayData_of_Ioc_phase_comparison
#print axioms complete_of_Ioc_finite_phases
end CRGIndicatorPeriodicRays
