import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic
import LevinDensity

/-! Geometry of the actual C₀ disk exceptional sets used by the manuscript.
The implication proved here goes from disk exceptions to radial exceptions.
The reverse implication for entire functions requires an analytic theorem and
is not inferred from this geometry. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LevinGeometry

structure DiskFamily where
  center : ℕ → ℂ
  radius : ℕ → ℝ
  radius_nonneg : ∀ n, 0 ≤ radius n

def disks (D : DiskFamily) : Set ℂ := ⋃ n, Metric.ball (D.center n) (D.radius n)

def radialShadow (D : DiskFamily) : Set ℝ :=
  ⋃ n, Ioo (‖D.center n‖ - D.radius n) (‖D.center n‖ + D.radius n)

def radiusMass (D : DiskFamily) (R : ℝ) : ℝ≥0∞ :=
  ∑' n, if ‖D.center n‖ ≤ R then ENNReal.ofReal (D.radius n) else 0

/-- The sum of radii of disks with centers of modulus at most R is o(R). -/
def IsC0 (D : DiskFamily) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 ≤ R₀ ∧
    ∀ R : ℝ, R₀ ≤ R → radiusMass D R ≤ ENNReal.ofReal (ε * R)

theorem measurableSet_radialShadow (D : DiskFamily) : MeasurableSet (radialShadow D) := by
  exact MeasurableSet.iUnion (fun _ => measurableSet_Ioo)

theorem norm_mem_radialShadow (D : DiskFamily) {z : ℂ} (hz : z ∈ disks D) :
    ‖z‖ ∈ radialShadow D := by
  obtain ⟨n, hn⟩ := mem_iUnion.mp hz
  apply mem_iUnion.mpr
  refine ⟨n, ?_⟩
  have hdist : ‖z - D.center n‖ < D.radius n := by simpa [dist_eq_norm] using hn
  have h := lt_of_le_of_lt (abs_norm_sub_norm_le z (D.center n)) hdist
  rw [abs_lt] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem radius_le_mass (D : DiskFamily) (n : ℕ) {R : ℝ} (hn : ‖D.center n‖ ≤ R) :
    ENNReal.ofReal (D.radius n) ≤ radiusMass D R := by
  have h := ENNReal.le_tsum (f := fun k =>
    if ‖D.center k‖ ≤ R then ENNReal.ofReal (D.radius k) else 0) n
  simpa only [if_pos hn, radiusMass] using h

theorem small_radius_at_large_center (D : DiskFamily) (hD : IsC0 D) :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ n, R₀ ≤ ‖D.center n‖ →
      D.radius n ≤ ‖D.center n‖ / 2 := by
  obtain ⟨R₀, hR₀, hmass⟩ := hD (1/2) (by norm_num)
  refine ⟨R₀, hR₀, fun n hn => ?_⟩
  have h := (radius_le_mass D n (le_refl _)).trans (hmass _ hn)
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  linarith

theorem radialShadow_volume_bound (D : DiskFamily) {R₀ R : ℝ}
    (hR₀ : 0 ≤ R₀) (hR : R₀ ≤ R)
    (hsmall : ∀ n, R₀ ≤ ‖D.center n‖ → D.radius n ≤ ‖D.center n‖ / 2) :
    volume (radialShadow D ∩ Icc 0 R) ≤ 2 * radiusMass D (2 * R) := by
  let S : ℕ → Set ℝ := fun n => if ‖D.center n‖ ≤ 2 * R then
    Ioo (‖D.center n‖ - D.radius n) (‖D.center n‖ + D.radius n) else ∅
  have hsub : radialShadow D ∩ Icc 0 R ⊆ ⋃ n, S n := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx.1
    have hc : ‖D.center n‖ ≤ 2 * R := by
      by_contra hc
      have hlarge : R₀ ≤ ‖D.center n‖ := by
        have := norm_nonneg (D.center n)
        linarith [not_le.mp hc]
      have hs := hsmall n hlarge
      have hl : ‖D.center n‖ - D.radius n < x := hn.1
      linarith [hx.2.2, not_le.mp hc]
    exact mem_iUnion.mpr ⟨n, by simpa only [S, if_pos hc] using hn⟩
  calc
    volume (radialShadow D ∩ Icc 0 R) ≤ volume (⋃ n, S n) := measure_mono hsub
    _ ≤ ∑' n, volume (S n) := measure_iUnion_le _
    _ = ∑' n, (2 : ℝ≥0∞) *
        (if ‖D.center n‖ ≤ 2 * R then ENNReal.ofReal (D.radius n) else 0) := by
      apply tsum_congr
      intro n
      dsimp [S]
      split_ifs
      · rw [Real.volume_Ioo]
        have heq : ‖D.center n‖ + D.radius n - (‖D.center n‖ - D.radius n) =
            2 * D.radius n := by ring
        rw [heq, ENNReal.ofReal_mul (by norm_num)]
        norm_num
      · simp
    _ = 2 * radiusMass D (2 * R) := by rw [ENNReal.tsum_mul_left]; rfl

/-- A C₀ union of disks has a measurable radial shadow of zero relative measure. -/
theorem radialShadow_zero_density (D : DiskFamily) (hD : IsC0 D) :
    LevinDensity.ZeroRadialDensity (radialShadow D) := by
  obtain ⟨A, hA, hsmall⟩ := small_radius_at_large_center D hD
  intro ε hε
  obtain ⟨B, hB, hmass⟩ := hD (ε / 4) (by positivity)
  refine ⟨max A B, le_max_of_le_left hA, fun R hR => ?_⟩
  have hAR : A ≤ R := (le_max_left _ _).trans hR
  have hBR : B ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 ≤ R := hA.trans hAR
  calc
    volume (radialShadow D ∩ Icc 0 R) ≤ 2 * radiusMass D (2 * R) :=
      radialShadow_volume_bound D hA hAR hsmall
    _ ≤ 2 * ENNReal.ofReal ((ε / 4) * (2 * R)) :=
      mul_le_mul' le_rfl (hmass (2 * R) (by linarith))
    _ = ENNReal.ofReal (ε * R) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

#print axioms measurableSet_radialShadow
#print axioms norm_mem_radialShadow
#print axioms radius_le_mass
#print axioms small_radius_at_large_center
#print axioms radialShadow_volume_bound
#print axioms radialShadow_zero_density

end LevinGeometry
