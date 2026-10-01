import LevinRadial
import LevinPoisson

/-! Auxiliary steps for identifying the unrestricted indicator.
These lemmas do not by themselves assert the full indicator identity. -/
noncomputable section
open Set Filter MeasureTheory Topology
open LevinGrowth LevinDensity LevinAssembly
namespace LevinIndicator

/-- Every sufficiently distant proportional interval contains a good radius.
Thus the exceptional set cannot hide a whole annulus of fixed relative width. -/
theorem eventually_exists_good_radius {E : Set ℝ} (hE : ZeroRadialDensity E)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ r : ℝ, R₁ ≤ r →
      ∃ s : ℝ, a * r < s ∧ s < b * r ∧ s ∉ E := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  obtain ⟨R₀, _, hbound⟩ := hE ((b - a) / (2 * b)) (by positivity)
  refine ⟨max 1 (R₀ / b), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans hr)
  have hlarge : R₀ ≤ b * r := by
    have h := (le_max_right 1 (R₀ / b)).trans hr
    exact (div_le_iff₀ hb).mp h |>.trans_eq (mul_comm _ _)
  by_contra hn
  have hsub : Ioo (a * r) (b * r) ⊆ E ∩ Icc 0 (b * r) := by
    intro s hs
    refine ⟨?_, (mul_nonneg ha hrpos.le).trans hs.1.le, hs.2.le⟩
    by_contra hsE
    exact hn ⟨s, hs.1, hs.2, hsE⟩
  have hm := (measure_mono hsub).trans (hbound (b * r) hlarge)
  rw [Real.volume_Ioo] at hm
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (show 0 ≤ (b - a) / (2 * b) * (b * r) by positivity)).mp hm
  have heq : (b - a) / (2 * b) * (b * r) = (b - a) * r / 2 := by
    field_simp
  rw [heq] at hreal
  nlinarith [mul_pos (sub_pos.mpr hab) hrpos]

#print axioms eventually_exists_good_radius
end LevinIndicator
