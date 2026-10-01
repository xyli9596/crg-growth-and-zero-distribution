import LevinGeometry

/-!
# Clipping finite exceptional disks to an annulus

Disks missing the closed annulus are replaced by radius-zero disks, preserving
the original index type. On the annulus the exceptional union is unchanged.
-/

noncomputable section
open Set Metric
open scoped BigOperators

namespace LevinDiskClip

def MeetsShell (R : ℝ) (c : ℂ) (r : ℝ) : Prop :=
  ∃ z : ℂ, ‖z‖ ∈ Icc R (2 * R) ∧ z ∈ ball c r

def clippedRadius (R : ℝ) (c : ℂ) (r : ℝ) : ℝ := by
  classical
  exact if MeetsShell R c r then r else 0

theorem clippedRadius_nonneg (R : ℝ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ clippedRadius R c r := by
  unfold clippedRadius
  split_ifs <;> simp_all

theorem clippedRadius_le (R : ℝ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    clippedRadius R c r ≤ r := by
  unfold clippedRadius
  split_ifs <;> simp_all

/-- A point in the shell belongs to exactly the same disks after clipping. -/
theorem mem_clipped_ball_iff {R : ℝ} {z : ℂ} (hz : ‖z‖ ∈ Icc R (2 * R))
    (c : ℂ) (r : ℝ) : z ∈ ball c (clippedRadius R c r) ↔ z ∈ ball c r := by
  classical
  by_cases hmeet : MeetsShell R c r
  · simp only [clippedRadius, if_pos hmeet]
  · have hnot : z ∉ ball c r := fun h => hmeet ⟨z, hz, h⟩
    simp [clippedRadius, hmeet, hnot]

/-- Any active disk of radius at most half the inner shell radius has its
center at or beyond half that shell radius. -/
theorem center_lower_of_clipped_ne_zero {R r : ℝ} {c : ℂ}
    (hsmall : r ≤ R / 2) (hactive : clippedRadius R c r ≠ 0) : R / 2 ≤ ‖c‖ := by
  classical
  have hmeet : MeetsShell R c r := by
    by_contra h
    exact hactive (by simp [clippedRadius, h])
  obtain ⟨z, hz, hball⟩ := hmeet
  have hdist : ‖z - c‖ < r := by simpa only [mem_ball, dist_eq_norm] using hball
  have htri := norm_sub_norm_le z c
  linarith [hz.1]

/-- Clipping decreases the actual finite sum of radii. -/
theorem sum_clippedRadius_le {ι : Type*} [Fintype ι]
    (R : ℝ) (c : ι → ℂ) (r : ι → ℝ) (hr : ∀ j, 0 ≤ r j) :
    (∑ j, clippedRadius R (c j) (r j)) ≤ ∑ j, r j := by
  exact Finset.sum_le_sum (fun j _ => clippedRadius_le R (c j) (hr j))

/-- Same-index clipping supplies the center constraint needed by C₀ assembly,
while preserving every shellwise pointwise estimate outside the disks. -/
theorem exists_clipped_family {ι : Type*} [Fintype ι]
    (R : ℝ) (c : ι → ℂ) (r : ι → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hsum : (∑ j, r j) ≤ R / 2) :
    ∃ r' : ι → ℝ, (∀ j, 0 ≤ r' j) ∧ (∑ j, r' j) ≤ ∑ j, r j ∧
      (∀ j, r' j ≠ 0 → R / 2 ≤ ‖c j‖) ∧
      ∀ z : ℂ, ‖z‖ ∈ Icc R (2 * R) →
        ((∀ j, z ∉ ball (c j) (r' j)) ↔ ∀ j, z ∉ ball (c j) (r j)) := by
  classical
  refine ⟨fun j => clippedRadius R (c j) (r j),
    fun j => clippedRadius_nonneg R (c j) (hr j), sum_clippedRadius_le R c r hr, ?_, ?_⟩
  · intro j hj
    have hjle : r j ≤ ∑ k, r k := Finset.single_le_sum (fun k _ => hr k) (Finset.mem_univ j)
    exact center_lower_of_clipped_ne_zero (hjle.trans hsum) hj
  · intro z hz
    exact forall_congr' (fun j => not_congr (mem_clipped_ball_iff hz (c j) (r j)))

#print axioms clippedRadius_nonneg
#print axioms clippedRadius_le
#print axioms mem_clipped_ball_iff
#print axioms center_lower_of_clipped_ne_zero
#print axioms sum_clippedRadius_le
#print axioms exists_clipped_family

end LevinDiskClip
