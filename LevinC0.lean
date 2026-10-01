import LevinCartanCost
import LevinLocalProfile
import LevinFiniteCover
import LevinScaledBounds
import LevinDiskClip
import LevinDiskAssembly
import LevinScaling

/-! Radial regularity to the manuscript's actual C₀ disk regularity.
The shell covers below are constructed from the proved finite Cartan estimate,
quantitative indicator modulus, global upper envelope, and radial good points. -/
noncomputable section
open Set Metric Real Complex Filter
open scoped Topology
open LevinGrowth LevinIndicatorModulus
namespace LevinC0

/-- Actual finite exceptional disks on each sufficiently large rescaled
annulus. Both the target error and the radius budget are independent inputs. -/
theorem exists_scaled_shell_covers {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hreg : RadialRegular f ρ h) {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ (m : ℕ) (c : Fin m → ℂ) (r : Fin m → ℝ),
        (∀ j, 0 ≤ r j) ∧ (∑ j, r j) ≤ b ∧
        ∀ z : ℂ, ‖z‖ ∈ Icc (1 : ℝ) 2 →
          (∀ j, z ∉ ball (c j) (r j)) →
          f ((R : ℂ)*z) ≠ 0 ∧
          |Real.log ‖f ((R : ℂ)*z)‖ / R^ρ-homogeneousIndicator ρ h z| ≤ ε := by
  classical
  obtain ⟨L, hL, hmod⟩ := exists_homogeneous_modulus hf hρ htype hreg
  obtain ⟨δ, a, η, hδ, hδ1, ha, hη, hη1, hbudget, herror⟩ :=
    LevinCartanCost.exists_parameters hL hb hε
  obtain ⟨Γ, hcard, hΓ, hcover⟩ :=
    LevinGrid.exists_annular_cover hδ (show δ ≤ 1/4 by linarith)
  obtain ⟨R₀, hR₀, hbds⟩ := LevinScaledBounds.exists_scaled_bounds
    hf hρ htype hreg ha hδ (show δ ≤ 1/4 by linarith)
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  have hRpos : 0 < R := hR₀.trans_le hR
  obtain ⟨hupper, hgood⟩ := hbds R hR
  have hcenters : ∀ c : Γ, ∃ q : ℂ, ‖q-(c : ℂ)‖ ≤ δ ∧
      ‖q‖ ∈ Icc (1/4 : ℝ) 4 ∧ f ((R : ℂ)*q) ≠ 0 ∧
      |Real.log ‖f ((R : ℂ)*q)‖ / R^ρ-homogeneousIndicator ρ h q| ≤ a := by
    intro c
    have hc := hΓ c.val c.property
    exact hgood c.val ⟨by linarith [hc.1], by linarith [hc.2]⟩
  choose q hq hqann hqnonzero hqgood using hcenters
  let Ω := L * LevinCartanCost.profileModulus δ
  have hΩ : 0 ≤ Ω := by
    have hm := LevinAnnulus.modulus_nonneg (show 0 < 128*δ by positivity)
      (show 128*δ ≤ 1 by linarith)
    dsimp [Ω, LevinCartanCost.profileModulus]
    positivity
  have hqsmall (i : Γ) : ‖q i‖ ∈ Icc (1/2 : ℝ) 3 := by
    have hc := hΓ i.val i.property
    have hd := abs_norm_sub_norm_le (q i) i.val
    rw [abs_le] at hd
    have ht := hq i
    constructor <;> linarith [hc.1, hc.2, hd.1, hd.2]
  have hlocal (i : Γ) : ∃ (m : ℕ) (c : Fin m → ℂ) (r : Fin m → ℝ),
      (∀ j, 0 ≤ r j) ∧ (∑ j, r j) ≤ 10*η*δ ∧
      ∀ z : ℂ, ‖z-q i‖ ≤ 2*δ → (∀ j, z ∉ ball (c j) (r j)) →
        f ((R : ℂ)*z) ≠ 0 ∧
        |Real.log ‖f ((R : ℂ)*z)‖ / R^ρ-homogeneousIndicator ρ h z| ≤ ε := by
    have hF : Differentiable ℂ (fun z : ℂ => f ((R : ℂ)*z)) :=
      hf.comp (by fun_prop)
    obtain ⟨m, c, r, hr, hsum, hg⟩ :=
      LevinLocalProfile.exists_local_disks hF (Real.rpow_pos_of_pos hRpos ρ) ha.le hΩ
        hδ hδ1 hη hη1
        (fun u v hu hv huv => by
          have hm := hmod (16*δ) (by positivity) (by linarith) u v hu hv huv
          have he : 8*(16*δ) = 128*δ := by ring
          simpa only [he, Ω, LevinCartanCost.profileModulus] using hm)
        hupper (hqsmall i) (hqnonzero i) (hqgood i)
    refine ⟨m, c, r, fun j => (hr j).le, hsum, fun z hz hzout => ?_⟩
    obtain ⟨hnz, hbound⟩ := hg z hz hzout
    exact ⟨hnz, hbound.trans herror⟩
  obtain ⟨m, c, r, hr, hsum, hgood⟩ :=
    LevinFiniteCover.combine_annular_local_disks hδ hη.le Γ hcard hcover q hq hlocal
  exact ⟨m, c, r, hr, hsum.trans hbudget, hgood⟩

/-- The full radial-to-C₀ implication for an entire function of positive order
and finite nonzero type. Every shell's disks and their analytic estimates are
provided by the preceding construction, rather than assumed as a certificate. -/
theorem diskRegular_of_radialRegular {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ) (htype : FinitePositiveType f ρ)
    (hreg : RadialRegular f ρ h) : DiskRegular f ρ h := by
  apply LevinDiskAssembly.diskRegular_of_finite_shell_covers f ρ h hreg.1
    (c := 1/2) (by norm_num)
  intro ε hε b hb
  let B := min b (1/2 : ℝ)
  have hB : 0 < B := lt_min hb (by norm_num)
  obtain ⟨R₀, hR₀, hlocal⟩ := exists_scaled_shell_covers hf hρ htype hreg hε hB
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  have hRpos : 0 < R := hR₀.trans_le hR
  obtain ⟨m, c, r, hr, hsum, hscaled⟩ := hlocal R hR
  obtain ⟨r', hr', hsum', hcenter, hclip⟩ :=
    LevinDiskClip.exists_clipped_family 1 c r hr (by
      have hBhalf : B ≤ 1/2 := min_le_right _ _
      linarith)
  refine ⟨m, fun j => (R : ℂ)*c j, fun j => R*r' j,
    fun j => mul_nonneg hRpos.le (hr' j), ?_, ?_, ?_⟩
  · intro j hj
    change R*r' j ≠ 0 at hj
    have hne : r' j ≠ 0 := (mul_ne_zero_iff.mp hj).2
    have hc := hcenter j hne
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
    nlinarith
  · rw [LevinScaling.sum_scaled_radii]
    have hBb : B ≤ b := min_le_left _ _
    nlinarith
  · apply LevinScaling.shell_estimate_of_scaled_shell c r' hRpos hρ hε.le
    intro z hz hzout
    exact hscaled z hz ((hclip z (by simpa using hz)).mp hzout)

/-- The exact original constant-order Levin goal, including the actual C₀ disk
definition and the unrestricted extended-real indicator, now has a proof. -/
theorem constantOrderLevin : ConstantOrderLevinGoal := by
  intro f ρ hf hρ htype hdense
  obtain ⟨h, hradial, hindicator⟩ :=
    LevinCriterion.radialRegular_and_indicator_of_dense_rays hf hρ htype hdense
  exact ⟨h, diskRegular_of_radialRegular hf hρ htype hradial, hindicator⟩

#print axioms exists_scaled_shell_covers
#print axioms diskRegular_of_radialRegular
#print axioms constantOrderLevin
end LevinC0
