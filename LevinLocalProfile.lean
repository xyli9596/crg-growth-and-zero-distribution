import LevinMinimumTransfer

/-! A local two-sided profile estimate. The upper envelope and one good center
are inputs; the exceptional disks are constructed by the proved Cartan theorem. -/
noncomputable section
open Set Metric Real Complex
namespace LevinLocalProfile

theorem exists_local_disks {F : ℂ → ℂ} {H : ℂ → ℝ} {T a Ω δ η : ℝ}
    (hF : Differentiable ℂ F) (hT : 0 < T) (ha : 0 ≤ a) (hΩ : 0 ≤ Ω)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/128) (hη : 0 < η) (hη1 : η ≤ 1)
    (hmod : ∀ u v : ℂ, ‖u‖ ∈ Icc (1/4 : ℝ) 4 → ‖v‖ ∈ Icc (1/4 : ℝ) 4 →
      ‖u-v‖ ≤ 16*δ → |H u-H v| ≤ Ω)
    (hupper : ∀ w : ℂ, ‖w‖ ∈ Icc (1/4 : ℝ) 4 →
      ‖F w‖ ≤ Real.exp (T*(H w+a)))
    {q : ℂ} (hq : ‖q‖ ∈ Icc (1/2 : ℝ) 3) (hFq : F q ≠ 0)
    (hgood : |Real.log ‖F q‖ / T-H q| ≤ a) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (r : Fin m → ℝ),
      (∀ j, 0 < r j) ∧ (∑ j, r j) ≤ 10*η*δ ∧
      ∀ z : ℂ, ‖z-q‖ ≤ 2*δ → (∀ j, z ∉ ball (c j) (r j)) →
        F z ≠ 0 ∧ |Real.log ‖F z‖ / T-H z| ≤
          Ω+a+LevinMinimumModulus.loss η*(Ω+2*a) := by
  have hqann : ‖q‖ ∈ Icc (1/4 : ℝ) 4 := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hnear (z : ℂ) (hz : ‖z-q‖ ≤ 16*δ) : ‖z‖ ∈ Icc (1/4 : ℝ) 4 := by
    have hn := abs_norm_sub_norm_le z q
    rw [abs_le] at hn
    constructor <;> linarith [hq.1, hq.2, hn.1, hn.2]
  have hqlo : T*(H q-a) ≤ Real.log ‖F q‖ := by
    have h := (abs_le.mp hgood).1
    have h' : H q-a ≤ Real.log ‖F q‖ / T := by linarith
    have ht := (le_div_iff₀ hT).mp h'
    nlinarith
  have hbound : ∀ z ∈ closedBall q (8*(2*δ)),
      ‖F z‖ ≤ Real.exp (T*(Ω+2*a)+Real.log ‖F q‖) := by
    intro z hz
    have hzq : ‖z-q‖ ≤ 16*δ := by
      have := mem_closedBall_iff_norm.mp hz
      linarith
    have hzann := hnear z hzq
    have hdiff := (abs_le.mp (hmod z q hzann hqann hzq)).2
    apply (hupper z hzann).trans
    apply Real.exp_le_exp.mpr
    nlinarith
  obtain ⟨m, c, r, hr, hsum, hlo⟩ :=
    LevinMinimumTransfer.exists_disks_local_lower hF hFq (show 0 < 2*δ by positivity)
      (show 0 ≤ T*(Ω+2*a) by positivity) hbound hη hη1
  refine ⟨m, c, r, hr, by nlinarith [hsum], ?_⟩
  intro z hz hzout
  have hz16 : ‖z-q‖ ≤ 16*δ := by linarith
  have hzann := hnear z hz16
  obtain ⟨hFz, hlower⟩ := hlo z (mem_closedBall_iff_norm.mpr hz) hzout
  refine ⟨hFz, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hdiff := (abs_le.mp (hmod z q hzann hqann hz16)).2
    have hraw : T*(H z-(Ω+a+LevinMinimumModulus.loss η*(Ω+2*a))) ≤
        Real.log ‖F z‖ := by nlinarith
    have ht := (le_div_iff₀ hT).mpr (by simpa only [mul_comm] using hraw)
    linarith
  · have hlog := Real.log_le_log (norm_pos_iff.mpr hFz) (hupper z hzann)
    rw [Real.log_exp] at hlog
    have ht : Real.log ‖F z‖ / T ≤ H z+a :=
      (div_le_iff₀ hT).mpr (by nlinarith)
    have hpos := (LevinMinimumModulus.loss_pos hη hη1).le
    have hmul : 0 ≤ LevinMinimumModulus.loss η*(Ω+2*a) := by positivity
    linarith

#print axioms exists_local_disks
end LevinLocalProfile
