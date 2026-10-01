import LevinMinimumModulus
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Quantitative compatibility of the Cartan loss and the indicator modulus.
This is the parameter estimate needed before choosing any scale thresholds. -/
noncomputable section
open Filter Real
open scoped Topology
namespace LevinCartanCost

theorem tendsto_mul_log_sq :
    Tendsto (fun δ : ℝ => δ * (Real.log δ)^2) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 1/2) (by norm_num)
  have hh := h.mul h
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hp : δ ^ (1/2 : ℝ) * δ ^ (1/2 : ℝ) = δ := by
    rw [← Real.rpow_add hδ]
    norm_num
  calc
    _ = (δ ^ (1/2 : ℝ) * δ ^ (1/2 : ℝ)) * (Real.log δ)^2 := by ring
    _ = _ := by rw [hp]

theorem tendsto_mul_log :
    Tendsto (fun δ : ℝ => δ * Real.log δ) (𝓝[>] 0) (𝓝 0) := by
  simpa using (Real.continuous_mul_log.tendsto (0 : ℝ)).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)

/-- The logarithmic loss of the local minimum modulus remains negligible
after paying a polynomial-size grid's disk budget. -/
theorem loss_mul_modulus_tendsto {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    Tendsto (fun δ : ℝ => LevinMinimumModulus.loss (b*δ/C) *
      (δ + LevinAnnulus.modulus (8*δ))) (𝓝[>] 0) (𝓝 0) := by
  let A := 2 + (Real.log 8 + 1 - Real.log b + Real.log C) / Real.log 2
  have hδ : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hh := ((hδ.const_mul (25*A)).add
    (tendsto_mul_log.const_mul (-8*A - 25/Real.log 2))).add
    (tendsto_mul_log_sq.const_mul (8/Real.log 2))
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have hlog : Real.log (8*Real.exp 1/(b*δ/C)) =
      Real.log 8 + 1 - Real.log b - Real.log δ + Real.log C := by
    rw [Real.log_div (mul_ne_zero (by norm_num) he)
      (div_ne_zero (mul_ne_zero hb.ne' hδ0) hC.ne'),
      Real.log_mul (by norm_num) he, Real.log_exp,
      Real.log_div (mul_ne_zero hb.ne' hδ0) hC.ne',
      Real.log_mul hb.ne' hδ0]
    ring
  unfold LevinMinimumModulus.loss LevinAnnulus.modulus
  rw [hlog, show 8*δ/8 = δ by ring]
  dsimp [A]
  ring

def profileModulus (δ : ℝ) : ℝ := 16*δ + LevinAnnulus.modulus (128*δ)

theorem profileModulus_tendsto_zero :
    Tendsto profileModulus (𝓝[>] 0) (𝓝 0) := by
  have hδ : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h128 := hδ.const_mul 128
  simp only [mul_zero] at h128
  have hm := LevinAnnulus.modulus_tendsto_zero.comp h128
  change Tendsto (fun δ : ℝ => 16*δ + LevinAnnulus.modulus (128*δ)) (𝓝[>] 0) (𝓝 0)
  simpa only [mul_zero, add_zero, Function.comp_def] using (hδ.const_mul 16).add hm

theorem loss_mul_profileModulus_tendsto {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    Tendsto (fun δ : ℝ => LevinMinimumModulus.loss (b*δ/C) * profileModulus δ)
      (𝓝[>] 0) (𝓝 0) := by
  have h16 : Tendsto (fun δ : ℝ => 16*δ) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0)).const_mul 16
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      change 0 < 16*δ
      exact mul_pos (by norm_num) hδ
  have ht := (loss_mul_modulus_tendsto (b := b/16) (by positivity) hC).comp h16
  apply ht.congr'
  filter_upwards [] with δ
  simp only [Function.comp_apply]
  rw [show b/16*(16*δ)/C = b*δ/C by ring,
    show 8*(16*δ) = 128*δ by ring]
  rfl

/-- Choose the mesh scale first, then the radial error. This leaves room for
both the disk-radius budget and the desired asymptotic error. -/
theorem exists_parameters {L b ε : ℝ} (_hL : 0 < L) (hb : 0 < b) (hε : 0 < ε) :
    ∃ δ a η : ℝ, 0 < δ ∧ δ ≤ 1/128 ∧ 0 < a ∧ 0 < η ∧ η ≤ 1 ∧
      1000*η/δ ≤ b ∧
      L*profileModulus δ+a+LevinMinimumModulus.loss η*(L*profileModulus δ+2*a) ≤ ε := by
  have hcost := ((profileModulus_tendsto_zero.const_mul L).add
    ((loss_mul_profileModulus_tendsto hb (show (0 : ℝ) < 1000 by norm_num)).const_mul L))
  simp only [mul_zero, add_zero] at hcost
  have hevent : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      L*profileModulus δ+L*(LevinMinimumModulus.loss (b*δ/1000)*profileModulus δ) < ε/2 :=
    (tendsto_order.mp hcost).2 _ (by positivity)
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < min (1/128 : ℝ) (1000/b) :=
    (eventually_lt_nhds (show (0 : ℝ) < min (1/128 : ℝ) (1000/b) by positivity)).filter_mono
      nhdsWithin_le_nhds
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδpos, hδsmall, hcostδ⟩ :=
    (hpos.and (hsmall.and hevent)).exists
  have hδ1 : δ ≤ 1/128 := (lt_min_iff.mp hδsmall).1.le
  let η := b*δ/1000
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    have h := (lt_min_iff.mp hδsmall).2
    have hbδ := (lt_div_iff₀ hb).mp h
    dsimp [η]
    linarith
  have hJ := LevinMinimumModulus.loss_pos hη hη1
  let a := ε / (4*(1+2*LevinMinimumModulus.loss η))
  have ha : 0 < a := by dsimp [a]; positivity
  have haeq : (1+2*LevinMinimumModulus.loss η)*a = ε/4 := by
    dsimp [a]
    field_simp
  refine ⟨δ, a, η, hδpos, hδ1, ha, hη, hη1, ?_, ?_⟩
  · have heq : 1000*η/δ = b := by dsimp [η]; field_simp
    exact heq.le
  · change L*profileModulus δ+L*(LevinMinimumModulus.loss η*profileModulus δ) < ε/2 at hcostδ
    nlinarith

#print axioms tendsto_mul_log_sq
#print axioms tendsto_mul_log
#print axioms loss_mul_modulus_tendsto
#print axioms profileModulus_tendsto_zero
#print axioms loss_mul_profileModulus_tendsto
#print axioms exists_parameters
end LevinCartanCost
