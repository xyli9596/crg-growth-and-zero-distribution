import CRGPhragmenStrip

noncomputable section
open Set Filter Complex Metric
open scoped Topology BigOperators
namespace CRGPhragmenGrowth

/-- Bounds on all positive radii of one ray, in logarithmic radius coordinates. -/
def RayBound (f : ℂ → ℂ) (τ θ : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
    ‖f (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))‖ ≤
      A * Real.exp (C * Real.exp (τ * x))

theorem lift_bound_of_upperOrder {f : ℂ → ℂ} {ρ κ : ℝ}
    (hf : Continuous f) (h : CRGOrder.UpperOrder f ρ) (hκ : ρ < κ) (hκ0 : 0 ≤ κ) :
    ∃ A : ℝ, 0 < A ∧ ∀ w : ℂ,
      ‖f (Complex.exp w)‖ ≤ A * Real.exp (Real.exp (κ * |w.re|)) := by
  obtain ⟨R, hR⟩ := h (κ - ρ) (sub_pos.mpr hκ)
  have hR' : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (‖z‖ ^ κ) := by
    simpa only [show ρ + (κ - ρ) = κ by ring] using hR
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun w => ?_⟩
  have hexp : 1 ≤ Real.exp (Real.exp (κ * |w.re|)) :=
    Real.one_le_exp (Real.exp_pos _).le
  by_cases hw : R ≤ ‖Complex.exp w‖
  · apply (hR' _ hw).trans
    calc
      Real.exp (‖Complex.exp w‖ ^ κ) ≤ Real.exp (Real.exp (κ * |w.re|)) := by
        rw [Complex.norm_exp, ← Real.exp_mul]
        apply Real.exp_le_exp.mpr
        apply Real.exp_le_exp.mpr
        nlinarith [le_abs_self w.re]
      _ ≤ max M 1 * Real.exp (Real.exp (κ * |w.re|)) :=
        le_mul_of_one_le_left (Real.exp_pos _).le (le_max_right _ _)
  · have hm := hM (Complex.exp w) (by simpa [mem_closedBall_iff_norm] using (not_le.mp hw).le)
    exact hm.trans ((le_max_left _ _).trans (le_mul_of_one_le_right
      (le_trans zero_le_one (le_max_right _ _)) hexp))

/-- A sufficiently narrow pair of directions bounds an open interval around
any intermediate angle. Constants may depend on these two directions. -/
theorem between_rays {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {ρ τ κ a b : ℝ} (horder : CRGOrder.UpperOrder f ρ)
    (hρκ : ρ < κ) (hκ : 0 < κ) (hτ : 0 ≤ τ) (hτκ : τ ≤ κ)
    (hab : a < b) (hgap : κ * (b - a) < Real.pi)
    (ha : RayBound f τ a) (hb : RayBound f τ b) :
    ∃ A : ℝ, 0 < A ∧ ∃ K : ℝ, 0 < K ∧ ∀ w : ℂ,
      a ≤ w.im → w.im ≤ b →
      ‖f (Complex.exp w)‖ ≤ A * Real.exp (K * Real.exp (τ * w.re)) := by
  obtain ⟨A₀, hA₀, hg⟩ := lift_bound_of_upperOrder hf.continuous horder hρκ hκ.le
  obtain ⟨Aa, hAa, Ca, hCa, ha⟩ := ha
  obtain ⟨Ab, hAb, Cb, hCb, hb⟩ := hb
  let A := max A₀ (max Aa Ab)
  let C := max Ca Cb
  let c := (a + b) / 2
  have hcos : 0 < Real.cos (τ * ((b - a) / 2)) := by
    apply Real.cos_pos_of_mem_Ioo
    have hmul : τ * (b - a) ≤ κ * (b - a) :=
      mul_le_mul_of_nonneg_right hτκ (sub_pos.mpr hab).le
    constructor <;> nlinarith [Real.pi_pos, mul_nonneg hτ (sub_pos.mpr hab).le]
  let K := C / Real.cos (τ * ((b - a) / 2))
  have hC : 0 < C := hCa.trans_le (le_max_left _ _)
  have hK : 0 < K := div_pos hC hcos
  have hA : 0 < A := hA₀.trans_le (le_max_left _ _)
  refine ⟨A, hA, K, hK, fun w hwa hwb => ?_⟩
  apply CRGPhragmenStrip.angular_bound hf (a := a) (b := b) (c := c)
    (κ := κ) (B := 1) (C := C) ((lt_div_iff₀ (sub_pos.mpr hab)).mpr hgap)
    hτ hτκ hA.le hK.le _ _ _ w hwa hwb
  · intro v
    simpa only [one_mul] using (hg v).trans
      (mul_le_mul_of_nonneg_right (le_max_left A₀ (max Aa Ab)) (Real.exp_pos _).le)
  · intro v hv
    have hvdecomp : v = (v.re : ℂ) + (v.im : ℂ) * Complex.I := by
      exact (Complex.re_add_im v).symm
    rcases hv with hva | hvb
    · have he := ha v.re
      rw [← hva, ← hvdecomp] at he
      exact he.trans (mul_le_mul ((le_max_left Aa Ab).trans (le_max_right A₀ _))
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left Ca Cb)
          (Real.exp_pos _).le)) (Real.exp_pos _).le hA.le)
    · have he := hb v.re
      rw [← hvb, ← hvdecomp] at he
      exact he.trans (mul_le_mul ((le_max_right Aa Ab).trans (le_max_right A₀ _))
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right Ca Cb)
          (Real.exp_pos _).le)) (Real.exp_pos _).le hA.le)
  · intro y hy
    have heq : Real.cos (τ * (y - c)) = Real.cos (τ * ((b - a) / 2)) := by
      rcases hy with hy | hy
      · rw [hy]
        have : τ * (a - c) = -(τ * ((b - a) / 2)) := by dsimp [c]; ring
        rw [this, Real.cos_neg]
      · rw [hy]; congr 1; dsimp [c]; ring
    rw [heq]
    exact (div_mul_cancel₀ C hcos.ne').ge

/-- Density supplies arbitrarily narrow bounding rays on both sides. -/
theorem local_bound_of_dense {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {ρ τ κ : ℝ} (horder : CRGOrder.UpperOrder f ρ)
    (hρκ : ρ < κ) (hκ : 0 < κ) (hτ : 0 ≤ τ) (hτκ : τ ≤ κ)
    {D : Set ℝ} (hD : Dense D) (hbound : ∀ θ ∈ D, RayBound f τ θ) (θ : ℝ) :
    ∃ a b : ℝ, a < θ ∧ θ < b ∧ ∃ A : ℝ, 0 < A ∧ ∃ K : ℝ, 0 < K ∧
      ∀ w : ℂ, a ≤ w.im → w.im ≤ b →
      ‖f (Complex.exp w)‖ ≤ A * Real.exp (K * Real.exp (τ * w.re)) := by
  let δ := Real.pi / (4 * κ)
  have hδ : 0 < δ := div_pos Real.pi_pos (by positivity)
  obtain ⟨a, haD, haθ⟩ := hD.exists_between (show θ - δ < θ by linarith)
  obtain ⟨b, hbD, hbθ⟩ := hD.exists_between (show θ < θ + δ by linarith)
  refine ⟨a, b, haθ.2, hbθ.1, between_rays hf horder hρκ hκ hτ hτκ
    (haθ.2.trans hbθ.1) ?_ (hbound a haD) (hbound b hbD)⟩
  have hδeq : κ * δ = Real.pi / 4 := by dsimp [δ]; field_simp
  have hlen : b - a < 2 * δ := by linarith [haθ.1, hbθ.2]
  have hmul := mul_lt_mul_of_pos_left hlen hκ
  nlinarith [Real.pi_pos]

#print axioms lift_bound_of_upperOrder
#print axioms between_rays
#print axioms local_bound_of_dense
end CRGPhragmenGrowth
