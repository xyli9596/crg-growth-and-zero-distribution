import GundersenLogarithm
import Mathlib.Analysis.Calculus.MeanValue

/-! The sharp first logarithmic derivative estimate supplies the genuinely
two-sided bound for log modulus, including the negative direction. -/
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace GundersenTwoSided
open CRGNormalFormGoal

theorem log_norm_power_bound_of_curve {g g' : ℝ → ℂ} {R α : ℝ}
    (hR : 1 ≤ R) (hα : 0 < α)
    (hg : ∀ r : ℝ, R ≤ r → HasDerivAt g (g' r) r)
    (hnz : ∀ r : ℝ, R ≤ r → g r ≠ 0)
    (hbound : ∀ r : ℝ, R ≤ r → ‖g' r / g r‖ ≤ r^(α-1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, R ≤ r → |Real.log ‖g r‖| ≤ C*r^α := by
  let C := |Real.log ‖g R‖| + 1/α
  have hC : 0 < C := add_pos_of_nonneg_of_pos (abs_nonneg _) (by positivity)
  refine ⟨C, hC, fun r hr => ?_⟩
  let L := fun t => Real.log ‖g t‖
  let d := fun t => (g' t / g t).re
  let B := fun t => |L R| + t^α/α
  have hd (t : ℝ) (ht : R ≤ t) : HasDerivAt L (d t) t :=
    GundersenLogarithm.hasDerivAt_log_norm (hg t ht) (hnz t ht)
  have hBd (t : ℝ) (ht : R ≤ t) : HasDerivAt B (t^(α-1)) t := by
    have ht0 : 0 < t := by linarith
    have hh := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl ht0.ne')).div_const α).const_add |L R|
    have he : α*t^(α-1)/α = t^(α-1) := by field_simp
    simpa only [he] using hh
  have hfcont : ContinuousOn L (Icc R r) := fun t ht => (hd t ht.1).continuousAt.continuousWithinAt
  have hbcont : ContinuousOn B (Icc R r) := fun t ht => (hBd t ht.1).continuousAt.continuousWithinAt
  have hstart : ‖L R‖ ≤ B R := by
    dsimp [B]
    exact le_add_of_nonneg_right (by positivity)
  have hlog : ‖L r‖ ≤ B r := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    hfcont (fun t ht => (hd t ht.1).hasDerivWithinAt) hstart hbcont
    (fun t ht => (hBd t ht.1).hasDerivWithinAt)
    (fun t ht => (Complex.abs_re_le_norm (g' t / g t)).trans (hbound t ht.1))
    ⟨hr, le_rfl⟩
  have hp : 1 ≤ r^α := Real.one_le_rpow (hR.trans hr) hα.le
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (L R))
  rw [Real.norm_eq_abs] at hlog
  dsimp [C, B, L] at hlog hm ⊢
  simp only [div_eq_mul_inv, one_mul] at hlog ⊢
  nlinarith

/-- The actual ray chain rule includes dz/dr = exp(iθ), whose modulus is one. -/
theorem ray_log_norm_power_bound {f : ℂ → ℂ} {ρ δ θ : ℝ}
    (hf : Differentiable ℂ f) (hρδ : 0 < ρ+δ)
    (hnz : ∀ᶠ r : ℝ in atTop, f (ray θ r) ≠ 0)
    (hbound : ∀ᶠ r : ℝ in atTop, ‖deriv f (ray θ r) / f (ray θ r)‖ ≤ r^(ρ-1+δ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℝ in atTop, |Real.log ‖f (ray θ r)‖| ≤ C*r^(ρ+δ) := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hnz.and hbound)
  let R' := max R 1
  have hbig (r : ℝ) (hr : R' ≤ r) := hR r ((le_max_left _ _).trans hr)
  let u := Complex.exp ((θ : ℂ)*Complex.I)
  have hu : ‖u‖ = 1 := by simp [u, Complex.norm_exp]
  have hg (r : ℝ) (_hr : R' ≤ r) :
      HasDerivAt (fun t : ℝ => f (ray θ t)) (deriv f (ray θ r)*u) r := by
    have hh := ((hf (ray θ r)).hasDerivAt.comp (r : ℂ)
      ((hasDerivAt_id (r : ℂ)).mul_const u)).comp_ofReal
    simpa only [ray, one_mul, u, Function.comp_apply, id_eq] using hh
  obtain ⟨C, hC, hc⟩ := log_norm_power_bound_of_curve (g := fun r => f (ray θ r))
    (g' := fun r => deriv f (ray θ r)*u) (show 1 ≤ R' from le_max_right _ _)
    hρδ hg (fun r hr => (hbig r hr).1) (by
      intro r hr
      rw [mul_div_right_comm, norm_mul, hu, mul_one]
      convert (hbig r hr).2 using 1
      congr 1
      ring)
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop R'] with r hr
  exact hc r hr

#print axioms log_norm_power_bound_of_curve
#print axioms ray_log_norm_power_bound
end GundersenTwoSided
