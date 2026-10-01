import GundersenGrowth
import LevinOrigin

/-! Removing the origin zero and normalizing the center without changing upper
order. These operations are proved for the actual entire functions. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GundersenOrigin

theorem upperOrder_remove_monomial {f F : ℂ → ℂ} {m : ℕ} {ρ : ℝ}
    (h : CRGOrder.UpperOrder f ρ) (heq : ∀ z, f z = z^m * F z) :
    CRGOrder.UpperOrder F ρ := by
  intro δ hδ
  obtain ⟨R, hR⟩ := h δ hδ
  refine ⟨max R 1, fun z hz => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
  have hn : ‖F z‖ ≤ ‖f z‖ := by
    rw [heq, norm_mul, norm_pow]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hz1)
  exact hn.trans (hR z ((le_max_left _ _).trans hz))

theorem upperOrder_const_mul {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : CRGOrder.UpperOrder f ρ) (c : ℂ) :
    CRGOrder.UpperOrder (fun z => c*f z) ρ := by
  intro δ hδ
  obtain ⟨R, hR⟩ := h (δ/2) (by positivity)
  obtain ⟨S, hS⟩ := eventually_atTop.mp (CRGOrder.eventually_mul_rpow_le
    (C := ‖c‖+1) (show ρ+δ/2 < ρ+δ by linarith))
  refine ⟨max R (max S 1), fun z hz => ?_⟩
  have hzR := (le_max_left R (max S 1)).trans hz
  have hzS := (le_max_left S 1).trans ((le_max_right R (max S 1)).trans hz)
  have hz1 : 1 ≤ ‖z‖ := (le_max_right S 1).trans ((le_max_right R (max S 1)).trans hz)
  have hpow : 1 ≤ ‖z‖^(ρ+δ/2) := Real.one_le_rpow hz1 (by linarith)
  have hce : ‖c‖ ≤ Real.exp ‖c‖ := by linarith [Real.add_one_le_exp ‖c‖]
  rw [norm_mul]
  calc
    ‖c‖*‖f z‖ ≤ Real.exp ‖c‖ * Real.exp (‖z‖^(ρ+δ/2)) :=
      mul_le_mul hce (hR z hzR) (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (‖c‖+‖z‖^(ρ+δ/2)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((‖c‖+1)*‖z‖^(ρ+δ/2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [norm_nonneg c]
    _ ≤ _ := Real.exp_le_exp.mpr (hS ‖z‖ hzS)

/-- Every nonzero entire function of upper order ρ factors as a monomial times
a nonzero constant times an entire function normalized to 1 at the origin,
with the SAME upper order. -/
theorem exists_normalized_factor {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hn : ∃ z, f z ≠ 0) (hρ : 0 ≤ ρ)
    (horder : CRGOrder.UpperOrder f ρ) :
    ∃ m : ℕ, ∃ a : ℂ, a ≠ 0 ∧ ∃ g : ℂ → ℂ,
      Differentiable ℂ g ∧ g 0 = 1 ∧ CRGOrder.UpperOrder g ρ ∧
      ∀ z, f z = z^m*(a*g z) := by
  obtain ⟨m, F, hF, hF0, heq⟩ := LevinOrigin.exists_entire_factor_at_origin hf hn
  let g : ℂ → ℂ := fun z => (F 0)⁻¹*F z
  refine ⟨m, F 0, hF0, g, hF.const_mul _, ?_, ?_, ?_⟩
  · simp [g, hF0]
  · exact upperOrder_const_mul hρ (upperOrder_remove_monomial horder heq) _
  · intro z
    rw [heq]
    simp [g, hF0]

/-- The removed monomial contributes exactly m/z to the logarithmic derivative. -/
theorem logDeriv_factorization {f g : ℂ → ℂ} {m : ℕ} {a z : ℂ}
    (hg : DifferentiableAt ℂ g z) (ha : a ≠ 0) (hz : z ≠ 0) (hgz : g z ≠ 0)
    (heq : ∀ w, f w = w^m*(a*g w)) :
    logDeriv f z = (m:ℂ)/z + logDeriv g z := by
  have hfun : f = fun w => w^m*(a*g w) := funext heq
  rw [hfun, logDeriv_mul (f := fun w : ℂ => w^m) (g := fun w => a*g w)
    z (pow_ne_zero m hz) (mul_ne_zero ha hgz)
    (by fun_prop) (hg.const_mul a), logDeriv_pow, logDeriv_const_mul z a ha]

/-- Reintroducing the removed origin zero preserves the sharp ray exponent.
The arbitrarily small error absorbs m/z and the factor two from the triangle
inequality. -/
theorem ray_logDeriv_restore {f g : ℂ → ℂ} {m : ℕ} {a : ℂ} {ρ δ θ : ℝ}
    (hg : Differentiable ℂ g) (ha : a ≠ 0) (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (heq : ∀ w, f w = w^m*(a*g w))
    (hbound : ∀ᶠ r : ℝ in atTop,
      g (CRGNormalFormGoal.ray θ r) ≠ 0 ∧
      ‖logDeriv g (CRGNormalFormGoal.ray θ r)‖ ≤ r^(ρ-1+δ/2)) :
    ∀ᶠ r : ℝ in atTop,
      f (CRGNormalFormGoal.ray θ r) ≠ 0 ∧
      ‖logDeriv f (CRGNormalFormGoal.ray θ r)‖ ≤ r^(ρ-1+δ) := by
  have hm := CRGOrder.eventually_mul_rpow_le (C := (m:ℝ))
    (show (-1:ℝ) < ρ-1+δ/2 by linarith)
  have ht := CRGOrder.eventually_mul_rpow_le (C := 2)
    (show ρ-1+δ/2 < ρ-1+δ by linarith)
  filter_upwards [hbound, hm, ht, eventually_gt_atTop (0:ℝ)] with r hr hmr htr hr0
  have hnorm : ‖CRGNormalFormGoal.ray θ r‖ = r := by
    simp [CRGNormalFormGoal.ray, Complex.norm_exp, Real.norm_of_nonneg hr0.le]
  have hz : CRGNormalFormGoal.ray θ r ≠ 0 := norm_pos_iff.mp (by rwa [hnorm])
  refine ⟨by rw [heq]; exact mul_ne_zero (pow_ne_zero m hz) (mul_ne_zero ha hr.1), ?_⟩
  rw [logDeriv_factorization (hg _) ha hz hr.1 heq]
  have hmono : ‖(m:ℂ)/CRGNormalFormGoal.ray θ r‖ ≤ r^(ρ-1+δ/2) := by
    rw [norm_div, Complex.norm_natCast, hnorm]
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hmr
  exact ((norm_add_le _ _).trans (add_le_add hmono hr.2)).trans (by linarith)

#print axioms ray_logDeriv_restore
#print axioms upperOrder_remove_monomial
#print axioms upperOrder_const_mul
#print axioms exists_normalized_factor
#print axioms logDeriv_factorization
end GundersenOrigin
