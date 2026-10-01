import CRGPhragmenRay

/-! Polynomial ray bounds are propagated using a denominator whose zero lies
outside the narrow sector; this avoids any pole at the origin. -/
noncomputable section
open Set Filter Complex Asymptotics
open scoped Topology BigOperators
namespace CRGPhragmenPolynomial

def denominator (c : ℝ) (w : ℂ) : ℂ :=
  1 + Complex.exp (w - (c : ℂ) * Complex.I)

theorem denominator_re (c : ℝ) (w : ℂ) :
    (denominator c w).re = 1 + Real.exp w.re * Real.cos (w.im - c) := by
  simp [denominator, Complex.exp_re]

theorem denominator_norm_upper (c : ℝ) (w : ℂ) :
    ‖denominator c w‖ ≤ 1 + Real.exp w.re := by
  simpa [denominator, Complex.norm_exp] using
    norm_add_le (1 : ℂ) (Complex.exp (w - (c : ℂ) * Complex.I))

/-- A polynomial bound with one exponent on two bounding rays propagates
across the whole intervening strip. -/
theorem strip_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a b c κ A B d : ℝ} {N : ℕ} (hab : a < b)
    (hκ : κ < Real.pi / (b - a)) (hA : 0 ≤ A) (hd : 0 < d) (hd1 : d ≤ 1)
    (hglobal : ∀ w : ℂ,
      ‖f (Complex.exp w)‖ ≤ A * Real.exp (B * Real.exp (κ * |w.re|)))
    (hboundary : ∀ w : ℂ, w.im = a ∨ w.im = b →
      ‖f (Complex.exp w)‖ ≤ A * (1 + Real.exp w.re) ^ N)
    (hcos : ∀ y ∈ Icc a b, 0 ≤ Real.cos (y - c))
    (hcosbd : ∀ y : ℝ, y = a ∨ y = b → d ≤ Real.cos (y - c))
    (w : ℂ) (hwa : a ≤ w.im) (hwb : w.im ≤ b) :
    ‖f (Complex.exp w)‖ ≤ (A / d ^ N) * (1 + Real.exp w.re) ^ N := by
  let U : Set ℂ := Complex.im ⁻¹' Ioo a b
  have hcl : closure U = Complex.im ⁻¹' Icc a b := by
    exact closure_preimage_im (Ioo a b) ▸ by rw [closure_Ioo hab.ne]
  have hnorm : ∀ v : ℂ, v.im ∈ Icc a b → 1 ≤ ‖denominator c v‖ := by
    intro v hv
    have he : 1 ≤ (denominator c v).re := by
      rw [denominator_re]
      exact le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (hcos _ hv))
    exact he.trans (Complex.re_le_norm _)
  have hnz : ∀ v : ℂ, v.im ∈ Icc a b → denominator c v ≠ 0 := by
    intro v hv hz
    have := hnorm v hv
    norm_num [hz] at this
  let g : ℂ → ℂ := fun v => (denominator c v ^ N)⁻¹ * f (Complex.exp v)
  have hdiffD : Differentiable ℂ (fun v => denominator c v ^ N) := by
    unfold denominator
    fun_prop
  have hg : DiffContOnCl ℂ g U := by
    exact (hdiffD.diffContOnCl.inv (fun v hv => pow_ne_zero _ (hnz v (by change v ∈ Complex.im ⁻¹' Icc a b; rwa [← hcl])))).smul
      ((hf.comp Complex.differentiable_exp).diffContOnCl)
  have hnormg : ∀ v, ‖g v‖ = ‖f (Complex.exp v)‖ / ‖denominator c v‖ ^ N := by
    intro v
    simp [g, norm_inv, norm_pow, div_eq_inv_mul]
  have hboundg : ∀ v : ℂ, v.im ∈ Ioo a b →
      ‖g v‖ ≤ A * Real.exp (B * Real.exp (κ * |v.re|)) := by
    intro v hv
    rw [hnormg]
    exact (div_le_self (norm_nonneg _) (one_le_pow₀ (hnorm v ⟨hv.1.le, hv.2.le⟩))).trans (hglobal v)
  have hbd : ∀ v : ℂ, v.im = a ∨ v.im = b → ‖g v‖ ≤ A / d ^ N := by
    intro v hv
    have hvI : v.im ∈ Icc a b := by
      rcases hv with hv | hv
      · rw [hv]; exact ⟨le_rfl, hab.le⟩
      · rw [hv]; exact ⟨hab.le, le_rfl⟩
    have hden : d * (1 + Real.exp v.re) ≤ ‖denominator c v‖ := by
      apply le_trans _ (Complex.re_le_norm _)
      rw [denominator_re]
      have hc := mul_le_mul_of_nonneg_left (hcosbd v.im hv) (Real.exp_pos v.re).le
      nlinarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ d * (1 + Real.exp v.re)) hden N
    rw [mul_pow] at hp
    rw [hnormg]
    apply (div_le_div_iff₀ (pow_pos (norm_pos_iff.mpr (hnz v hvI)) _) (pow_pos hd _)).mpr
    have hm := mul_le_mul_of_nonneg_left hp hA
    have hb' := mul_le_mul_of_nonneg_right (hboundary v hv) (pow_nonneg hd.le N)
    nlinarith
  have hPL : ‖g w‖ ≤ A / d ^ N := by
    apply PhragmenLindelof.horizontal_strip hg ⟨κ, hκ, B, ?_⟩
      (fun v hv => hbd v (Or.inl hv)) (fun v hv => hbd v (Or.inr hv)) hwa hwb
    apply Asymptotics.IsBigO.of_bound A
    exact eventually_inf_principal.mpr (Eventually.of_forall fun v hv => by simpa using hboundg v hv)
  rw [hnormg] at hPL
  have hrecover := (div_le_iff₀ (pow_pos (norm_pos_iff.mpr (hnz w ⟨hwa, hwb⟩)) N)).mp hPL
  exact hrecover.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (denominator_norm_upper c w) N) (by positivity))

#print axioms denominator_re
#print axioms denominator_norm_upper
#print axioms strip_bound
end CRGPhragmenPolynomial
