import CRGPhragmenPolynomial

noncomputable section
open Set Filter Complex Metric
open scoped Topology BigOperators
namespace CRGPhragmenPolynomialGlobal

def RayBound (f : ℂ → ℂ) (θ : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ x : ℝ,
    ‖f (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))‖ ≤ A * (1 + Real.exp x) ^ N

theorem between_rays {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {ρ κ a b : ℝ} (horder : CRGOrder.UpperOrder f ρ)
    (hρκ : ρ < κ) (hκ : 1 ≤ κ) (hab : a < b) (hgap : κ * (b - a) < Real.pi)
    (ha : RayBound f a) (hb : RayBound f b) :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ w : ℂ,
      a ≤ w.im → w.im ≤ b → ‖f (Complex.exp w)‖ ≤ A * (1 + Real.exp w.re) ^ N := by
  obtain ⟨A₀, hA₀, hg⟩ := CRGPhragmenGrowth.lift_bound_of_upperOrder hf.continuous horder hρκ (by linarith)
  obtain ⟨Aa, hAa, Na, ha⟩ := ha
  obtain ⟨Ab, hAb, Nb, hb⟩ := hb
  let A := max A₀ (max Aa Ab)
  let N := max Na Nb
  let c := (a + b) / 2
  let d := Real.cos ((b - a) / 2)
  have hwidth : b - a < Real.pi := by
    have hh := mul_le_mul_of_nonneg_right hκ (sub_pos.mpr hab).le
    nlinarith
  have hd : 0 < d := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hd1 : d ≤ 1 := Real.cos_le_one _
  have hA : 0 < A := hA₀.trans_le (le_max_left _ _)
  refine ⟨A / d ^ N, div_pos hA (pow_pos hd _), N, fun w hwa hwb => ?_⟩
  apply CRGPhragmenPolynomial.strip_bound hf (a := a) (b := b) (c := c)
    (κ := κ) (B := 1) hab ((lt_div_iff₀ (sub_pos.mpr hab)).mpr hgap)
    hA.le hd hd1 _ _ _ _ w hwa hwb
  · intro v
    simpa only [one_mul] using (hg v).trans
      (mul_le_mul_of_nonneg_right (le_max_left A₀ (max Aa Ab)) (Real.exp_pos _).le)
  · intro v hv
    have hvdecomp : v = (v.re : ℂ) + (v.im : ℂ) * Complex.I := (Complex.re_add_im v).symm
    have hbase : 1 ≤ 1 + Real.exp v.re := by linarith [Real.exp_pos v.re]
    rcases hv with hva | hvb
    · have he := ha v.re
      rw [← hva, ← hvdecomp] at he
      exact he.trans (mul_le_mul ((le_max_left Aa Ab).trans (le_max_right A₀ _))
        (pow_le_pow_right₀ hbase (le_max_left Na Nb)) (by positivity) hA.le)
    · have he := hb v.re
      rw [← hvb, ← hvdecomp] at he
      exact he.trans (mul_le_mul ((le_max_right Aa Ab).trans (le_max_right A₀ _))
        (pow_le_pow_right₀ hbase (le_max_right Na Nb)) (by positivity) hA.le)
  · intro y hy
    apply (Real.cos_pos_of_mem_Ioo ?_).le
    dsimp [c]
    constructor <;> linarith [hy.1, hy.2]
  · intro y hy
    suffices Real.cos (y - c) = d by rw [this]
    rcases hy with hy | hy
    · rw [hy]
      have hh : a - c = -((b - a) / 2) := by dsimp [c]; ring
      rw [hh, Real.cos_neg]
    · rw [hy]; congr 1; dsimp [c]; ring

theorem local_bound_of_dense {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {ρ κ : ℝ} (horder : CRGOrder.UpperOrder f ρ)
    (hρκ : ρ < κ) (hκ : 1 ≤ κ)
    {D : Set ℝ} (hD : Dense D) (hbound : ∀ θ ∈ D, RayBound f θ) (θ : ℝ) :
    ∃ a b : ℝ, a < θ ∧ θ < b ∧ ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ,
      ∀ w : ℂ, a ≤ w.im → w.im ≤ b →
      ‖f (Complex.exp w)‖ ≤ A * (1 + Real.exp w.re) ^ N := by
  let δ := Real.pi / (4 * κ)
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hδ : 0 < δ := div_pos Real.pi_pos (by positivity)
  obtain ⟨a, haD, haθ⟩ := hD.exists_between (show θ - δ < θ by linarith)
  obtain ⟨b, hbD, hbθ⟩ := hD.exists_between (show θ < θ + δ by linarith)
  refine ⟨a, b, haθ.2, hbθ.1, between_rays hf horder hρκ hκ
    (haθ.2.trans hbθ.1) ?_ (hbound a haD) (hbound b hbD)⟩
  have hδeq : κ * δ = Real.pi / 4 := by dsimp [δ]; field_simp
  have hlen : b - a < 2 * δ := by linarith [haθ.1, hbθ.2]
  have hmul := mul_lt_mul_of_pos_left hlen hκ0
  nlinarith [Real.pi_pos]

/-- Dense polynomial ray estimates, with direction-dependent exponents, imply
one global polynomial estimate with a fixed integer exponent. -/
theorem global_bound_of_dense {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfinite : CRGOrder.FiniteOrder f) {D : Set ℝ} (hD : Dense D)
    (hbound : ∀ θ ∈ D, RayBound f θ) :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ z : ℂ, ‖f z‖ ≤ A * (1 + ‖z‖) ^ N := by
  classical
  obtain ⟨ρ, _, horder⟩ := hfinite
  let κ := max (ρ + 1) 1
  have hρκ : ρ < κ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hκ : 1 ≤ κ := le_max_right _ _
  have hlocal := local_bound_of_dense hf horder hρκ hκ hD hbound
  choose a b ha hb A hA N hlocal using hlocal
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover
    (fun θ : ℝ => Ioo (a θ) (b θ)) (fun _ => isOpen_Ioo)
    (show Icc (-Real.pi) Real.pi ⊆ ⋃ θ : ℝ, Ioo (a θ) (b θ) from
      fun θ _ => mem_iUnion.mpr ⟨θ, ha θ, hb θ⟩)
  let A₁ := ∑ θ ∈ s, A θ
  let N₁ := ∑ θ ∈ s, N θ
  have hA₁ : 0 ≤ A₁ := Finset.sum_nonneg fun θ _ => (hA θ).le
  let A₂ := max A₁ ‖f 0‖ + 1
  have hA₂ : 0 < A₂ := by
    have := hA₁.trans (le_max_left A₁ ‖f 0‖)
    dsimp [A₂]; linarith
  refine ⟨A₂, hA₂, N₁, fun z => ?_⟩
  by_cases hz : z = 0
  · subst z
    have hle : ‖f 0‖ ≤ A₂ := by dsimp [A₂]; linarith [le_max_right A₁ ‖f 0‖]
    simpa using hle
  · have harg : z.arg ∈ Icc (-Real.pi) Real.pi := ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
    obtain ⟨θ, hθs, hθ⟩ := mem_iUnion₂.mp (hs harg)
    have hw := hlocal θ (Complex.log z)
      (by simpa only [Complex.log_im] using hθ.1.le)
      (by simpa only [Complex.log_im] using hθ.2.le)
    rw [Complex.exp_log hz, Complex.log_re, Real.exp_log (norm_pos_iff.mpr hz)] at hw
    have hAA : A θ ≤ A₂ := by
      have hsum : A θ ≤ A₁ := Finset.single_le_sum (fun i _ => (hA i).le) hθs
      dsimp [A₂]; linarith [le_max_left A₁ ‖f 0‖]
    have hNN : N θ ≤ N₁ := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hθs
    exact hw.trans (mul_le_mul hAA (pow_le_pow_right₀ (by linarith [norm_nonneg z]) hNN)
      (by positivity) hA₂.le)

#print axioms between_rays
#print axioms local_bound_of_dense
#print axioms global_bound_of_dense
end CRGPhragmenPolynomialGlobal
