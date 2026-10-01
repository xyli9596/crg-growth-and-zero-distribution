import CRGPhragmenGrowth

/-! The dense-ray growth estimates become one global finite-type estimate.
The constants are selected only after taking a genuine finite angular subcover. -/
noncomputable section
open Set Filter Complex Metric
open scoped Topology BigOperators
namespace CRGPhragmenGlobal

/-- The dense-ray exponential bound used in the order lemma. -/
theorem global_bound_of_dense {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfinite : CRGOrder.FiniteOrder f) {τ : ℝ} (hτ : 0 ≤ τ)
    {D : Set ℝ} (hD : Dense D)
    (hbound : ∀ θ ∈ D, CRGPhragmenGrowth.RayBound f τ θ) :
    ∃ A : ℝ, 0 < A ∧ ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ,
      ‖f z‖ ≤ A * Real.exp (K * ‖z‖ ^ τ) := by
  classical
  obtain ⟨ρ, hρ, horder⟩ := hfinite
  let κ := max (ρ + 1) (τ + 1)
  have hρκ : ρ < κ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hκ : 0 < κ := lt_of_le_of_lt hρ hρκ
  have hτκ : τ ≤ κ := le_trans (by linarith) (le_max_right _ _)
  have hlocal := CRGPhragmenGrowth.local_bound_of_dense hf horder hρκ hκ hτ hτκ hD hbound
  choose a b ha hb A hA K hK hlocal using hlocal
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover
    (fun θ : ℝ => Ioo (a θ) (b θ)) (fun _ => isOpen_Ioo)
    (show Icc (-Real.pi) Real.pi ⊆ ⋃ θ : ℝ, Ioo (a θ) (b θ) from
      fun θ _ => mem_iUnion.mpr ⟨θ, ha θ, hb θ⟩)
  let A₁ := ∑ θ ∈ s, A θ
  let K₁ := (∑ θ ∈ s, K θ) + 1
  have hA₁ : 0 ≤ A₁ := Finset.sum_nonneg fun θ _ => (hA θ).le
  have hK₁ : 0 < K₁ := by
    have : 0 ≤ ∑ θ ∈ s, K θ := Finset.sum_nonneg fun θ _ => (hK θ).le
    dsimp [K₁]; linarith
  let A₂ := max A₁ ‖f 0‖ + 1
  have hA₂ : 0 < A₂ := by
    have := hA₁.trans (le_max_left A₁ ‖f 0‖)
    dsimp [A₂]; linarith
  refine ⟨A₂, hA₂, K₁, hK₁, fun z => ?_⟩
  by_cases hz : z = 0
  · subst z
    have hle : ‖f 0‖ ≤ A₂ := by dsimp [A₂]; linarith [le_max_right A₁ ‖f 0‖]
    exact hle.trans (le_mul_of_one_le_right hA₂.le
      (Real.one_le_exp (mul_nonneg hK₁.le (Real.rpow_nonneg (norm_nonneg _) _))))
  · have harg : z.arg ∈ Icc (-Real.pi) Real.pi := ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
    obtain ⟨θ, hθs, hθ⟩ := mem_iUnion₂.mp (hs harg)
    have hw := hlocal θ (Complex.log z) (by simpa only [Complex.log_im] using hθ.1.le) (by simpa only [Complex.log_im] using hθ.2.le)
    rw [Complex.exp_log hz, Complex.log_re] at hw
    have hpow : Real.exp (τ * Real.log ‖z‖) = ‖z‖ ^ τ := by
      rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz), mul_comm]
    rw [hpow] at hw
    have hAA : A θ ≤ A₂ := by
      have hsum : A θ ≤ A₁ := Finset.single_le_sum (fun i _ => (hA i).le) hθs
      dsimp [A₂]; linarith [le_max_left A₁ ‖f 0‖]
    have hKK : K θ ≤ K₁ := by
      have hsum : K θ ≤ ∑ i ∈ s, K i := Finset.single_le_sum (fun i _ => (hK i).le) hθs
      dsimp [K₁]; linarith
    exact hw.trans (mul_le_mul hAA (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hKK (Real.rpow_nonneg (norm_nonneg _) _)))
      (Real.exp_pos _).le hA₂.le)

/-- Remove the harmless prefactor on all sufficiently large radii. -/
theorem finiteType_of_dense {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfinite : CRGOrder.FiniteOrder f) {τ : ℝ} (hτ : 0 ≤ τ)
    {D : Set ℝ} (hD : Dense D)
    (hbound : ∀ θ ∈ D, CRGPhragmenGrowth.RayBound f τ θ) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ,
      R ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (C * ‖z‖ ^ τ) := by
  obtain ⟨A, hA, K, hK, h⟩ := global_bound_of_dense hf hfinite hτ hD hbound
  refine ⟨K + A, by positivity, 1, zero_lt_one, fun z hz => ?_⟩
  apply (h z).trans
  have hpow : 1 ≤ ‖z‖ ^ τ := Real.one_le_rpow hz hτ
  have hAexp : A ≤ Real.exp (A * ‖z‖ ^ τ) := by
    have hmul : A ≤ A * ‖z‖ ^ τ := le_mul_of_one_le_right hA.le hpow
    linarith [Real.add_one_le_exp (A * ‖z‖ ^ τ)]
  calc
    A * Real.exp (K * ‖z‖ ^ τ) ≤
        Real.exp (A * ‖z‖ ^ τ) * Real.exp (K * ‖z‖ ^ τ) :=
      mul_le_mul_of_nonneg_right hAexp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

#print axioms global_bound_of_dense
#print axioms finiteType_of_dense
end CRGPhragmenGlobal
