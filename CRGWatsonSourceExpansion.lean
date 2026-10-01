import CRGWatsonFormalSeries
import CRGPolynomialKernelPuiseux

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial Asymptotics
open scoped Topology BigOperators Interval
namespace CRGWatson
open CRGPolynomialKernel CRGAsymptoticCoefficientQuotient
open CRGAsymptoticCoefficientScalarAlgebra

/-- A holomorphic germ fixes its formal series before a sectorial filter is
chosen, and its zero value fixes the zero constant term needed for substitution. -/
theorem exists_zero_constant_completeExpansion {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) :
    ∃ G : PowerSeries ℂ, PowerSeries.constantCoeff G = 0 ∧
      ∀ l : Filter ℂ, l ≤ 𝓝 (0 : ℂ) → CompleteExpansion l g G := by
  obtain ⟨G,hG⟩ := exists_completeExpansion_of_analyticAt hg
  refine ⟨G,?_,hG⟩
  have ht := tendsto_of_completeExpansion le_rfl (hG (𝓝 0) le_rfl)
  exact (tendsto_nhds_unique ht hg.continuousAt).trans hg0

/-- The cone Watson estimate gives all finite endpoint approximations after
substitution by any actual local inverse phase. -/
theorem growing_polynomial_approximations {w : ℝ → ℂ}
    (hw : AnalyticOnNhd ℝ w (Icc 0 1)) {m : ℕ} (hm : 0 < m)
    {l : Filter ℂ} {s g : ℂ → ℂ}
    (hs : Tendsto (fun x => ‖s x‖) l atTop)
    {c : ℝ} (hc : 0 < c) (hcone : ∀ᶠ x in l,c*‖s x‖ ≤ (s x).re)
    (hginv : ∀ᶠ x in l,g x = (s x)⁻¹)
    (N : ℕ) :
    (fun x => Complex.exp (-s x) * laplaceIntegral w (fun t => (t:ℂ)^m) (s x) -
      (PowerSeries.trunc (N+1) (growingFormalSeries (powerDensity w m))).eval (g x)) =O[l]
        (fun x => ‖g x‖^(N+1)) := by
  obtain ⟨B,hB,R,hR,hbound⟩ := analytic_growing_uniform_expansion hw hm N hc
  apply IsBigO.of_bound B
  filter_upwards [hs.eventually (eventually_ge_atTop R),hcone,hginv] with x hx hc hg
  rw [hg,←endpointSeries_eq_trunc]
  have hb := hbound (s x) hx hc
  simpa only [norm_inv,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _),
    inv_pow,div_eq_mul_inv] using hb

theorem norm_inverse_root_pow (s : ℂ) (m N : ℕ) :
    ‖s ^ (-(m:ℂ)⁻¹)‖^(N+1) = ‖s‖ ^ (-((N:ℝ)+1)/(m:ℝ)) := by
  have he := Complex.norm_cpow_real s (-(m:ℝ)⁻¹)
  simp only [Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_natCast] at he
  rw [he,←Real.rpow_natCast,
    ←Real.rpow_mul (norm_nonneg s)]
  congr 1
  push_cast
  ring

/-- The decaying cone estimate gives all finite Gamma-moment approximations
in an actual local principal inverse-root coordinate. -/
theorem decaying_polynomial_approximations {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (hwa : AnalyticAt ℝ w 0)
    {m : ℕ} (hm : 0 < m) {l : Filter ℂ} {s g : ℂ → ℂ}
    (hs : Tendsto (fun x => ‖s x‖) l atTop)
    {c : ℝ} (hc : 0 < c) (hcone : ∀ᶠ x in l,c*‖s x‖ ≤ (s x).re)
    (hgroot : ∀ᶠ x in l,g x = (s x) ^ (-(m:ℂ)⁻¹))
    (N : ℕ) :
    (fun x => laplaceIntegral w (fun t => (t:ℂ)^m) (-s x) -
      (PowerSeries.trunc (N+1) (decayingFormalSeries w m)).eval (g x)) =O[l]
        (fun x => ‖g x‖^(N+1)) := by
  obtain ⟨B,hB,R,hR,hbound⟩ := analytic_decaying_uniform_expansion hw hwa hm N hc
  apply IsBigO.of_bound B
  filter_upwards [hs.eventually (eventually_ge_atTop R),hcone,hgroot] with x hx hc hg
  rw [hg,←decayingSum_eq_trunc w hm]
  have hb := hbound (s x) hx hc
  simpa only [norm_inverse_root_pow,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hb

/-- The forced zero head lets integral approximations start at order one;
this supplies the order-zero bound needed by the general substitution theorem. -/
theorem completeExpansion_of_integral_approximations {l : Filter ℂ}
    (hl : l ≤ 𝓝 (0 : ℂ)) {K g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hg : CompleteExpansion l g G) (hG : PowerSeries.constantCoeff G = 0)
    (hF : PowerSeries.constantCoeff F = 0)
    (ha : ∀ N : ℕ, (fun x => K x - (PowerSeries.trunc (N+1) F).eval (g x)) =O[l]
      (fun x => ‖g x‖^(N+1))) :
    CompleteExpansion l K (formalComposition F G) := by
  apply completeExpansion_of_polynomial_approximations hl hg hG
  intro N
  cases N with
  | succ N => exact ha N
  | zero =>
    have hK : K =O[l] (fun x => ‖g x‖) := by
      simpa only [zero_add,PowerSeries.trunc_one_left,Polynomial.eval_C,
        PowerSeries.coeff_zero_eq_constantCoeff_apply,hF,sub_zero,pow_one] using ha 0
    have hgb : (fun x => ‖g x‖) =O[l] (fun _ : ℂ => (1:ℝ)) := by
      have ht := tendsto_of_completeExpansion hl hg
      rw [hG] at ht
      exact isBigO_const_of_tendsto (ht.norm) (by norm_num)
    simpa only [PowerSeries.trunc_zero',Polynomial.eval_zero,sub_zero,pow_zero] using hK.trans hgb

/-- A fixed analytic inverse-phase germ supplies the complete growing
endpoint series on every closed cone filter, before choosing any direction. -/
theorem exists_growing_completeExpansion {w : ℝ → ℂ}
    (hw : AnalyticOnNhd ℝ w (Icc 0 1)) {m : ℕ} (hm : 0 < m)
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) :
    ∃ A : PowerSeries ℂ, ∀ l : Filter ℂ, l ≤ 𝓝 (0 : ℂ) →
      ∀ s : ℂ → ℂ, Tendsto (fun x => ‖s x‖) l atTop →
      ∀ c : ℝ, 0 < c → (∀ᶠ x in l, c*‖s x‖ ≤ (s x).re) →
        (∀ᶠ x in l, g x = (s x)⁻¹) →
      CompleteExpansion l (fun x => Complex.exp (-s x) *
        laplaceIntegral w (fun t => (t:ℂ)^m) (s x)) A := by
  obtain ⟨G,hG,hge⟩ := exists_zero_constant_completeExpansion hg hg0
  refine ⟨formalComposition (growingFormalSeries (powerDensity w m)) G,?_⟩
  intro l hl s hs c hc hcone hginv
  exact completeExpansion_of_integral_approximations hl (hge l hl) hG
    (integralSeries_constantCoeff _) (growing_polynomial_approximations hw hm hs hc hcone hginv)

/-- A fixed analytic inverse-root germ supplies the complete decaying
Gamma-moment series on every closed cone filter, before choosing any direction. -/
theorem exists_decaying_completeExpansion {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (hwa : AnalyticAt ℝ w 0)
    {m : ℕ} (hm : 0 < m) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) :
    ∃ A : PowerSeries ℂ, ∀ l : Filter ℂ, l ≤ 𝓝 (0 : ℂ) →
      ∀ s : ℂ → ℂ, Tendsto (fun x => ‖s x‖) l atTop →
      ∀ c : ℝ, 0 < c → (∀ᶠ x in l, c*‖s x‖ ≤ (s x).re) →
        (∀ᶠ x in l, g x = (s x) ^ (-(m:ℂ)⁻¹)) →
      CompleteExpansion l (fun x => laplaceIntegral w (fun t => (t:ℂ)^m) (-s x)) A := by
  obtain ⟨G,hG,hge⟩ := exists_zero_constant_completeExpansion hg hg0
  refine ⟨formalComposition (decayingFormalSeries w m) G,?_⟩
  intro l hl s hs c hc hcone hgroot
  exact completeExpansion_of_integral_approximations hl (hge l hl) hG
    (integralSeries_constantCoeff _) (decaying_polynomial_approximations hw hwa hm hs hc hcone hgroot)

/-- The same growing expansion applies to a finite grouped density, including
its integrable singularity at zero; only the upper endpoint is analytic. -/
theorem density_growing_polynomial_approximations {v : ℝ → ℂ}
    (hvi : IntervalIntegrable v MeasureTheory.volume 0 1)
    (hva : AnalyticOnNhd ℝ v (Ioc 0 1))
    {l : Filter ℂ} {s g : ℂ → ℂ}
    (hs : Tendsto (fun x => ‖s x‖) l atTop)
    {c : ℝ} (hc : 0 < c) (hcone : ∀ᶠ x in l,c*‖s x‖ ≤ (s x).re)
    (hginv : ∀ᶠ x in l,g x = (s x)⁻¹) (N : ℕ) :
    (fun x => Complex.exp (-s x) * laplaceIntegral v (fun t => (t:ℂ)) (s x) -
      (PowerSeries.trunc (N+1) (growingFormalSeries v)).eval (g x)) =O[l]
        (fun x => ‖g x‖^(N+1)) := by
  have hupper : AnalyticOnNhd ℝ v [[(1/2:ℝ),1]] := by
    apply hva.mono
    rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)]
    intro u hu
    exact ⟨by linarith [hu.1],hu.2⟩
  obtain ⟨B,hB,R,hR,hbound⟩ := growing_density_uniform_expansion
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) hvi hupper N hc
  apply IsBigO.of_bound B
  filter_upwards [hs.eventually (eventually_ge_atTop R),hcone,hginv] with x hx hc hg
  rw [hg,←endpointSeries_eq_trunc]
  have hb := hbound (s x) hx hc
  simpa only [CRGLinearKernelIntegration.kernel,CRGPolynomialKernel.laplaceIntegral,
    norm_inv,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _),
    inv_pow,div_eq_mul_inv] using hb

theorem exists_density_growing_completeExpansion {v : ℝ → ℂ}
    (hvi : IntervalIntegrable v MeasureTheory.volume 0 1)
    (hva : AnalyticOnNhd ℝ v (Ioc 0 1))
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) :
    ∃ A : PowerSeries ℂ, ∀ l : Filter ℂ, l ≤ 𝓝 (0 : ℂ) →
      ∀ s : ℂ → ℂ, Tendsto (fun x => ‖s x‖) l atTop →
      ∀ c : ℝ, 0 < c → (∀ᶠ x in l, c*‖s x‖ ≤ (s x).re) →
        (∀ᶠ x in l, g x = (s x)⁻¹) →
      CompleteExpansion l (fun x => Complex.exp (-s x) *
        laplaceIntegral v (fun t => (t:ℂ)) (s x)) A := by
  obtain ⟨G,hG,hge⟩ := exists_zero_constant_completeExpansion hg hg0
  refine ⟨formalComposition (growingFormalSeries v) G,?_⟩
  intro l hl s hs c hc hcone hginv
  exact completeExpansion_of_integral_approximations hl (hge l hl) hG
    (integralSeries_constantCoeff _) (density_growing_polynomial_approximations hvi hva hs hc hcone hginv)

#print axioms exists_zero_constant_completeExpansion
#print axioms growing_polynomial_approximations
#print axioms decaying_polynomial_approximations
end CRGWatson
