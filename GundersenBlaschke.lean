import GundersenCartan
import LevinMinimumModulus

/-! Logarithmic derivatives of the actual Blaschke factors and their finite
products, retaining analytic multiplicities. -/
noncomputable section
open Set Metric Complex ComplexConjugate MeromorphicOn
open scoped BigOperators
namespace GundersenBlaschke

def factor (S : ℝ) (a z : ℂ) : ℂ :=
  (S : ℂ) * (z - a) / ((S : ℂ)^2 - conj a * z)

theorem factor_eq_inverse_canonical (S : ℝ) (a z : ℂ) :
    factor S a z = (canonicalFactor S a z)⁻¹ := by
  simp [factor, canonicalFactor_apply]

theorem factor_nonzero {S : ℝ} {a z : ℂ} (ha : a ∈ ball 0 S)
    (hz : z ∈ closedBall 0 S) (hza : z ≠ a) : factor S a z ≠ 0 := by
  have hS := pos_of_mem_ball ha
  exact div_ne_zero (mul_ne_zero (by exact_mod_cast hS.ne') (sub_ne_zero.mpr hza))
    (LevinFactorization.canonical_numerator_ne_zero ha hz)

theorem logDeriv_factor {S : ℝ} {a z : ℂ} (ha : a ∈ ball 0 S)
    (hz : z ∈ closedBall 0 S) (hza : z ≠ a) :
    logDeriv (factor S a) z = (z-a)⁻¹ + conj a / ((S : ℂ)^2 - conj a*z) := by
  have hS := pos_of_mem_ball ha
  unfold factor
  rw [logDeriv_div (f := fun w : ℂ => (S : ℂ)*(w-a))
    (g := fun w : ℂ => (S : ℂ)^2-conj a*w) z
    (mul_ne_zero (by exact_mod_cast hS.ne') (sub_ne_zero.mpr hza))
    (LevinFactorization.canonical_numerator_ne_zero ha hz) (by fun_prop) (by fun_prop),
    logDeriv_const_mul z (S : ℂ) (by exact_mod_cast hS.ne')]
  simp [logDeriv, neg_div, sub_neg_eq_add]

/-- The reflected zero in a Blaschke factor contributes at most 2/S on the half
disk. The near zero contributes the exact reciprocal distance. -/
theorem norm_logDeriv_factor_le {S : ℝ} {a z : ℂ} (ha : a ∈ ball 0 S)
    (hz : z ∈ closedBall 0 (S/2)) (hza : z ≠ a) :
    ‖logDeriv (factor S a) z‖ ≤ ‖z-a‖⁻¹ + 2/S := by
  have hS := pos_of_mem_ball ha
  have haS := (mem_ball_zero_iff.mp ha).le
  have hzS := mem_closedBall_zero_iff.mp hz
  have hz' : z ∈ closedBall 0 S := closedBall_subset_closedBall (by linarith) hz
  have hd : S^2/2 ≤ ‖(S : ℂ)^2 - conj a*z‖ := by
    have hn := norm_sub_norm_le ((S : ℂ)^2) (conj a*z)
    simp only [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hS, norm_mul, norm_conj] at hn
    nlinarith [mul_le_mul haS hzS (norm_nonneg z) hS.le]
  have hbd : ‖conj a / ((S : ℂ)^2 - conj a*z)‖ ≤ 2/S := by
    rw [norm_div, norm_conj]
    calc
      ‖a‖ / ‖(S : ℂ)^2 - conj a*z‖ ≤ S / (S^2/2) :=
        div_le_div₀ hS.le haS (by positivity) hd
      _ = _ := by field_simp
  rw [logDeriv_factor ha hz' hza]
  exact (norm_add_le _ _).trans (by simpa only [norm_inv] using add_le_add (le_refl ‖(z-a)⁻¹‖) hbd)

/-- Equality before taking norms, preserving all factors and zero multiplicities. -/
theorem finiteBlaschke_eq_product {f : ℂ → ℂ} {S : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) :
    LevinFactorization.finiteBlaschke f S =
      fun z => ∏ i : LevinMinimumModulus.ZeroIndex hf, factor S i.1.val z := by
  classical
  ext z
  rw [LevinFactorization.finiteBlaschke,
    finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop)
      hf.meromorphicOn.divisor_ball_support_finite, Finset.prod_apply,
    Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_coe_sort (LevinFiniteProduct.zeroSupport hf)
    (fun a => factor S a z ^ (divisor f (ball 0 S) a).toNat)]
  apply Finset.prod_congr rfl
  intro a _
  have hn := (hf.mono ball_subset_closedBall).divisor_nonneg a
  rw [factor_eq_inverse_canonical]
  simp only [Pi.pow_apply, zpow_neg]
  rw [← zpow_natCast, Int.toNat_of_nonneg hn, inv_zpow]

/-- The reciprocal sum estimate applies directly to the actual analytic
Blaschke product, without assuming the logarithmic derivative formula. -/
theorem exists_disks_finiteBlaschke_bound {f : ℂ → ℂ} {S H : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S)) (hS : 0 < S) (hH : 0 < H) :
    ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ r : Fin m → ℝ,
      (∀ j, 0 < r j) ∧ (∑ j, r j) ≤ 5*H ∧
      ∀ z ∈ closedBall 0 (S/2), (∀ j, z ∉ ball (c j) (r j)) →
        LevinFactorization.finiteBlaschke f S z ≠ 0 ∧
        ‖logDeriv (LevinFactorization.finiteBlaschke f S) z‖ ≤
          (Fintype.card (LevinMinimumModulus.ZeroIndex hf) : ℝ) / H *
            (1 + Real.log (Fintype.card (LevinMinimumModulus.ZeroIndex hf))) +
          Fintype.card (LevinMinimumModulus.ZeroIndex hf) * (2/S) := by
  classical
  let Z := LevinMinimumModulus.ZeroIndex hf
  obtain ⟨m, c, r, hr, hsum, hb⟩ := GundersenCartan.exists_disks_reciprocal_bound
    (fun i : Z => i.1.val) hH
  refine ⟨m, c, r, hr, hsum, fun z hz he => ?_⟩
  obtain ⟨hnz, hbound⟩ := hb z he
  have hi (i : Z) : i.1.val ∈ ball (0 : ℂ) S :=
    (divisor f (ball 0 S)).supportWithinDomain
      ((LevinFiniteProduct.mem_zeroSupport hf).mp i.1.property)
  have hz' : z ∈ closedBall 0 S := closedBall_subset_closedBall (by linarith) hz
  have hfactor (i : Z) : factor S i.1.val z ≠ 0 := factor_nonzero (hi i) hz' (hnz i)
  rw [finiteBlaschke_eq_product hf]
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => hfactor i), ?_⟩
  rw [logDeriv_prod (s := Finset.univ) (f := fun i : Z => factor S i.1.val)
    (fun i _ => hfactor i) (fun i _ => ?_)]
  · calc
      ‖∑ i : Z, logDeriv (factor S i.1.val) z‖ ≤ ∑ i : Z, ‖logDeriv (factor S i.1.val) z‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Z, (‖z-i.1.val‖⁻¹ + 2/S) :=
        Finset.sum_le_sum (fun i _ => norm_logDeriv_factor_le (hi i) hz (hnz i))
      _ = (∑ i : Z, ‖z-i.1.val‖⁻¹) + Fintype.card Z * (2/S) := by
        rw [Finset.sum_add_distrib]; simp
      _ ≤ _ := add_le_add hbound le_rfl
  · simpa only [← factor_eq_inverse_canonical] using
      ((LevinFactorization.analyticOnNhd_inverse_canonical (hi i)) z hz').differentiableAt

#print axioms factor_eq_inverse_canonical
#print axioms factor_nonzero
#print axioms logDeriv_factor
#print axioms norm_logDeriv_factor_le
#print axioms finiteBlaschke_eq_product
#print axioms exists_disks_finiteBlaschke_bound
end GundersenBlaschke
