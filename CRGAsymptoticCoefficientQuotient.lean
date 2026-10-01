import CRGAsymptoticCoefficientPullback
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Division of complete scalar asymptotic expansions by a nonzero formal
series, including arbitrary leading powers and flat numerators. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace CRGAsymptoticCoefficientQuotient

/-- Full scalar asymptotic expansion on a specified sectorial filter. -/
def CompleteExpansion (l : Filter ℂ) (f : ℂ → ℂ) (A : PowerSeries ℂ) : Prop :=
  ∀ N : ℕ, (fun z => f z - (PowerSeries.trunc N A).eval z) =O[l]
    (fun z : ℂ => ‖z‖^N)

/-- The pole-cleared convention for a full Laurent asymptotic expansion. -/
def LaurentExpansion (l : Filter ℂ) (f : ℂ → ℂ) (b : ℕ) (A : PowerSeries ℂ) : Prop :=
  CompleteExpansion l (fun z => z^b*f z) A

/-- A zero formal expansion is smaller than every positive integer power. -/
def Flat (l : Filter ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ N : ℕ, f =O[l] (fun z : ℂ => ‖z‖^N)

theorem flat_iff_zero_expansion (l : Filter ℂ) (f : ℂ → ℂ) :
    Flat l f ↔ CompleteExpansion l f 0 := by
  simp only [Flat,CompleteExpansion,map_zero,Polynomial.eval_zero,sub_zero]

theorem isBigO_polynomial_of_X_pow_dvd (P : Polynomial ℂ) (N : ℕ)
    (hP : Polynomial.X^N ∣ P) :
    (fun z => P.eval z) =O[𝓝 (0 : ℂ)] (fun z : ℂ => ‖z‖^N) := by
  obtain ⟨Q,rfl⟩ := hP
  have hQ : (fun z => Q.eval z) =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1:ℝ)) :=
    isBigO_const_of_tendsto (Q.continuous.tendsto 0) (by norm_num)
  have hp : (fun z : ℂ => z^N) =O[𝓝 0] (fun z : ℂ => ‖z‖^N) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with z
    simp
  simpa only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,mul_one] using hp.mul hQ

/-- The leading constant of an asymptotic unit is the actual sectorial limit. -/
theorem tendsto_of_completeExpansion
    {l : Filter ℂ} (hl : l ≤ 𝓝 (0 : ℂ)) {f : ℂ → ℂ} {A : PowerSeries ℂ}
    (hf : CompleteExpansion l f A) : Tendsto f l (𝓝 (PowerSeries.constantCoeff A)) := by
  have ht : Tendsto (fun z : ℂ => ‖z‖^1) l (𝓝 (0:ℝ)) := by
    simpa only [pow_one,norm_zero] using continuous_norm.tendsto (0:ℂ) |>.mono_left hl
  have hh := (hf 1).trans_tendsto ht
  simp only [PowerSeries.trunc_one_left,Polynomial.eval_C,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at hh
  simpa only [sub_add_cancel,zero_add] using hh.add_const (PowerSeries.constantCoeff A)

/-- Inversion of the actual coefficient is bounded on the same filter once
its formal leading constant is nonzero. -/
theorem inverse_bounded_of_completeExpansion
    {l : Filter ℂ} (hl : l ≤ 𝓝 (0 : ℂ)) {f : ℂ → ℂ} {A : PowerSeries ℂ}
    (hf : CompleteExpansion l f A) (hA : PowerSeries.constantCoeff A ≠ 0) :
    (fun z => (f z)⁻¹) =O[l] (fun _ : ℂ => (1:ℝ)) :=
  isBigO_const_of_tendsto ((tendsto_of_completeExpansion hl hf).inv₀ hA) (by norm_num)

theorem eventually_ne_zero_of_completeExpansion
    {l : Filter ℂ} (hl : l ≤ 𝓝 (0 : ℂ)) {f : ℂ → ℂ} {A : PowerSeries ℂ}
    (hf : CompleteExpansion l f A) (hA : PowerSeries.constantCoeff A ≠ 0) :
    ∀ᶠ z in l, f z ≠ 0 := by
  exact (tendsto_of_completeExpansion hl hf).eventually_ne hA

/-- Division is carried out in the formal power-series ring. The output
coefficients are the actual quotient expansion, even when either series
has radius of convergence zero. -/
theorem completeExpansion_quotient_unit
    {l : Filter ℂ} (hl : l ≤ 𝓝 (0 : ℂ))
    {f g : ℂ → ℂ} {A B : PowerSeries ℂ}
    (hf : CompleteExpansion l f A) (hg : CompleteExpansion l g B)
    (hB : PowerSeries.constantCoeff B ≠ 0) :
    CompleteExpansion l (fun z => f z/g z) (A*B⁻¹) := by
  intro N
  let Q := A*B⁻¹
  have hBQ : B*Q=A := by
    dsimp [Q]
    rw [mul_comm A _, ← mul_assoc, PowerSeries.mul_inv_cancel B hB, one_mul]
  have hfinite : (fun z : ℂ =>
      (PowerSeries.trunc N A - PowerSeries.trunc N B * PowerSeries.trunc N Q).eval z) =O[l]
      (fun z : ℂ => ‖z‖^N) := by
    apply (isBigO_polynomial_of_X_pow_dvd _ N ?_).mono hl
    apply Polynomial.X_pow_dvd_iff.mpr
    intro k hk
    rw [Polynomial.coeff_sub,PowerSeries.coeff_trunc,if_pos hk]
    have he := PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc B Q hk
    rw [hBQ] at he
    rw [← Polynomial.coe_mul,Polynomial.coeff_coe] at he
    rw [← he,sub_self]
  have hpoly : (fun z : ℂ => (PowerSeries.trunc N Q).eval z) =O[l]
      (fun _ : ℂ => (1:ℝ)) :=
    isBigO_const_of_tendsto (((PowerSeries.trunc N Q).continuous.tendsto 0).mono_left hl)
      (by norm_num)
  have hnum : (fun z : ℂ => f z - g z*(PowerSeries.trunc N Q).eval z) =O[l]
      (fun z : ℂ => ‖z‖^N) := by
    have hgp : (fun z : ℂ =>
        (g z - (PowerSeries.trunc N B).eval z)*(PowerSeries.trunc N Q).eval z) =O[l]
        (fun z : ℂ => ‖z‖^N) := by
      simpa only [mul_one] using (hg N).mul hpoly
    exact (((hf N).sub hgp).add hfinite).congr_left (fun z => by
      rw [Polynomial.eval_sub,Polynomial.eval_mul]
      ring)
  have hinv := inverse_bounded_of_completeExpansion hl hg hB
  have hout : (fun z : ℂ => (f z - g z*(PowerSeries.trunc N Q).eval z)*(g z)⁻¹) =O[l]
      (fun z : ℂ => ‖z‖^N) := by
    simpa only [mul_one] using hnum.mul hinv
  apply hout.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ne_zero_of_completeExpansion hl hg hB] with z hz
  dsimp [Q]
  field_simp

/-- Removing the leading monomial gives an asymptotic unit and exactly the
formal coefficient shift divXPowOrder. -/
theorem completeExpansion_remove_leading
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0 : ℂ))
    {g : ℂ → ℂ} {B : PowerSeries ℂ} (hg : CompleteExpansion l g B) :
    CompleteExpansion l (fun z => z^(-(B.order.toNat:ℤ))*g z) B.divXPowOrder := by
  intro N
  let b := B.order.toNat
  let U := B.divXPowOrder
  have hB : PowerSeries.X^b*U=B := PowerSeries.X_pow_order_mul_divXPowOrder
  have htrunc : PowerSeries.trunc (N+b) B = Polynomial.X^b * PowerSeries.trunc N U := by
    rw [← hB]
    ext n
    rw [PowerSeries.coeff_trunc,Polynomial.coeff_X_pow_mul',PowerSeries.coeff_X_pow_mul']
    split_ifs <;> simp_all only [PowerSeries.coeff_trunc]
    all_goals split_ifs <;> try omega
    all_goals simp_all
  obtain ⟨C,hC,hbound⟩ := (hg (N+b)).exists_pos
  apply IsBigO.of_bound C
  filter_upwards [hbound.bound,
    (show ∀ᶠ z in l,z≠0 from Filter.Eventually.filter_mono hl self_mem_nhdsWithin)] with z hz hzne
  have hr : z^(-(b:ℤ))*g z - (PowerSeries.trunc N U).eval z =
      z^(-(b:ℤ))*(g z - (PowerSeries.trunc (N+b) B).eval z) := by
    rw [htrunc,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]
    rw [zpow_neg,zpow_natCast]
    field_simp
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hzne
  change ‖z^(-(b:ℤ))*g z - (PowerSeries.trunc N U).eval z‖ ≤ C*‖‖z‖^N‖
  rw [hr,norm_mul,zpow_neg,zpow_natCast,norm_inv,norm_pow]
  have hz' : ‖g z - (PowerSeries.trunc (N+b) B).eval z‖ ≤ C*‖z‖^(N+b) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg z) _)] using hz
  calc
    _ ≤ (‖z‖^b)⁻¹*(C*‖z‖^(N+b)) := mul_le_mul_of_nonneg_left hz' (by positivity)
    _ = _ := by
      rw [pow_add]
      simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg z) _)]
      field_simp

/-- A nonzero denominator expansion has no actual zeros on a sectorial tail. -/
theorem eventually_ne_zero_of_nonzero_series
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0 : ℂ))
    {g : ℂ → ℂ} {B : PowerSeries ℂ} (hg : CompleteExpansion l g B) (hB : B≠0) :
    ∀ᶠ z in l,g z≠0 := by
  have hU : PowerSeries.constantCoeff B.divXPowOrder ≠ 0 :=
    PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hB
  have hnorm := completeExpansion_remove_leading hl hg
  filter_upwards [eventually_ne_zero_of_completeExpansion (hl.trans nhdsWithin_le_nhds) hnorm hU]
    with z hz
  intro hzero
  exact hz (by rw [hzero,mul_zero])

/-- General full Laurent quotient expansion. Its finite pole is the formal
order of the denominator; its coefficients depend only on the two original
formal series. -/
theorem laurentExpansion_quotient
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0 : ℂ))
    {f g : ℂ → ℂ} {A B : PowerSeries ℂ}
    (hf : CompleteExpansion l f A) (hg : CompleteExpansion l g B) (hB : B≠0) :
    LaurentExpansion l (fun z => f z/g z) B.order.toNat (A*B.divXPowOrder⁻¹) := by
  have hU : PowerSeries.constantCoeff B.divXPowOrder ≠ 0 :=
    PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hB
  have he := completeExpansion_quotient_unit (hl.trans nhdsWithin_le_nhds) hf
    (completeExpansion_remove_leading hl hg) hU
  intro N
  apply (he N).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [(show ∀ᶠ z in l,z≠0 from Filter.Eventually.filter_mono hl self_mem_nhdsWithin)]
    with z hz
  simp only [zpow_neg,zpow_natCast]
  field_simp

/-- Removing any fixed nonnegative power from a flat function preserves
flatness. This is the precise finite power loss in division by a leading term. -/
theorem flat_cancel_power
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0 : ℂ)) {f : ℂ → ℂ} (b : ℕ)
    (hf : Flat l (fun z => z^b*f z)) : Flat l f := by
  intro N
  obtain ⟨C,hC,hbound⟩ := (hf (N+b)).exists_pos
  apply IsBigO.of_bound C
  filter_upwards [hbound.bound,
    (show ∀ᶠ z in l,z≠0 from Filter.Eventually.filter_mono hl self_mem_nhdsWithin)] with z hz hzne
  have hnz : 0<‖z‖^b := pow_pos (norm_pos_iff.mpr hzne) _
  have hh : ‖z‖^b*‖f z‖≤‖z‖^b*(C*‖z‖^N) := by
    simpa only [norm_mul,norm_pow,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg z) _),abs_of_nonneg (norm_nonneg z),
      pow_add,mul_assoc,mul_left_comm,mul_comm] using hz
  have hh' := (mul_le_mul_iff_right₀ hnz).mp hh
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg z) _)] using hh'

/-- A complete zero-series numerator divided by any nonzero-series
denominator remains flat; there is no hidden convergence hypothesis. -/
theorem flat_quotient
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0 : ℂ))
    {f g : ℂ → ℂ} {B : PowerSeries ℂ} (hf : Flat l f)
    (hg : CompleteExpansion l g B) (hB : B≠0) : Flat l (fun z => f z/g z) := by
  have hx := laurentExpansion_quotient hl ((flat_iff_zero_expansion l f).mp hf) hg hB
  simp only [zero_mul] at hx
  exact flat_cancel_power hl B.order.toNat ((flat_iff_zero_expansion _ _).mpr hx)

/-- Polynomially bounded factors preserve flatness. -/
theorem flat_mul_of_power_bound
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0 : ℂ)) {f g : ℂ → ℂ}
    (hf : Flat l f) (K : ℕ)
    (hg : g =O[l] (fun z : ℂ => (‖z‖^K)⁻¹)) : Flat l (fun z => f z*g z) := by
  intro N
  have hh := (hf (N+K)).mul hg
  apply hh.congr' Filter.EventuallyEq.rfl ?_
  filter_upwards [(show ∀ᶠ z in l,z≠0 from Filter.Eventually.filter_mono hl self_mem_nhdsWithin)]
    with z hz
  have hnz : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
  rw [pow_add]
  field_simp

/-- A nonzero formal series cannot simultaneously be the complete expansion
of a flat function on a genuine approach filter. -/
theorem nonzero_series_not_flat
    {l : Filter ℂ} [NeBot l] (hl : l ≤ 𝓝[≠] (0 : ℂ))
    {g : ℂ → ℂ} {B : PowerSeries ℂ} (hg : CompleteExpansion l g B) (hB : B≠0) :
    ¬Flat l g := by
  intro hflat
  have hnorm := completeExpansion_remove_leading hl hg
  have hnormflat : Flat l (fun z => z^(-(B.order.toNat:ℤ))*g z) := by
    have hx : Flat l (fun z => z^B.order.toNat*(z^(-(B.order.toNat:ℤ))*g z)) := by
      intro N
      apply (hflat N).congr' ?_ Filter.EventuallyEq.rfl
      filter_upwards [(show ∀ᶠ z in l,z≠0 from Filter.Eventually.filter_mono hl self_mem_nhdsWithin)]
        with z hz
      simp only [zpow_neg,zpow_natCast]
      field_simp
    exact flat_cancel_power hl B.order.toNat hx
  have ht₁ := tendsto_of_completeExpansion (hl.trans nhdsWithin_le_nhds) hnorm
  have ht₀ := tendsto_of_completeExpansion (hl.trans nhdsWithin_le_nhds)
    ((flat_iff_zero_expansion _ _).mp hnormflat)
  have he := tendsto_nhds_unique ht₁ ht₀
  have hU : PowerSeries.constantCoeff B.divXPowOrder ≠ 0 :=
    PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hB
  exact hU (by simpa only [map_zero] using he)

#print axioms flat_cancel_power
#print axioms flat_quotient
#print axioms flat_mul_of_power_bound
#print axioms nonzero_series_not_flat
#print axioms tendsto_of_completeExpansion
#print axioms inverse_bounded_of_completeExpansion
#print axioms eventually_ne_zero_of_completeExpansion
#print axioms completeExpansion_quotient_unit
#print axioms completeExpansion_remove_leading
#print axioms eventually_ne_zero_of_nonzero_series
#print axioms laurentExpansion_quotient
end CRGAsymptoticCoefficientQuotient
