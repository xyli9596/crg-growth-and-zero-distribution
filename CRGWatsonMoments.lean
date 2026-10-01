import CRGWatsonTaylor

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CRGWatson

/-- Actual improper power moment along the negative real parameter ray. -/
def realPowerMoment (m j : ℕ) (A : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, t ^ j * Real.exp (-A * t ^ m)

theorem integrable_realPowerMoment {m : ℕ} (hm : 0 < m) (j : ℕ)
    {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun t : ℝ => t ^ j * Real.exp (-A * t ^ m)) (Ioi 0) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (-1 : ℝ) < j := by linarith [Nat.cast_nonneg (α := ℝ) j]
  simpa only [Real.rpow_natCast] using
    integrableOn_rpow_mul_exp_neg_mul_rpow hj hmR hA

/-- Gamma evaluation of every monomial moment. -/
theorem realPowerMoment_gamma {m : ℕ} (hm : 0 < m) (j : ℕ)
    {A : ℝ} (hA : 0 < A) :
    realPowerMoment m j A = A ^ (-((j : ℝ) + 1) / (m : ℝ)) *
      (1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (-1 : ℝ) < j := by linarith [Nat.cast_nonneg (α := ℝ) j]
  simpa only [realPowerMoment, Real.rpow_natCast] using
    integral_rpow_mul_exp_neg_mul_rpow hmR hj hA

/-- Truncating a monomial moment at the other endpoint produces an actual
exponentially small tail, uniformly for positive real parameters. -/
theorem powerMoment_tail_bound {m : ℕ} (hm : 0 < m) (j : ℕ)
    {A : ℝ} (hA : 0 < A) :
    (∫ t : ℝ in Ioi 1, t ^ j * Real.exp (-A * t ^ m)) ≤
      Real.exp (-A / 2) * ((A / 2) ^ (-((j : ℝ) + 1) / (m : ℝ)) *
        (1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ))) := by
  have hhalf : 0 < A / 2 := by positivity
  have hi := integrable_realPowerMoment hm j hA
  have hi' := integrable_realPowerMoment hm j hhalf
  have hci : IntegrableOn (fun t : ℝ => Real.exp (-A / 2) *
      (t ^ j * Real.exp (-(A / 2) * t ^ m))) (Ioi 0) :=
    hi'.const_mul (Real.exp (-A / 2))
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht))
  calc
    _ ≤ ∫ t : ℝ in Ioi 1, Real.exp (-A / 2) *
        (t ^ j * Real.exp (-(A / 2) * t ^ m)) := by
      apply setIntegral_mono_on (hi.mono_set hsub)
        (hci.mono_set hsub) measurableSet_Ioi
      intro t ht
      have hpow : 1 ≤ t ^ m := one_le_pow₀ (le_of_lt ht)
      have hexp : -A * t ^ m ≤ -A / 2 + -(A / 2) * t ^ m := by nlinarith
      have he := Real.exp_le_exp.mpr hexp
      rw [Real.exp_add] at he
      have hh := mul_le_mul_of_nonneg_left he (pow_nonneg (zero_lt_one.trans ht).le j)
      nlinarith [hh]
    _ ≤ ∫ t : ℝ in Ioi 0, Real.exp (-A / 2) *
        (t ^ j * Real.exp (-(A / 2) * t ^ m)) := by
      apply setIntegral_mono_set hci
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.exp_nonneg _)
          (mul_nonneg (pow_nonneg (mem_Ioi.mp ht).le _) (Real.exp_nonneg _))
      · exact Filter.Eventually.of_forall (fun t ht => hsub ht)
    _ = _ := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      exact realPowerMoment_gamma hm j hhalf

#print axioms realPowerMoment_gamma
#print axioms powerMoment_tail_bound
end CRGWatson
