import CRGWatsonSourceExpansion
import CRGPolynomialKernelCancellation

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial
open scoped Topology BigOperators
namespace CRGPolynomialKernel
open CRGAsymptoticCoefficientScalarAlgebra CRGWatson

theorem constantCoeff_formalComposition (F G : PowerSeries ℂ) :
    PowerSeries.constantCoeff (formalComposition F G) = PowerSeries.constantCoeff F := by
  rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [formalComposition,PowerSeries.coeff_mk,zero_add,Finset.sum_range_one,
    pow_zero,map_one,mul_one,PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Substitution into a nonzero zero-constant formal germ cannot erase the
first nonzero coefficient, even for divergent outer series. -/
theorem formalComposition_ne_zero {F G : PowerSeries ℂ}
    (hF : F ≠ 0) (hG : G ≠ 0) (hG0 : PowerSeries.constantCoeff G = 0) :
    formalComposition F G ≠ 0 := by
  let k := F.order.toNat
  let q := G.order.toNat
  have hqorder : (q : ENat) = G.order := PowerSeries.coe_toNat_order hG
  have hq : 0 < q := by
    have hh := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hG0
    rw [←hqorder] at hh
    exact_mod_cast hh
  have hmem : k ∈ Finset.range (q*k+1) := by
    simp only [Finset.mem_range]
    have hk : k ≤ q*k := by nlinarith
    omega
  have hcoeff : PowerSeries.coeff (q*k) (formalComposition F G) =
      PowerSeries.coeff k F * PowerSeries.coeff (q*k) (G^k) := by
    rw [formalComposition,PowerSeries.coeff_mk]
    apply Finset.sum_eq_single_of_mem k hmem
    intro j _ hj
    rcases lt_or_gt_of_ne hj with hj | hj
    · rw [PowerSeries.coeff_of_lt_order_toNat _ hj,zero_mul]
    · have hlow : (q*k : ENat) < (G^j).order := by
        rw [PowerSeries.order_pow,←hqorder]
        simp only [nsmul_eq_mul,←Nat.cast_mul]
        exact_mod_cast (by simpa only [Nat.mul_comm j q] using Nat.mul_lt_mul_of_pos_left hj hq)
      rw [PowerSeries.coeff_of_lt_order _ hlow,mul_zero]
  have hpoworder : (G^k).order.toNat = q*k := by
    rw [PowerSeries.order_pow,←hqorder]
    simp only [nsmul_eq_mul,←Nat.cast_mul,ENat.toNat_natCast]
    exact Nat.mul_comm k q
  have hnonzero : PowerSeries.coeff (q*k) (formalComposition F G) ≠ 0 := by
    rw [hcoeff,←hpoworder]
    exact mul_ne_zero (PowerSeries.coeff_order hF) (PowerSeries.coeff_order (pow_ne_zero k hG))
  intro hz
  rw [hz,map_zero] at hnonzero
  exact hnonzero rfl

/-- A grouped nonzero analytic density has a nonzero formal endpoint series;
all endpoint jets zero would force the actual integral to disappear. -/
theorem growingFormalSeries_ne_zero {v : ℝ → ℂ}
    (hv : AnalyticOnNhd ℝ v (Ioc 0 1)) (hn : ¬EqOn v 0 (Ioc 0 1)) :
    growingFormalSeries v ≠ 0 := by
  have he : ∃ t ∈ Ioc (0:ℝ) 1, v t ≠ 0 := by
    by_contra h
    apply hn
    intro t ht
    by_contra hz
    exact h ⟨t,ht,hz⟩
  obtain ⟨j,hj⟩ := exists_nonzero_endpoint_derivative hv he
  intro hz
  have hc := congrArg (PowerSeries.coeff (j+1)) hz
  simp only [growingFormalSeries,integralSeries,PowerSeries.coeff_mk,
    Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,Nat.add_sub_cancel,
    map_zero] at hc
  exact (mul_ne_zero (pow_ne_zero j (by norm_num : (-1:ℂ)≠0)) hj) hc

/-- A nonvanishing analytic germ supplies a nonzero fixed complete series.
This uses its actual finite analytic order, rather than an assumed formal head. -/
theorem exists_nonzero_completeExpansion_of_analyticAt {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (horder : analyticOrderAt g 0 ≠ ⊤) :
    ∃ G : PowerSeries ℂ, G ≠ 0 ∧ ∀ l : Filter ℂ,
      l ≤ 𝓝 (0:ℂ) → CRGAsymptoticCoefficientQuotient.CompleteExpansion l g G := by
  let k := (analyticOrderAt g 0).toNat
  have hk : analyticOrderAt g 0 = (k : ENat) :=
    (ENat.natCast_toNat_eq_self.mpr horder).symm
  obtain ⟨u,hu,hun,hgu⟩ := hg.analyticOrderAt_eq_natCast.mp hk
  obtain ⟨U,hU⟩ := exists_completeExpansion_of_analyticAt hu
  have hU0 : PowerSeries.constantCoeff U = u 0 := by
    exact tendsto_nhds_unique
      (CRGAsymptoticCoefficientQuotient.tendsto_of_completeExpansion le_rfl (hU (𝓝 0) le_rfl))
      hu.continuousAt
  have hUn : U ≠ 0 := by
    intro hz
    have hh := hU0
    rw [hz,map_zero] at hh
    exact hun hh.symm
  refine ⟨PowerSeries.X^k*U,mul_ne_zero (pow_ne_zero k PowerSeries.X_ne_zero) hUn,?_⟩
  intro l hl N
  have hmono : CRGAsymptoticCoefficientQuotient.CompleteExpansion l
      (fun x:ℂ=>x^k) (PowerSeries.X^k) := by
    simpa only [Polynomial.coe_pow,Polynomial.coe_X,Polynomial.eval_pow,Polynomial.eval_X] using
      (CRGAsymptoticCoefficientMatrixTransfer.polynomial_completeExpansion hl (Polynomial.X^k))
  have he := completeExpansion_mul hl hmono (hU l hl) N
  apply he.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hgu.filter_mono hl] with x hx
  rw [hx]
  simp only [sub_zero,smul_eq_mul]

/-- A nonzero grouped upper endpoint remains nonzero after the genuine
ramified polynomial substitution. -/
theorem exists_nonzero_density_growing_completeExpansion {v : ℝ → ℂ}
    (hvi : IntervalIntegrable v MeasureTheory.volume 0 1)
    (hva : AnalyticOnNhd ℝ v (Ioc 0 1)) (hvn : ¬EqOn v 0 (Ioc 0 1))
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (horder : analyticOrderAt g 0 ≠ ⊤) :
    ∃ A : PowerSeries ℂ, A ≠ 0 ∧ PowerSeries.constantCoeff A=0 ∧
      ∀ l : Filter ℂ, l ≤ 𝓝 (0:ℂ) → ∀ s : ℂ → ℂ,
        Tendsto (fun x=>‖s x‖) l atTop → ∀ c : ℝ, 0<c →
          (∀ᶠ x in l,c*‖s x‖ ≤ (s x).re) → (∀ᶠ x in l,g x=(s x)⁻¹) →
        CRGAsymptoticCoefficientQuotient.CompleteExpansion l
          (fun x=>Complex.exp (-s x)*laplaceIntegral v (fun t=>(t:ℂ)) (s x)) A := by
  obtain ⟨G,hGn,hge⟩ := exists_nonzero_completeExpansion_of_analyticAt hg horder
  have hG0 : PowerSeries.constantCoeff G = 0 := by
    exact (tendsto_nhds_unique
      (CRGAsymptoticCoefficientQuotient.tendsto_of_completeExpansion le_rfl (hge (𝓝 0) le_rfl))
      hg.continuousAt).trans hg0
  refine ⟨formalComposition (growingFormalSeries v) G,
    formalComposition_ne_zero (growingFormalSeries_ne_zero hva hvn) hGn hG0,
    (constantCoeff_formalComposition _ _).trans (integralSeries_constantCoeff _),?_⟩
  intro l hl s hs c hc hcone hginv
  exact completeExpansion_of_integral_approximations hl (hge l hl) hG0
    (integralSeries_constantCoeff _) (density_growing_polynomial_approximations hvi hva hs hc hcone hginv)

#print axioms formalComposition_ne_zero
#print axioms growingFormalSeries_ne_zero
#print axioms exists_nonzero_completeExpansion_of_analyticAt
#print axioms exists_nonzero_density_growing_completeExpansion
end CRGPolynomialKernel
