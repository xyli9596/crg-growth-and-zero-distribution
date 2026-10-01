import CRGPolynomialKernelNonvanishing
import CRGPolynomialKernelClearing

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial Asymptotics
open scoped Topology BigOperators
namespace CRGPolynomialKernel
open CRGWatson CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientScalarAlgebra

def growingGroupAmplitude (P Q : Polynomial ℂ) (p : ℕ) (v : ℝ → ℂ) (x : ℂ) : ℂ :=
  P.eval (x^(-(p:ℤ))) + Complex.exp (-Q.eval (x^(-(p:ℤ)))) *
    laplaceIntegral v (fun t=>(t:ℂ)) (Q.eval (x^(-(p:ℤ))))

/-- Every actual grouped growing component, including its exponential-polynomial
multiplier, has one fixed complete cleared series. An actual nonzero component
forces this series to be nonzero through disjoint polynomial and integral heads. -/
theorem exists_growingGroup_completeExpansion (P Q : Polynomial ℂ)
    (hQ : 0<Q.natDegree) {p h : ℕ} (hp : 0<p) (hh : p*P.natDegree ≤ h)
    {v : ℝ → ℂ} (hvi : IntervalIntegrable v MeasureTheory.volume 0 1)
    (hva : AnalyticOnNhd ℝ v (Ioc 0 1)) :
    ∃ A : PowerSeries ℂ, ((P≠0 ∨ ¬EqOn v 0 (Ioc 0 1)) → A≠0) ∧
      ∀ l : Filter ℂ, l≤𝓝 (0:ℂ) → (∀ᶠx in l,x≠0) →
        Tendsto (fun x=>‖Q.eval (x^(-(p:ℤ)))‖) l atTop →
        ∀c : ℝ, 0<c → (∀ᶠx in l,c*‖Q.eval (x^(-(p:ℤ)))‖≤(Q.eval (x^(-(p:ℤ)))).re) →
      CompleteExpansion l (fun x=>x^h*growingGroupAmplitude P Q p v x) A := by
  have hQn : Q≠0 := by intro hz; simp only [hz,Polynomial.natDegree_zero] at hQ; omega
  let g := inversePhase Q p
  have hg := analyticAt_inversePhase hQn hp
  have hg0 := inversePhase_zero hQ hp
  have horder : analyticOrderAt g 0 ≠ ⊤ := by
    rw [inversePhase_analyticOrder hQn hp]
    exact ENat.natCast_ne_top _
  have hsource : ∃ B : PowerSeries ℂ, PowerSeries.constantCoeff B=0 ∧
      (¬EqOn v 0 (Ioc 0 1) → B≠0) ∧
      ∀ l : Filter ℂ,l≤𝓝 (0:ℂ) → ∀s : ℂ → ℂ,
        Tendsto (fun x=>‖s x‖) l atTop → ∀c : ℝ,0<c →
          (∀ᶠx in l,c*‖s x‖≤(s x).re) → (∀ᶠx in l,g x=(s x)⁻¹) →
        CompleteExpansion l (fun x=>Complex.exp (-s x)*laplaceIntegral v (fun t=>(t:ℂ)) (s x)) B := by
    by_cases hvn : EqOn v 0 (Ioc 0 1)
    · refine ⟨0,map_zero _,fun hn=>False.elim (hn hvn),?_⟩
      intro l hl s hs c hc hcone hginv
      simpa only [integral_zero_of_zero_density _ hvn,mul_zero,map_zero] using completeExpansion_const hl 0
    · obtain ⟨B,hBn,hB0,hBe⟩ := exists_nonzero_density_growing_completeExpansion hvi hva hvn hg hg0 horder
      exact ⟨B,hB0,fun _=>hBn,hBe⟩
  obtain ⟨B,hB0,hBn,hBe⟩ := hsource
  let R := clearedPolynomial P p h
  let A : PowerSeries ℂ := (R : PowerSeries ℂ)+PowerSeries.X^h*B
  refine ⟨A,?_,?_⟩
  · intro hn
    apply polynomial_head_tail_nonzero _ _ h
    · intro j hj
      simpa only [Polynomial.coeff_coe] using clearedPolynomial_coeff_above P p h j hj
    · exact cleared_zero_head_coeff hB0 h
    · rcases hn with hPn | hvn
      · exact Or.inl (by
          intro hz
          have hr : R=0 := by
            apply Polynomial.coe_injective
            simpa only [Polynomial.coe_zero] using hz
          exact clearedPolynomial_ne_zero hPn hp hh hr)
      · exact Or.inr (mul_ne_zero (pow_ne_zero h PowerSeries.X_ne_zero) (hBn hvn))
  · intro l hl hx hs c hc hcone
    have hginv : ∀ᶠx in l,g x=(Q.eval (x^(-(p:ℤ))))⁻¹ := by
      filter_upwards [hx] with x hx
      exact inversePhase_eq p hx
    have hI := hBe l hl (fun x=>Q.eval (x^(-(p:ℤ)))) hs c hc hcone hginv
    have hmono : CompleteExpansion l (fun x:ℂ=>x^h) (PowerSeries.X^h) := by
      simpa only [Polynomial.coe_pow,Polynomial.coe_X,Polynomial.eval_pow,Polynomial.eval_X] using
        CRGAsymptoticCoefficientMatrixTransfer.polynomial_completeExpansion hl (Polynomial.X^h)
    have hR := CRGAsymptoticCoefficientMatrixTransfer.polynomial_completeExpansion hl R
    have he := completeExpansion_add hR (completeExpansion_mul hl hmono hI)
    intro N
    apply (he N).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hx] with x hx
    rw [clearedPolynomial_eval hh hx]
    simp only [growingGroupAmplitude]
    ring

#print axioms exists_growingGroup_completeExpansion
end CRGPolynomialKernel
