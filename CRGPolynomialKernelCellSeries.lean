import CRGPolynomialKernelCellGroups

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial Asymptotics
open scoped Topology BigOperators
namespace CRGPolynomialKernel
open CRGExponentialCoefficients CRGExponentialCoefficientGroups CRGPuiseuxMonic
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientScalarAlgebra CRGWatson
open CRGAsymptoticCoefficientRayTail WasowGlobalRayData CRGPuiseuxCoordinates
variable {n : ℕ} {D : CoefficientData n}

theorem Cell.exists_decayingSeries (C : Cell D) :
    ∃B : Fin D.count → Fin (n+1) → PowerSeries ℂ,
      (∀ell,B ell (Fin.last n)=0) ∧
      ∀ell,C.growing ell=false → ∀θ∈C.angles,∀j,
        CompleteExpansion (rayFilter (direction (θ/C.denominator)))
          (fun x=>polynomialKernel (D.fullWeight j ell) (D.phase ell) (D.power ell)
            (originalPoint C.denominator x)) (B ell j) := by
  classical
  have hlow : ∀ell : Fin D.count,∀k : Fin n,∃B : PowerSeries ℂ,
      C.growing ell=false → ∀θ∈C.angles,
        CompleteExpansion (rayFilter (direction (θ/C.denominator)))
          (fun x=>polynomialKernel (D.fullWeight k.castSucc ell) (D.phase ell) (D.power ell)
            (originalPoint C.denominator x)) B := by
    intro ell k
    by_cases hd : C.growing ell=false
    · have hw := D.fullWeight_analytic k.castSucc ell
      obtain ⟨B,hB⟩ := exists_decaying_completeExpansion hw.continuousOn (hw 0 (by simp))
        (D.power_positive ell) (C.root_analytic ell hd) (C.root_zero ell hd)
      refine ⟨B,fun _ θ hθ=>?_⟩
      obtain ⟨hs,⟨c,hc,hcone⟩,hroot⟩ := C.decaying_geometry ell hd θ hθ
      have hl := (rayFilter_le_punctured (direction_ne_zero (θ/C.denominator))).trans nhdsWithin_le_nhds
      have he := hB _ hl (fun x=>-(D.phase ell).eval (originalPoint C.denominator x))
        hs c hc hcone hroot
      simpa only [neg_neg,polynomialKernel,laplaceIntegral] using he
    · exact ⟨0,fun h=>False.elim (hd h)⟩
  choose B hB using hlow
  refine ⟨fun ell j=>Fin.lastCases 0 (B ell) j,?_,?_⟩
  · intro ell
    simp
  · intro ell hd θ hθ j
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last,D.fullWeight_last,polynomialKernel,Pi.zero_apply,
        zero_mul,intervalIntegral.integral_zero]
      simpa only [map_zero] using completeExpansion_const
        ((rayFilter_le_punctured (direction_ne_zero _)).trans nhdsWithin_le_nhds) 0
    | cast j => simpa only [Fin.lastCases_castSucc] using hB ell j hd θ hθ

def Cell.clearing (C : Cell D) (E : MonicGroups D.exponential) : ℕ :=
  ∑q∈C.phaseSet E,∑j : Fin (n+1),C.denominator*(C.polynomial E q j).natDegree

theorem Cell.clearing_bound (C : Cell D) (E : MonicGroups D.exponential)
    (q : Polynomial ℂ) (hq : q∈C.phaseSet E) (j : Fin (n+1)) :
    C.denominator*(C.polynomial E q j).natDegree≤C.clearing E := by
  have hinner : C.denominator*(C.polynomial E q j).natDegree ≤
      ∑j : Fin (n+1),C.denominator*(C.polynomial E q j).natDegree :=
    Finset.single_le_sum (f:=fun j : Fin (n+1)=>C.denominator*(C.polynomial E q j).natDegree)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  exact hinner.trans (Finset.single_le_sum (f:=fun q : Polynomial ℂ=>∑j : Fin (n+1),C.denominator*(C.polynomial E q j).natDegree)
    (fun _ _=>Nat.zero_le _) hq)

theorem Cell.monomialExpansion (C : Cell D) (h : ℕ) (θ : ℝ) :
    CompleteExpansion (rayFilter (direction (θ/C.denominator))) (fun x:ℂ=>x^h)
      (PowerSeries.X^h) := by
  have hl := (rayFilter_le_punctured (direction_ne_zero (θ/C.denominator))).trans nhdsWithin_le_nhds
  simpa only [Polynomial.coe_pow,Polynomial.coe_X,Polynomial.eval_pow,Polynomial.eval_X] using
    CRGAsymptoticCoefficientMatrixTransfer.polynomial_completeExpansion hl (Polynomial.X^h)

def Cell.active (C : Cell D) (E : MonicGroups D.exponential) (q : Polynomial ℂ) : Prop :=
  q=0 ∨ ∃j : Fin (n+1),C.polynomial E q j≠0 ∨ ¬EqOn (C.density q j) 0 (Ioc 0 1)

theorem Cell.exists_component_series (C : Cell D) (E : MonicGroups D.exponential)
    (B : Fin D.count → Fin (n+1) → PowerSeries ℂ)
    (hBtop : ∀ell,B ell (Fin.last n)=0)
    (hB : ∀ell,C.growing ell=false → ∀θ∈C.angles,∀j,
      CompleteExpansion (rayFilter (direction (θ/C.denominator)))
        (fun x=>polynomialKernel (D.fullWeight j ell) (D.phase ell) (D.power ell)
          (originalPoint C.denominator x)) (B ell j))
    (q : Polynomial ℂ) (hq : q∈C.phaseSet E) (j : Fin (n+1)) :
    ∃ A : PowerSeries ℂ,
      ((q=0 ∧ j=Fin.last n) ∨ (q≠0 ∧
        (C.polynomial E q j≠0 ∨ ¬EqOn (C.density q j) 0 (Ioc 0 1))) → A≠0) ∧
      ∀θ∈C.angles,CompleteExpansion (rayFilter (direction (θ/C.denominator)))
        (fun x=>x^(C.clearing E)*C.amplitude E q j x) A := by
  classical
  let h := C.clearing E
  let P := C.polynomial E q j
  let R := clearedPolynomial P C.denominator h
  have hh : C.denominator*P.natDegree≤h := C.clearing_bound E q hq j
  by_cases hq0 : q=0
  · subst q
    let T := ∑ell∈C.decayingIndices,B ell j
    refine ⟨(R:PowerSeries ℂ)+PowerSeries.X^h*T,?_,?_⟩
    · intro hn
      have hj : j=Fin.last n := by
        rcases hn with hn | hn
        · exact hn.2
        · exact False.elim (hn.1 rfl)
      subst j
      have hP : C.polynomial E 0 (Fin.last n)=1 := by
        simp only [Cell.polynomial,if_pos E.zero_mem,E.top,if_true]
      have hT : T=0 := by simp only [T,hBtop,Finset.sum_const_zero]
      have hR : R=Polynomial.X^h := by
        simp only [R,P,hP,clearedPolynomial,Polynomial.natDegree_one,zero_add,
          Finset.sum_range_one,Polynomial.coeff_one_zero,Nat.mul_zero,Nat.sub_zero,
          Polynomial.C_1,one_mul]
      rw [hT,mul_zero,add_zero,hR,Polynomial.coe_pow,Polynomial.coe_X]
      exact pow_ne_zero h PowerSeries.X_ne_zero
    · intro θ hθ
      let l := rayFilter (direction (θ/C.denominator))
      have hl : l≤𝓝 (0:ℂ) := (rayFilter_le_punctured (direction_ne_zero _)).trans nhdsWithin_le_nhds
      have hx : ∀ᶠx in l,x≠0 := (show ∀ᶠx : ℂ in 𝓝[≠] (0:ℂ),x≠0 from self_mem_nhdsWithin).filter_mono
        (rayFilter_le_punctured (direction_ne_zero _))
      have hT : CompleteExpansion l (C.decayingAmplitude j) T := by
        exact completeExpansion_sum C.decayingIndices (fun ell hell=>
          hB ell (Finset.mem_filter.mp hell).2 θ hθ j)
      have hR := CRGAsymptoticCoefficientMatrixTransfer.polynomial_completeExpansion hl R
      have he := completeExpansion_add hR (completeExpansion_mul hl (C.monomialExpansion h θ) hT)
      intro N
      apply (he N).congr' ?_ Filter.EventuallyEq.rfl
      filter_upwards [hx] with x hx
      have hd := C.density_zero C.zero_not_growingPhases j
      simp only [Cell.amplitude,growingGroupAmplitude,hd,laplaceIntegral,Pi.zero_apply,
        zero_mul,intervalIntegral.integral_zero,mul_zero,add_zero,if_true]
      rw [clearedPolynomial_eval hh hx]
      ring
  · by_cases hqg : q∈C.growingPhases
    · have hqd : 0<q.natDegree := by
        simpa only [sub_zero] using distinct_normalized_nonconstant (C.phaseSet_normalized E q hq)
          (by simp : (0:Polynomial ℂ).coeff 0=0) hq0
      obtain ⟨A,hAn,hA⟩ := exists_growingGroup_completeExpansion P q hqd C.positive hh
        (C.density_integrable q j) (C.density_analytic q j)
      refine ⟨A,?_,?_⟩
      · intro hn
        rcases hn with hn | hn
        · exact False.elim (hq0 hn.1)
        · exact hAn hn.2
      · intro θ hθ
        obtain ⟨ell,hell,he⟩ := Finset.mem_image.mp hqg
        have hg := (Finset.mem_filter.mp hell).2
        obtain ⟨hs,c,hc,hcone⟩ := C.growing_geometry ell hg θ hθ
        rw [he] at hs hcone
        have hl := (rayFilter_le_punctured (direction_ne_zero (θ/C.denominator))).trans nhdsWithin_le_nhds
        have hx := (show ∀ᶠx : ℂ in 𝓝[≠] (0:ℂ),x≠0 from self_mem_nhdsWithin).filter_mono (rayFilter_le_punctured (direction_ne_zero (θ/C.denominator)))
        simpa only [Cell.amplitude,if_neg hq0,add_zero] using hA _ hl hx hs c hc hcone
    · refine ⟨(R:PowerSeries ℂ),?_,?_⟩
      · intro hn
        have hPn : P≠0 := by
          rcases hn with hn | hn
          · exact False.elim (hq0 hn.1)
          · rcases hn.2 with hp | hv
            · exact hp
            · exact False.elim (hv (by rw [C.density_zero hqg j]; exact fun _ _=>rfl))
        intro hz
        have hr : R=0 := by
          apply Polynomial.coe_injective
          simpa only [Polynomial.coe_zero] using hz
        exact clearedPolynomial_ne_zero hPn C.positive hh hr
      · intro θ hθ
        have hl := (rayFilter_le_punctured (direction_ne_zero (θ/C.denominator))).trans nhdsWithin_le_nhds
        have hx := (show ∀ᶠx : ℂ in 𝓝[≠] (0:ℂ),x≠0 from self_mem_nhdsWithin).filter_mono (rayFilter_le_punctured (direction_ne_zero (θ/C.denominator)))
        have he := CRGAsymptoticCoefficientMatrixTransfer.polynomial_completeExpansion hl R
        intro N
        apply (he N).congr' ?_ Filter.EventuallyEq.rfl
        filter_upwards [hx] with x hx
        simp only [Cell.amplitude,growingGroupAmplitude,C.density_zero hqg j,
          laplaceIntegral,Pi.zero_apply,zero_mul,intervalIntegral.integral_zero,mul_zero,
          add_zero,if_neg hq0]
        rw [clearedPolynomial_eval hh hx]

#print axioms Cell.exists_decayingSeries
#print axioms Cell.clearing_bound
end CRGPolynomialKernel
