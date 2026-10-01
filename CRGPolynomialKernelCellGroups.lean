import CRGPolynomialKernelCells
import CRGPolynomialKernelMonic
import CRGPolynomialKernelGrowingGroup
import CRGExponentialCoefficientGroups

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial Asymptotics
open scoped Topology BigOperators
namespace CRGPolynomialKernel
open CRGExponentialCoefficients CRGExponentialCoefficientGroups CRGPuiseuxMonic
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientScalarAlgebra
open CRGAsymptoticCoefficientRayTail WasowGlobalRayData CRGPuiseuxCoordinates
variable {n : ℕ} {D : CoefficientData n}

def Cell.growingIndices (C : Cell D) : Finset (Fin D.count) :=
  Finset.univ.filter (fun ell=>C.growing ell=true)

def Cell.decayingIndices (C : Cell D) : Finset (Fin D.count) :=
  Finset.univ.filter (fun ell=>C.growing ell=false)

def Cell.growingPhases (C : Cell D) : Finset (Polynomial ℂ) :=
  C.growingIndices.image (fun ell=>normalizedExponent (D.phase ell))

def Cell.phaseSet (C : Cell D) (E : MonicGroups D.exponential) : Finset (Polynomial ℂ) :=
  E.exponents ∪ C.growingPhases

def Cell.polynomial (_C : Cell D) (E : MonicGroups D.exponential)
    (q : Polynomial ℂ) (j : Fin (n+1)) : Polynomial ℂ :=
  if q∈E.exponents then E.coeff q j else 0

def Cell.densityIndices (C : Cell D) (q : Polynomial ℂ) : Finset (Fin D.count) :=
  C.growingIndices.filter (fun ell=>normalizedExponent (D.phase ell)=q)

def Cell.density (C : Cell D) (q : Polynomial ℂ) (j : Fin (n+1)) : ℝ → ℂ :=
  groupedPowerDensity (C.densityIndices q) (D.fullWeight j) D.power D.phase

def Cell.decayingAmplitude (C : Cell D) (j : Fin (n+1)) (x : ℂ) : ℂ :=
  ∑ell∈C.decayingIndices,polynomialKernel (D.fullWeight j ell) (D.phase ell)
    (D.power ell) (originalPoint C.denominator x)

def Cell.amplitude (C : Cell D) (E : MonicGroups D.exponential)
    (q : Polynomial ℂ) (j : Fin (n+1)) (x : ℂ) : ℂ :=
  growingGroupAmplitude (C.polynomial E q j) q C.denominator (C.density q j) x +
    if q=0 then C.decayingAmplitude j x else 0

theorem Cell.zero_not_growingPhases (C : Cell D) : 0∉C.growingPhases := by
  intro h0
  obtain ⟨ell,_,he⟩ := Finset.mem_image.mp h0
  exact normalizedExponent_nonzero (D.phase_nonconstant ell) he

theorem Cell.densityIndices_empty (C : Cell D) {q : Polynomial ℂ} (hq : q∉C.growingPhases) :
    C.densityIndices q=∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro ell hell
  have he := Finset.mem_filter.mp hell
  exact hq (Finset.mem_image.mpr ⟨ell,he.1,he.2⟩)

theorem Cell.density_zero (C : Cell D) {q : Polynomial ℂ} (hq : q∉C.growingPhases)
    (j : Fin (n+1)) : C.density q j=0 := by
  funext u
  simp only [Cell.density,Cell.densityIndices_empty C hq,groupedPowerDensity,Finset.sum_empty,
    Pi.zero_apply]

theorem Cell.density_integrable (C : Cell D) (q : Polynomial ℂ) (j : Fin (n+1)) :
    IntervalIntegrable (C.density q j) MeasureTheory.volume 0 1 :=
  intervalIntegrable_groupedPowerDensity _ _ _ _
    (fun ell _=>(D.fullWeight_analytic j ell).continuousOn) (fun ell _=>D.power_positive ell)

theorem Cell.density_analytic (C : Cell D) (q : Polynomial ℂ) (j : Fin (n+1)) :
    AnalyticOnNhd ℝ (C.density q j) (Ioc 0 1) :=
  analyticOnNhd_groupedPowerDensity _ _ _ _
    (fun ell _=>D.fullWeight_analytic j ell) (fun ell _=>D.power_positive ell)

theorem Cell.growing_kernel_group (C : Cell D) (q : Polynomial ℂ) (j : Fin (n+1)) (z : ℂ) :
    (∑ell∈C.densityIndices q,polynomialKernel (D.fullWeight j ell) (D.phase ell) (D.power ell) z) =
      laplaceIntegral (C.density q j) (fun u=>(u:ℂ)) (q.eval z) := by
  exact polynomialKernel_grouped _ _ _ _ _
    (fun ell _=>(D.fullWeight_analytic j ell).continuousOn) (fun ell _=>D.power_positive ell)
    (fun ell hell=>(Finset.mem_filter.mp hell).2) z

theorem Cell.growing_kernel_sum (C : Cell D) (j : Fin (n+1)) (z : ℂ) :
    (∑ell∈C.growingIndices,polynomialKernel (D.fullWeight j ell) (D.phase ell) (D.power ell) z) =
      ∑q∈C.growingPhases,laplaceIntegral (C.density q j) (fun u=>(u:ℂ)) (q.eval z) := by
  rw [←Finset.sum_fiberwise_of_maps_to (s:=C.growingIndices) (t:=C.growingPhases)
    (g:=fun ell=>normalizedExponent (D.phase ell))
    (fun ell hell=>Finset.mem_image.mpr ⟨ell,hell,rfl⟩)
    (fun ell=>polynomialKernel (D.fullWeight j ell) (D.phase ell) (D.power ell) z)]
  exact Finset.sum_congr rfl (fun q _=>C.growing_kernel_group q j z)

theorem Cell.phaseSet_zero_mem (C : Cell D) (E : MonicGroups D.exponential) :
    0∈C.phaseSet E := Finset.mem_union_left _ E.zero_mem

theorem Cell.phaseSet_normalized (C : Cell D) (E : MonicGroups D.exponential)
    (q : Polynomial ℂ) (hq : q∈C.phaseSet E) : q.coeff 0=0 := by
  rcases Finset.mem_union.mp hq with hq | hq
  · exact E.normalized q hq
  · obtain ⟨ell,_,rfl⟩ := Finset.mem_image.mp hq
    exact normalizedExponent_zero _

theorem Cell.polynomial_sum (C : Cell D) (E : MonicGroups D.exponential)
    (j : Fin (n+1)) (z : ℂ) :
    (∑q∈C.phaseSet E,Complex.exp (q.eval z)*(C.polynomial E q j).eval z) =
      fullCoefficient D.exponential j z := by
  rw [E.representation]
  have he : (∑q∈E.exponents,Complex.exp (q.eval z)*(C.polynomial E q j).eval z)=
      ∑q∈E.exponents,Complex.exp (q.eval z)*(E.coeff q j).eval z :=
    Finset.sum_congr rfl (fun q hq=>by simp only [Cell.polynomial,if_pos hq])
  rw [←he]
  symm
  apply Finset.sum_subset (Finset.subset_union_left)
  intro q _hq hnq
  simp only [Cell.polynomial,if_neg hnq,Polynomial.eval_zero,mul_zero]

theorem Cell.growing_kernel_sum_phaseSet (C : Cell D) (E : MonicGroups D.exponential)
    (j : Fin (n+1)) (z : ℂ) :
    (∑q∈C.phaseSet E,laplaceIntegral (C.density q j) (fun u=>(u:ℂ)) (q.eval z)) =
      ∑ell∈C.growingIndices,polynomialKernel (D.fullWeight j ell) (D.phase ell) (D.power ell) z := by
  rw [Cell.growing_kernel_sum]
  symm
  apply Finset.sum_subset (Finset.subset_union_right)
  intro q _hq hnq
  simp only [C.density_zero hnq j,laplaceIntegral,Pi.zero_apply,zero_mul,
    intervalIntegral.integral_zero]

theorem Cell.amplitude_representation (C : Cell D) (E : MonicGroups D.exponential)
    (j : Fin (n+1)) (x : ℂ) :
    fullCoefficient D.coefficient j (originalPoint C.denominator x) =
      ∑q∈C.phaseSet E,C.amplitude E q j x*Complex.exp (q.eval (originalPoint C.denominator x)) := by
  classical
  let z := originalPoint C.denominator x
  have hpoint : ∀q : Polynomial ℂ,C.amplitude E q j x*Complex.exp (q.eval z)=
      Complex.exp (q.eval z)*(C.polynomial E q j).eval z +
        laplaceIntegral (C.density q j) (fun u=>(u:ℂ)) (q.eval z) +
          if q=0 then C.decayingAmplitude j x else 0 := by
    intro q
    unfold Cell.amplitude growingGroupAmplitude
    have he : Complex.exp (-(q.eval z))*Complex.exp (q.eval z)=1 := by
      rw [←Complex.exp_add,neg_add_cancel,Complex.exp_zero]
    dsimp only [z,originalPoint] at he ⊢
    by_cases hq : q=0
    · subst q
      simp only [Polynomial.eval_zero,neg_zero,Complex.exp_zero,if_true,one_mul,mul_one]
    · simp only [if_neg hq,add_zero]
      calc
        _ = Complex.exp (q.eval z)*(C.polynomial E q j).eval z +
          (Complex.exp (-(q.eval z))*Complex.exp (q.eval z))*
            laplaceIntegral (C.density q j) (fun u=>(u:ℂ)) (q.eval z) := by dsimp only [z,originalPoint]; ring
        _ = _ := by dsimp only [z,originalPoint]; rw [he,one_mul]
  change fullCoefficient D.coefficient j z =
    ∑q∈C.phaseSet E,C.amplitude E q j x*Complex.exp (q.eval z)
  simp_rw [hpoint,Finset.sum_add_distrib]
  rw [C.polynomial_sum E j z,C.growing_kernel_sum_phaseSet E j z]
  simp only [Finset.sum_ite_eq',C.phaseSet_zero_mem E,if_pos True.intro]
  rw [D.full_coefficient_representation]
  have hs := Finset.sum_filter_add_sum_filter_not (s:=Finset.univ)
    (p:=fun ell : Fin D.count=>C.growing ell=true)
    (f:=fun ell=>polynomialKernel (D.fullWeight j ell) (D.phase ell) (D.power ell) z)
  simpa only [Cell.growingIndices,Cell.decayingIndices,Cell.decayingAmplitude,
    Bool.not_eq_true,add_assoc] using
      congrArg (fun y=>fullCoefficient D.exponential j z+y) hs.symm

#print axioms Cell.density_integrable
#print axioms Cell.growing_kernel_sum
end CRGPolynomialKernel
