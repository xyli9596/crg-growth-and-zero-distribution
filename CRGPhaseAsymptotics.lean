import CRGPhaseDirections

/-! Leading radial asymptotics of the actual fixed polynomial phases. -/
set_option autoImplicit false
noncomputable section
open Polynomial Filter Set
open scoped Topology
namespace CRGPhaseAsymptotics
open WasowPhaseOrdering CRGNormalFormGoal

theorem coeff_realPhasePolynomial (P : Polynomial ℂ) (c : ℂ) (n : ℕ) :
    (realPhasePolynomial P c).coeff n = (P.coeff n * c^n).re := by
  classical
  unfold realPhasePolynomial
  rw [finsetSum_coeff]
  simp only [coeff_monomial]
  by_cases h : n ∈ P.support
  · simp [h]
  · simp [h, notMem_support_iff.mp h]

theorem natDegree_realPhasePolynomial_le (P : Polynomial ℂ) (c : ℂ) :
    (realPhasePolynomial P c).natDegree ≤ P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_realPhasePolynomial, coeff_eq_zero_of_natDegree_lt hn]
  simp

theorem realPhasePolynomial_degree (P : Polynomial ℂ) (c : ℂ)
    (h : (P.leadingCoeff*c^P.natDegree).re ≠ 0) :
    (realPhasePolynomial P c).natDegree = P.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_realPhasePolynomial_le P c)
  simpa only [coeff_realPhasePolynomial, coeff_natDegree] using h

theorem realPhasePolynomial_leadingCoeff (P : Polynomial ℂ) (c : ℂ)
    (h : (P.leadingCoeff*c^P.natDegree).re ≠ 0) :
    (realPhasePolynomial P c).leadingCoeff = (P.leadingCoeff*c^P.natDegree).re := by
  rw [leadingCoeff, realPhasePolynomial_degree P c h, coeff_realPhasePolynomial,
    coeff_natDegree]

theorem polynomial_normalized_limit (P : Polynomial ℂ) (c : ℂ)
    (h : (P.leadingCoeff*c^P.natDegree).re ≠ 0) :
    Tendsto (fun r : ℝ => (P.eval ((r:ℂ)*c)).re / r^P.natDegree)
      atTop (𝓝 (P.leadingCoeff*c^P.natDegree).re) := by
  let Q := realPhasePolynomial P c
  have hQ : Q ≠ 0 := by
    intro he
    have hlead := realPhasePolynomial_leadingCoeff P c h
    change Q.leadingCoeff = _ at hlead
    rw [he, leadingCoeff_zero] at hlead
    exact h hlead.symm
  have hd : Q.degree = (X^P.natDegree : Polynomial ℝ).degree := by
    rw [degree_eq_natDegree hQ, degree_X_pow]
    congr 1
    exact realPhasePolynomial_degree P c h
  have hh := Q.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (X^P.natDegree) hd
  simpa only [Q, eval_realPhasePolynomial, eval_pow, eval_X, leadingCoeff_X_pow,
    div_one, realPhasePolynomial_leadingCoeff P c h] using hh

theorem phase_normalized_limit (p : ℕ) (hp : 0<p) (P : Polynomial ℂ)
    (θ : ℝ) (ℓ : Fin p)
    (h : (P.leadingCoeff *
      (Complex.exp (((θ+2*Real.pi*(ℓ:ℝ))/(p:ℝ):ℝ)*Complex.I))^P.natDegree).re ≠ 0) :
    Tendsto (fun r : ℝ => (phaseOnRay p P θ ℓ r).re /
      r^((P.natDegree:ℝ)/(p:ℝ))) atTop
      (𝓝 (P.leadingCoeff *
        (Complex.exp (((θ+2*Real.pi*(ℓ:ℝ))/(p:ℝ):ℝ)*Complex.I))^P.natDegree).re) := by
  have ht := (polynomial_normalized_limit P _ h).comp
    (tendsto_rpow_atTop (one_div_pos.mpr (by exact_mod_cast hp) : 0<1/(p:ℝ)))
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  dsimp [phaseOnRay, rootOnRay]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  congr 1
  ring

#print axioms coeff_realPhasePolynomial
#print axioms natDegree_realPhasePolynomial_le
#print axioms realPhasePolynomial_degree
#print axioms realPhasePolynomial_leadingCoeff
#print axioms polynomial_normalized_limit
#print axioms phase_normalized_limit
end CRGPhaseAsymptotics
