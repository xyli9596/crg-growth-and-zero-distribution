import CRGPolynomialKernelCancellation
import CRGPolynomialKernelDensity
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace CRGPolynomialKernel

/-- A polynomial head and a strictly negative-power tail have disjoint
coefficient support after clearing a common pole. -/
theorem polynomial_head_tail_zero_iff (P T : PowerSeries ℂ) (h : ℕ)
    (hP : ∀ j : ℕ, h < j → PowerSeries.coeff j P = 0)
    (hT : ∀ j : ℕ, j ≤ h → PowerSeries.coeff j T = 0) :
    P + T = 0 ↔ P = 0 ∧ T = 0 := by
  constructor
  · intro hsum
    have hcoeff : ∀ j : ℕ, PowerSeries.coeff j P + PowerSeries.coeff j T = 0 := fun j => by
      simpa only [map_add, map_zero] using congrArg (PowerSeries.coeff j) hsum
    have hpzero : P = 0 := by
      apply PowerSeries.ext
      intro j
      simp only [map_zero]
      by_cases hj : j ≤ h
      · simpa only [hT j hj, add_zero] using hcoeff j
      · exact hP j (Nat.lt_of_not_ge hj)
    have htzero : T = 0 := by
      rw [hpzero, zero_add] at hsum
      exact hsum
    exact ⟨hpzero, htzero⟩
  · rintro ⟨rfl, rfl⟩
    simp

theorem polynomial_head_tail_nonzero (P T : PowerSeries ℂ) (h : ℕ)
    (hP : ∀ j : ℕ, h < j → PowerSeries.coeff j P = 0)
    (hT : ∀ j : ℕ, j ≤ h → PowerSeries.coeff j T = 0)
    (hne : P ≠ 0 ∨ T ≠ 0) : P + T ≠ 0 := by
  intro hz
  exact hne.elim (fun hp => hp ((polynomial_head_tail_zero_iff P T h hP hT).mp hz).1)
    (fun ht => ht ((polynomial_head_tail_zero_iff P T h hP hT).mp hz).2)

/-- Finite grouping of actual integrable densities commutes with the integral. -/
theorem laplaceIntegral_finset_sum {ι : Type*} (S : Finset ι)
    (v : ι → ℝ → ℂ) (lam : ℂ)
    (hv : ∀ i ∈ S, IntervalIntegrable (v i) volume 0 1) :
    laplaceIntegral (fun u => ∑ i ∈ S, v i u) (fun u => (u : ℂ)) lam =
      ∑ i ∈ S, laplaceIntegral (v i) (fun u => (u : ℂ)) lam := by
  unfold laplaceIntegral
  simp_rw [Finset.sum_mul]
  apply intervalIntegral.integral_finsetSum
  intro i hi
  exact (hv i hi).mul_continuousOn (by fun_prop)

/-- Absorbing constant phase differences and adding the corresponding densities
is an equality of the actual kernels, not a formal grouping convention. -/
theorem group_constant_shifted_integrals {ι : Type*} (S : Finset ι)
    (v : ι → ℝ → ℂ) (c : ι → ℂ) (lam : ℂ)
    (hv : ∀ i ∈ S, IntervalIntegrable (v i) volume 0 1) :
    (∑ i ∈ S, laplaceIntegral (v i) (fun u => (u : ℂ)) (lam + c i)) =
      laplaceIntegral (fun u => ∑ i ∈ S, v i u * Complex.exp (c i * (u : ℂ)))
        (fun u => (u : ℂ)) lam := by
  rw [laplaceIntegral_finset_sum S _ lam (fun i hi =>
    (hv i hi).mul_continuousOn (by fun_prop))]
  apply Finset.sum_congr rfl
  intro i _
  exact laplaceIntegral_add_parameter (v i) (fun u => (u : ℂ)) lam (c i)

#print axioms polynomial_head_tail_zero_iff
#print axioms polynomial_head_tail_nonzero
#print axioms group_constant_shifted_integrals
end CRGPolynomialKernel
