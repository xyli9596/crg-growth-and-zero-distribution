import WasowActualTruncation
import WasowRational
import WasowGaugeAssembly
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Analytic.Polynomial

/-! Actual analytic inverse-variable coefficients of every rational system.
A common integer order is chosen from the genuine numerators. Reversal of the
nonzero denominators gives an analytic extension at zero, before any ray is
chosen. No Taylor expansion of the original rational matrix is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace WasowRationalAtInfinity
open Polynomial CRGNormalFormGoal

/-- A nonzero denominator has a nonzero reversed value at the origin. -/
theorem reverse_denom_zero (f : RatFunc ℂ) : f.denom.reverse.eval 0 ≠ 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
  exact Polynomial.leadingCoeff_ne_zero.mpr (RatFunc.denom_ne_zero f)

/-- The exact reversal identity, restricted only to nonzero inverse variable. -/
theorem eval_inv (P : Polynomial ℂ) {t : ℂ} (ht : t ≠ 0) :
    P.eval t⁻¹ = P.reverse.eval t / t ^ P.natDegree := by
  let : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht)
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) t⁻¹ P
  simpa only [invOf_eq_inv, inv_inv, Polynomial.eval₂_id, inv_pow,
    div_eq_mul_inv] using h.symm

/-- Genuine analytic extension of `t^d f(1/t)`, for an adequate integer d. -/
def scalarCoefficient (d : ℕ) (f : RatFunc ℂ) (t : ℂ) : ℂ :=
  t ^ (d + f.denom.natDegree - f.num.natDegree) *
    f.num.reverse.eval t / f.denom.reverse.eval t

theorem scalarCoefficient_analytic (d : ℕ) (f : RatFunc ℂ) :
    AnalyticAt ℂ (scalarCoefficient d f) 0 := by
  have hp (P : Polynomial ℂ) : AnalyticAt ℂ (fun z => P.eval z) 0 := by
    simpa using (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).aeval_polynomial P
  exact ((analyticAt_id.pow _).mul (hp _)).div (hp _) (reverse_denom_zero f)

theorem scalarCoefficient_eq (d : ℕ) (f : RatFunc ℂ)
    (hd : f.num.natDegree ≤ d) {t : ℂ} (ht : t ≠ 0) :
    scalarCoefficient d f t = t ^ d * RatFunc.eval (RingHom.id ℂ) t⁻¹ f := by
  change _ = t ^ d * (f.num.eval t⁻¹ / f.denom.eval t⁻¹)
  rw [eval_inv f.num ht, eval_inv f.denom ht]
  unfold scalarCoefficient
  by_cases hQ : f.denom.reverse.eval t = 0
  · simp [hQ]
  · have hn : t ^ f.num.natDegree ≠ 0 := pow_ne_zero _ ht
    have hD : t ^ f.denom.natDegree ≠ 0 := pow_ne_zero _ ht
    field_simp
    have he : d + f.denom.natDegree - f.num.natDegree + f.num.natDegree =
        d + f.denom.natDegree := by omega
    calc
      _ = f.num.reverse.eval t * (t ^ (d + f.denom.natDegree - f.num.natDegree) * t ^ f.num.natDegree) := by ring
      _ = _ := by rw [← pow_add, he, pow_add, mul_assoc]

/-- One angle-independent order for all matrix entries. -/
def order {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) : ℕ :=
  ∑ i, ∑ j, (A i j).num.natDegree

theorem numerator_degree_le_order {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (i j : Fin m) :
    (A i j).num.natDegree ≤ order A := by
  have hj : (A i j).num.natDegree ≤ ∑ j : Fin m, (A i j).num.natDegree :=
    Finset.single_le_sum (f := fun j : Fin m => (A i j).num.natDegree) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hi : (∑ j : Fin m, (A i j).num.natDegree) ≤ order A :=
    Finset.single_le_sum (f := fun i : Fin m => ∑ j : Fin m, (A i j).num.natDegree) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact hj.trans hi

def coefficient {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (t : ℂ) :
    Matrix (Fin m) (Fin m) ℂ := fun i j => scalarCoefficient (order A) (A i j) t

/-- Analyticity is proved in the actual matrix operator norm via a finite
sum of scalar analytic functions times constant coordinate matrices. -/
theorem coefficient_analytic {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) :
    AnalyticAt ℂ (coefficient A) 0 := by
  have he : coefficient A = fun t => ∑ i : Fin m, ∑ j : Fin m,
      scalarCoefficient (order A) (A i j) t • Matrix.single i j (1 : ℂ) := by
    funext t
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    simp [coefficient, ite_and]
  rw [he]
  apply Finset.analyticAt_fun_sum
  intro i _
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (scalarCoefficient_analytic _ _).smul analyticAt_const

theorem coefficient_eq {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    {t : ℂ} (ht : t ≠ 0) :
    coefficient A t = t ^ order A • A.map (RatFunc.eval (RingHom.id ℂ) t⁻¹) := by
  ext i j
  exact scalarCoefficient_eq _ _ (numerator_degree_le_order A i j) ht

/-- The actual Taylor series and its coefficient identity are constructed
from rationality and the analytic extension, with no series premise. -/
theorem exists_formal_expansion {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) :
    ∃ (s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ))
      (F : PowerSeries (Matrix (Fin m) (Fin m) ℂ)),
      HasFPowerSeriesAt (coefficient A) s 0 ∧
      (∀ n, s.coeff n = PowerSeries.coeff n F) := by
  obtain ⟨s, hs⟩ := coefficient_analytic A
  exact ⟨s, PowerSeries.mk (fun n => s.coeff n), hs,
    fun n => (PowerSeries.coeff_mk n _).symm⟩

#print axioms reverse_denom_zero
#print axioms eval_inv
#print axioms scalarCoefficient_analytic
#print axioms scalarCoefficient_eq
#print axioms numerator_degree_le_order
#print axioms coefficient_analytic
#print axioms coefficient_eq
#print axioms exists_formal_expansion

/-- Rotation of the already fixed inverse-variable coefficient. The angle
does not change the order or the original complex analytic germ. -/
def rayAnalytic {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ)
    (t : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I) ^ (order A + 1) •
    coefficient A ((Complex.exp ((θ : ℂ) * Complex.I))⁻¹ * t)

theorem rayAnalytic_analytic {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ) :
    AnalyticAt ℂ (rayAnalytic A θ) 0 := by
  have hf : AnalyticAt ℂ (fun t : ℂ => (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ * t) 0 :=
    analyticAt_const.mul analyticAt_id
  have hc := (coefficient_analytic A).comp_of_eq hf (by simp)
  have hu : AnalyticAt ℂ (fun _ : ℂ => Complex.exp ((θ : ℂ) * Complex.I) ^ (order A + 1)) 0 :=
    analyticAt_const
  exact hu.fun_smul hc

/-- Exact identification with the original rational ODE on the ray. -/
theorem coefficientOnRay_eq {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ)
    {r : ℝ} (hr : 0 < r) :
    coefficientOnRay A θ r =
      WasowGaugeAssembly.rayCoefficient (rayAnalytic A θ) (order A + 1) r := by
  let u : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hu : u ≠ 0 := Complex.exp_ne_zero _
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have ht : u⁻¹ * (r : ℂ)⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hu) (inv_ne_zero hr')
  unfold WasowGaugeAssembly.rayCoefficient rayAnalytic
  simp only [Nat.add_sub_cancel]
  change _ = (r : ℂ) ^ order A • (u ^ (order A + 1) • coefficient A (u⁻¹ * (r : ℂ)⁻¹))
  rw [coefficient_eq A ht]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, mul_inv_rev, inv_inv]
  change u * RatFunc.eval (RingHom.id ℂ) ((r : ℂ) * u) (A i j) = _
  rw [mul_pow, inv_pow, inv_pow, pow_succ]
  field_simp

/-- Every rational matrix automatically supplies all initial analytic-series
premises used by the finite-gauge remainder theorem. -/
theorem exists_ray_expansion {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ) :
    ∃ (s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ))
      (F : PowerSeries (Matrix (Fin m) (Fin m) ℂ)),
      HasFPowerSeriesAt (rayAnalytic A θ) s 0 ∧
      (∀ n, s.coeff n = PowerSeries.coeff n F) ∧
      ∀ r > 0, coefficientOnRay A θ r =
        WasowGaugeAssembly.rayCoefficient (rayAnalytic A θ) (order A + 1) r := by
  obtain ⟨s, hs⟩ := rayAnalytic_analytic A θ
  exact ⟨s, PowerSeries.mk (fun n => s.coeff n), hs,
    fun n => (PowerSeries.coeff_mk n _).symm, fun r hr => coefficientOnRay_eq A θ hr⟩

#print axioms rayAnalytic_analytic
#print axioms coefficientOnRay_eq
#print axioms exists_ray_expansion
end WasowRationalAtInfinity
