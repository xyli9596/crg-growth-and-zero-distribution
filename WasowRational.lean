import NormalFormGoal
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Rational coefficients on ray tails

All bounds are derived from the actual polynomial numerator and monic
denominator. The polynomial part is independent of the chosen ray.
-/

noncomputable section
open Set Filter Polynomial Asymptotics Bornology
open scoped Topology
open CRGNormalFormGoal

namespace WasowRational

/-- A concrete exterior-disk form of the polynomial degree comparison. -/
theorem polynomial_bound_of_degree_le {P Q : Polynomial ℂ} (hdeg : P.degree ≤ Q.degree) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧
      ∀ z : ℂ, R < ‖z‖ → ‖P.eval z‖ ≤ C * ‖Q.eval z‖ := by
  obtain ⟨C, hC, hb⟩ := (Polynomial.isBigO_cobounded_of_degree_le hdeg).exists_pos
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hb.bound
  exact ⟨C, hC, max 1 R, le_max_left _ _, fun z hz =>
    hR ((le_max_right _ _).trans hz.le)⟩

/-- A nonzero polynomial stays quantitatively away from zero outside one disk. -/
theorem polynomial_denominator_bound (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧
      ∀ z : ℂ, R < ‖z‖ → Q.eval z ≠ 0 ∧ 1 ≤ C * ‖Q.eval z‖ := by
  have hdeg : (1 : Polynomial ℂ).degree ≤ Q.degree := by
    rw [Polynomial.degree_eq_natDegree hQ]
    simp
  obtain ⟨C, hC, R, hR, hb⟩ := polynomial_bound_of_degree_le hdeg
  refine ⟨C, hC, R, hR, fun z hz => ?_⟩
  have hbound : 1 ≤ C * ‖Q.eval z‖ := by simpa using hb z hz
  refine ⟨?_, hbound⟩
  intro hzero
  norm_num [hzero] at hbound

/-- The actual quotient in Euclidean division by the monic denominator. -/
def polynomialPart (a : RatFunc ℂ) : Polynomial ℂ := a.num /ₘ a.denom

def properNumerator (a : RatFunc ℂ) : Polynomial ℂ := a.num %ₘ a.denom

theorem properNumerator_degree_lt (a : RatFunc ℂ) :
    (properNumerator a).degree < a.denom.degree :=
  Polynomial.degree_modByMonic_lt _ (RatFunc.monic_denom a)

/-- This equality is restricted to true nonpoles. -/
theorem eval_sub_polynomialPart (a : RatFunc ℂ) (z : ℂ) (hz : a.denom.eval z ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z a - (polynomialPart a).eval z =
      (properNumerator a).eval z / a.denom.eval z := by
  change a.num.eval z / a.denom.eval z - (polynomialPart a).eval z = _
  have h := congrArg (Polynomial.eval z) (Polynomial.modByMonic_add_div a.num a.denom)
  simp only [Polynomial.eval_add, Polynomial.eval_mul] at h
  dsimp [polynomialPart, properNumerator]
  field_simp
  linear_combination -h

/-- A proper rational quotient has a uniform inverse-radius bound in every
direction. No continuity or decay estimate is assumed. -/
theorem proper_quotient_bound {P Q : Polynomial ℂ} (hQ : Q ≠ 0)
    (hdeg : P.degree < Q.degree) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧ ∀ z : ℂ, R < ‖z‖ →
      Q.eval z ≠ 0 ∧ ‖P.eval z / Q.eval z‖ ≤ C / ‖z‖ := by
  have hmuldeg : (P * Polynomial.X).degree ≤ Q.degree := by
    by_cases hP : P = 0
    · simp [hP]
    rw [Polynomial.degree_eq_natDegree (mul_ne_zero hP Polynomial.X_ne_zero),
      Polynomial.degree_eq_natDegree hQ, Polynomial.natDegree_mul_X hP]
    exact_mod_cast Nat.succ_le_of_lt (Polynomial.natDegree_lt_natDegree hP hdeg)
  obtain ⟨C, hC, R, hR, hb⟩ := polynomial_bound_of_degree_le hmuldeg
  obtain ⟨D, _, S, hS, hden⟩ := polynomial_denominator_bound Q hQ
  refine ⟨C, hC, max R S, hR.trans (le_max_left _ _), fun z hz => ?_⟩
  have hRz : R < ‖z‖ := (le_max_left _ _).trans_lt hz
  have hSz : S < ‖z‖ := (le_max_right _ _).trans_lt hz
  have hzn : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) (hR.trans hRz.le)
  have hQz := (hden z hSz).1
  have hbound := hb z hRz
  rw [Polynomial.eval_mul, Polynomial.eval_X, norm_mul] at hbound
  refine ⟨hQz, ?_⟩
  rw [norm_div]
  apply (div_le_div_iff₀ (norm_pos_iff.mpr hQz) hzn).mpr
  nlinarith [hbound]

/-- The polynomial part is chosen once; its error is `O(1/‖z‖)` uniformly
outside one disk, and the same disk excludes every pole. -/
theorem exists_polynomial_part_tail (a : RatFunc ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧ ∀ z : ℂ, R < ‖z‖ →
      a.denom.eval z ≠ 0 ∧
      ‖RatFunc.eval (RingHom.id ℂ) z a - (polynomialPart a).eval z‖ ≤ C / ‖z‖ := by
  obtain ⟨C, hC, R, hR, hb⟩ := proper_quotient_bound (RatFunc.denom_ne_zero a)
    (properNumerator_degree_lt a)
  refine ⟨C, hC, R, hR, fun z hz => ?_⟩
  have hg := hb z hz
  exact ⟨hg.1, by rw [eval_sub_polynomialPart a z hg.1]; exact hg.2⟩

/-- The ray in the normal-form specification has exactly its positive radius. -/
theorem norm_ray (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) : ‖ray θ r‖ = r := by
  simp [ray, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
    Real.norm_of_nonneg hr]

/-- The actual proper rational part, including the ray's derivative factor. -/
def residualOnRay (a : RatFunc ℂ) (θ r : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I) *
    ((properNumerator a).eval (ray θ r) / a.denom.eval (ray θ r))

/-- One pair of constants works for every ray. The proper remainder is
continuous on the closed tail, and the polynomial part is fixed independently
of the angle. -/
theorem exists_ray_polynomial_part (a : RatFunc ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 1 ≤ R ∧ ∀ θ : ℝ,
      ContinuousOn (residualOnRay a θ) (Ici R) ∧
      ∀ r : ℝ, R ≤ r → a.denom.eval (ray θ r) ≠ 0 ∧
        (Complex.exp ((θ : ℂ) * Complex.I) * RatFunc.eval (RingHom.id ℂ) (ray θ r) a -
          Complex.exp ((θ : ℂ) * Complex.I) * (polynomialPart a).eval (ray θ r) =
            residualOnRay a θ r) ∧ ‖residualOnRay a θ r‖ ≤ C / r := by
  obtain ⟨C, hC, S, hS, hb⟩ := exists_polynomial_part_tail a
  let R := S + 1
  have hR : 1 ≤ R := by dsimp [R]; linarith
  have htail (θ r : ℝ) (hr : R ≤ r) : S < ‖ray θ r‖ := by
    rw [norm_ray θ (by linarith)]
    dsimp [R] at hr
    linarith
  have hden (θ r : ℝ) (hr : R ≤ r) : a.denom.eval (ray θ r) ≠ 0 :=
    (hb _ (htail θ r hr)).1
  refine ⟨C, hC, R, hR, fun θ => ⟨?_, ?_⟩⟩
  · have hnum : Continuous (fun r : ℝ => (properNumerator a).eval (ray θ r)) := by
      dsimp [ray]
      fun_prop
    have hdenCont : Continuous (fun r : ℝ => a.denom.eval (ray θ r)) := by
      dsimp [ray]
      fun_prop
    exact continuousOn_const.mul (hnum.continuousOn.div hdenCont.continuousOn
      (fun r hr => hden θ r hr))
  · intro r hr
    have hd := hden θ r hr
    refine ⟨hd, ?_, ?_⟩
    · rw [← mul_sub, eval_sub_polynomialPart a _ hd]
      rfl
    · have hbound := (hb _ (htail θ r hr)).2
      rw [eval_sub_polynomialPart a _ hd, norm_ray θ (by linarith)] at hbound
      simpa only [residualOnRay, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul] using hbound

#print axioms polynomial_bound_of_degree_le
#print axioms polynomial_denominator_bound
#print axioms properNumerator_degree_lt
#print axioms eval_sub_polynomialPart
#print axioms proper_quotient_bound
#print axioms exists_polynomial_part_tail
#print axioms norm_ray
#print axioms exists_ray_polynomial_part

end WasowRational
