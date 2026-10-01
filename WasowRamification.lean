import WasowShearing
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Exact power ramification of a differential system

The actual chain rule supplies the new coefficient under `x=t^p`. This module
also records the rational rank arithmetic of §19.3. It does not assume or
claim termination of the general shearing sequence.
-/
noncomputable section
open Matrix Set Filter
open scoped Topology BigOperators
namespace WasowRamification

/-- The exact coefficient after the power change of independent variable. -/
def coefficient {m : ℕ} (p : ℕ) (A : ℂ → Matrix (Fin m) (Fin m) ℂ) (t : ℂ) :
    Matrix (Fin m) (Fin m) ℂ := (p * t ^ (p-1)) • A (t^p)

/-- Ramification of an actual complex-parameter solution by the chain rule. -/
theorem solution_hasDerivAt {m : ℕ} (p : ℕ)
    (A : ℂ → Matrix (Fin m) (Fin m) ℂ) (y : ℂ → Fin m → ℂ) (t : ℂ)
    (hy : HasDerivAt y ((A (t^p)).mulVec (y (t^p))) (t^p)) :
    HasDerivAt (fun s => y (s^p)) ((coefficient p A t).mulVec (y (t^p))) t := by
  have hd := hy.scomp t (hasDerivAt_pow p t)
  convert hd using 1 <;> try rfl
  exact Matrix.smul_mulVec _ _ _

/-- The same exact pullback on a real ray parameter, without any implicit
complex differentiation of the ray function. -/
theorem real_solution_hasDerivAt {m : ℕ} (p : ℕ)
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (y : ℝ → Fin m → ℂ) (t : ℝ)
    (hy : HasDerivAt y ((A (t^p)).mulVec (y (t^p))) (t^p)) :
    HasDerivAt (fun s => y (s^p))
      ((((p : ℂ) * (t : ℂ) ^ (p-1)) • A (t^p)).mulVec (y (t^p))) t := by
  have hd := hy.scomp t (hasDerivAt_pow p t)
  convert hd using 1 <;> try rfl
  rw [Matrix.smul_mulVec]
  ext i
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.ofReal_pow]

/-- A monomial coefficient transforms with the exact ramified integer exponent. -/
theorem coefficient_monomial {m : ℕ} (p : ℕ) (n : ℤ)
    (B : Matrix (Fin m) (Fin m) ℂ) {t : ℂ} (ht : t ≠ 0) (hp : 0 < p) :
    coefficient p (fun x => x ^ n • B) t =
      ((p : ℂ) * t ^ ((p : ℤ) * (n+1)-1)) • B := by
  unfold coefficient
  rw [smul_smul]
  have hp1 : ((p-1 : ℕ) : ℤ) = (p : ℤ)-1 := by omega
  have hz : t ^ (p-1) * (t ^ p) ^ n = t ^ ((p : ℤ)*(n+1)-1) := by
    rw [← zpow_natCast t (p-1), ← zpow_natCast t p, ← zpow_mul,
      ← zpow_add₀ ht, hp1]
    congr 1
    ring
  rw [mul_assoc, hz]

/-- Clearing a rational slope denominator makes the new rank integral.
This is the exact arithmetic `h=p*(q+1-σ)-1` from §19.3. -/
theorem ramified_rank (q : ℤ) (a : ℤ) (p : ℕ) (hp : 0 < p) :
    (p : ℚ) * ((q : ℚ)+1-(a : ℚ)/(p : ℚ))-1 =
      ((p : ℤ)*(q+1)-a-1 : ℤ) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

/-- An integral positive shearing slope strictly reduces the unramified rank.
No conclusion about a sequence of nonintegral shears is hidden here. -/
theorem integral_slope_rank_decreases (q s : ℤ) (hs : 0 < s) : q-s < q := by omega


/-- A nonconstant power substitution never annihilates a nonzero polynomial. -/
theorem polynomial_comp_pow_ne_zero (p : ℕ) (hp : 0 < p)
    (P : Polynomial ℂ) (hP : P ≠ 0) : P.comp (Polynomial.X ^ p) ≠ 0 := by
  intro hz
  rcases Polynomial.comp_eq_zero_iff.mp hz with h | ⟨_, h⟩
  · exact hP h
  · have hd := congrArg Polynomial.natDegree h
    simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_C] at hd
    omega

theorem powerSubstitution_preserves_nonZeroDivisors (p : ℕ) (hp : 0 < p) :
    nonZeroDivisors (Polynomial ℂ) ≤
      (nonZeroDivisors (Polynomial ℂ)).comap (Polynomial.compRingHom (Polynomial.X ^ p)) := by
  intro P hP
  change (Polynomial.compRingHom (Polynomial.X ^ p)) P ∈ nonZeroDivisors (Polynomial ℂ)
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  exact polynomial_comp_pow_ne_zero p hp P (mem_nonZeroDivisors_iff_ne_zero.mp hP)

/-- The power substitution as a genuine endomorphism of the rational function field. -/
def powerSubstitution (p : ℕ) (hp : 0 < p) : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.mapRingHom (Polynomial.compRingHom (Polynomial.X ^ p))
    (powerSubstitution_preserves_nonZeroDivisors p hp)

/-- Rational substitution is literally numerator and denominator substitution. -/
theorem powerSubstitution_div (p : ℕ) (hp : 0 < p) (P Q : Polynomial ℂ) :
    powerSubstitution p hp (algebraMap (Polynomial ℂ) (RatFunc ℂ) P /
      algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.comp (Polynomial.X ^ p)) /
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (Q.comp (Polynomial.X ^ p)) := by
  exact RatFunc.map_apply_div _ (powerSubstitution_preserves_nonZeroDivisors p hp) P Q

/-- The exact ramified coefficient remains an actual rational matrix. -/
def rationalCoefficient {m : ℕ} (p : ℕ) (hp : 0 < p)
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) : Matrix (Fin m) (Fin m) (RatFunc ℂ) :=
  ((p : RatFunc ℂ) * (RatFunc.X : RatFunc ℂ) ^ (p-1)) • A.map (powerSubstitution p hp)

/-- Every positive rational slope has an explicit positive integral ramification. -/
theorem exists_integral_ramification (σ : ℚ) (hσ : 0 < σ) :
    ∃ p : ℕ, 0 < p ∧ ∃ a : ℤ, 0 < a ∧ (p : ℚ) * σ = a := by
  refine ⟨σ.den, σ.den_pos, σ.num, ?_, ?_⟩
  · exact Rat.num_pos.mpr hσ
  · have hd : (σ.den : ℚ) ≠ 0 := by exact_mod_cast σ.den_ne_zero
    have hh := σ.num_div_den
    calc
      (σ.den : ℚ) * σ = σ.den * (σ.num / σ.den) := by rw [hh]
      _ = σ.num := by field_simp


/-- Evaluating a displayed rational fraction is legitimate at every nonpole
of its displayed denominator, even when the fraction is not reduced. -/
theorem eval_polynomial_fraction (P Q : Polynomial ℂ) (z : ℂ) (hQ : Q.eval z ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) =
      P.eval z / Q.eval z := by
  let f : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) P /
    algebraMap (Polynomial ℂ) (RatFunc ℂ) Q
  have hQ0 : Q ≠ 0 := by intro h; exact hQ (by simp [h])
  have hden : f.denom.eval z ≠ 0 := by
    intro hz
    exact hQ (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_div_dvd P Q) hz)
  have hpoly : f.num * Q = P * f.denom := (RatFunc.num_mul_eq_mul_denom_iff hQ0).mpr rfl
  have he := congrArg (Polynomial.eval z) hpoly
  change f.num.eval z / f.denom.eval z = _
  apply (div_eq_div_iff hden hQ).mpr
  simpa only [Polynomial.eval_mul] using he

/-- The rational endomorphism agrees with the actual analytic substitution
at genuine nonpoles; totalized rational evaluation is not used across poles. -/
theorem eval_powerSubstitution (p : ℕ) (hp : 0 < p) (f : RatFunc ℂ) (z : ℂ)
    (hf : f.denom.eval (z^p) ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z (powerSubstitution p hp f) =
      RatFunc.eval (RingHom.id ℂ) (z^p) f := by
  have hh : (f.denom.comp (Polynomial.X^p)).eval z ≠ 0 := by
    simpa only [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X] using hf
  calc
    _ = RatFunc.eval (RingHom.id ℂ) z (powerSubstitution p hp
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) f.num /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) f.denom)) := by rw [RatFunc.num_div_denom]
    _ = (f.num.comp (Polynomial.X^p)).eval z / (f.denom.comp (Polynomial.X^p)).eval z := by
      rw [powerSubstitution_div, eval_polynomial_fraction _ _ _ hh]
    _ = _ := by simp only [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]; rfl


/-- A genuine nonpole remains a nonpole after positive power substitution. -/
theorem powerSubstitution_pole_free (p : ℕ) (hp : 0 < p) (f : RatFunc ℂ) (z : ℂ)
    (hf : f.denom.eval (z^p) ≠ 0) : (powerSubstitution p hp f).denom.eval z ≠ 0 := by
  have he : powerSubstitution p hp f =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (f.num.comp (Polynomial.X^p)) /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (f.denom.comp (Polynomial.X^p)) := by
    calc
      _ = powerSubstitution p hp (algebraMap (Polynomial ℂ) (RatFunc ℂ) f.num /
          algebraMap (Polynomial ℂ) (RatFunc ℂ) f.denom) := by rw [RatFunc.num_div_denom]
      _ = _ := powerSubstitution_div p hp _ _
  have hd := RatFunc.denom_div_dvd (f.num.comp (Polynomial.X^p)) (f.denom.comp (Polynomial.X^p))
  rw [← he] at hd
  intro hz
  have hh := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hd hz
  exact hf (by simpa only [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X] using hh)

/-- Scalar evaluation of the actual ramified coefficient at a nonpole. -/
theorem eval_ramifiedScalar (p : ℕ) (hp : 0 < p) (f : RatFunc ℂ) (z : ℂ)
    (hf : f.denom.eval (z^p) ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z
      (((p : RatFunc ℂ) * RatFunc.X^(p-1)) * powerSubstitution p hp f) =
        ((p : ℂ) * z^(p-1)) * RatFunc.eval (RingHom.id ℂ) (z^p) f := by
  have hfactor : (p : RatFunc ℂ) * RatFunc.X^(p-1) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C (p : ℂ) * Polynomial.X^(p-1)) := by simp
  rw [hfactor]
  have hd := powerSubstitution_pole_free p hp f z hf
  have hh := RatFunc.eval_mul (f := RingHom.id ℂ) (a := z)
    (x := algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.C (p : ℂ) * Polynomial.X^(p-1)))
    (y := powerSubstitution p hp f) (by rw [RatFunc.denom_algebraMap]; simp) (by simpa using hd)
  rw [hh, RatFunc.eval_algebraMap, eval_powerSubstitution p hp f z hf]
  simp

/-- The actual rational coefficient evaluates to the exact chain-rule
coefficient of the transformed analytic system at every genuine nonpole. -/
theorem eval_rationalCoefficient {m : ℕ} (p : ℕ) (hp : 0 < p)
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (z : ℂ)
    (hA : ∀ i j, (A i j).denom.eval (z^p) ≠ 0) :
    (rationalCoefficient p hp A).map (RatFunc.eval (RingHom.id ℂ) z) =
      coefficient p (fun x => A.map (RatFunc.eval (RingHom.id ℂ) x)) z := by
  ext i j
  exact eval_ramifiedScalar p hp (A i j) z (hA i j)

end WasowRamification

#print axioms WasowRamification.solution_hasDerivAt
#print axioms WasowRamification.real_solution_hasDerivAt
#print axioms WasowRamification.coefficient_monomial
#print axioms WasowRamification.ramified_rank
#print axioms WasowRamification.integral_slope_rank_decreases

#print axioms WasowRamification.polynomial_comp_pow_ne_zero
#print axioms WasowRamification.powerSubstitution_div
#print axioms WasowRamification.exists_integral_ramification

#print axioms WasowRamification.powerSubstitution_preserves_nonZeroDivisors
#print axioms WasowRamification.eval_polynomial_fraction
#print axioms WasowRamification.eval_powerSubstitution

#print axioms WasowRamification.powerSubstitution_pole_free
#print axioms WasowRamification.eval_ramifiedScalar
#print axioms WasowRamification.eval_rationalCoefficient
