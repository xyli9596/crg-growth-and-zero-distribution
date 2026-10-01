import CRGPolynomialKernelAtInfinity
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace CRGPolynomialKernel

/-- A continuous choice of a root on a connected set differs from another
choice by one fixed root of unity, rather than a pointwise branch factor. -/
theorem root_ratio_constant {S : Set ℂ} (hS : IsPreconnected S)
    {f g : ℂ → ℂ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hgn : ∀ x ∈ S, g x ≠ 0) {m : ℕ} (hm : 0 < m)
    (he : ∀ x ∈ S, (f x)^m = (g x)^m) :
    ∀ x₀ ∈ S, ∀ x ∈ S, f x = (f x₀ / g x₀) * g x := by
  have hpoly : (Polynomial.X ^ m - Polynomial.C (1 : ℂ)) ≠ 0 := by
    intro hz
    have hc := congrArg (Polynomial.coeff · m) hz
    simp only [Polynomial.coeff_sub,Polynomial.coeff_X_pow_self,
      Polynomial.coeff_C,if_neg hm.ne',Polynomial.coeff_zero] at hc
    norm_num at hc
  have hroot : ∀ x ∈ S, Polynomial.IsRoot (Polynomial.X ^ m - Polynomial.C (1 : ℂ))
      (f x / g x) := by
    intro x hx
    simp only [Polynomial.IsRoot,Polynomial.eval_sub,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C]
    rw [div_pow,he x hx,div_self (pow_ne_zero _ (hgn x hx)),sub_self]
  have hfin : ( (fun x => f x / g x) '' S).Finite :=
    (Polynomial.finite_setOfPred_isRoot hpoly).subset (by
      rintro z ⟨x,hx,rfl⟩; exact hroot x hx)
  have hconn := hS.image (fun x => f x / g x) (hf.div hg hgn)
  intro x₀ hx₀ x hx
  have heq : f x / g x = f x₀ / g x₀ := by
    by_contra hn
    exact (hconn.infinite_of_nontrivial
      ⟨_,⟨x,hx,rfl⟩,_,⟨x₀,hx₀,rfl⟩,hn⟩).not_finite hfin
  exact (div_eq_iff (hgn x hx)).mp heq

/-- A fixed analytic germ of the fractional inverse phase after clearing
its integer ramification exponent. -/
def inversePhaseRoot (Q : Polynomial ℂ) (p m : ℕ) (x : ℂ) : ℂ :=
  x ^ (p * Q.natDegree / m) * (phaseUnit Q p x) ^ (-(m : ℂ)⁻¹) *
    Q.leadingCoeff ^ (-(m : ℂ)⁻¹)

theorem analyticAt_inversePhaseRoot {Q : Polynomial ℂ} (hQ : Q ≠ 0)
    {p : ℕ} (hp : 0 < p) (m : ℕ) :
    AnalyticAt ℂ (inversePhaseRoot Q p m) 0 :=
  ((analyticAt_id.pow _).mul (analyticAt_fractionalPhaseUnit hQ hp _)).mul analyticAt_const

theorem inversePhaseRoot_pow {Q : Polynomial ℂ} (hQ : Q ≠ 0)
    {p m : ℕ} (hm : 0 < m) (hdiv : m ∣ p * Q.natDegree) (x : ℂ) :
    (inversePhaseRoot Q p m x)^m = inversePhase Q p x := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hexp : (-(m : ℂ)⁻¹) * m = (-1 : ℂ) := by field_simp
  unfold inversePhaseRoot inversePhase phaseUnit
  rw [mul_pow,mul_pow,←pow_mul,Nat.div_mul_cancel hdiv,
    ←Complex.cpow_mul_nat,hexp,Complex.cpow_neg_one,
    ←Complex.cpow_mul_nat,hexp,Complex.cpow_neg_one,inv_div,mul_assoc]
  have hlc := Polynomial.leadingCoeff_ne_zero.mpr hQ
  simp only [div_eq_mul_inv]
  field_simp

theorem inversePhaseRoot_zero {Q : Polynomial ℂ} (hdegree : 0 < Q.natDegree)
    {p m : ℕ} (hp : 0 < p) (hm : 0 < m) (hdiv : m ∣ p * Q.natDegree) :
    inversePhaseRoot Q p m 0 = 0 := by
  have hk : 0 < p * Q.natDegree / m :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hp hdegree) hdiv) hm
  simp only [inversePhaseRoot, zero_pow hk.ne', zero_mul]

/-- A sectorial principal inverse root and the analytic ramified germ have
one fixed branch factor on every connected punctured sector. -/
theorem principal_inverse_root_eq {Q : Polynomial ℂ} (hQ : Q ≠ 0)
    {p m : ℕ} (hm : 0 < m) (hdiv : m ∣ p * Q.natDegree)
    {S : Set ℂ} (hS : IsPreconnected S)
    (hx : ∀ x ∈ S, x ≠ 0)
    (hs : ∀ x ∈ S, 0 < (Q.eval (x ^ (-(p : ℤ)))).re)
    (hg : ContinuousOn (inversePhaseRoot Q p m) S) :
    ∀ x₀ ∈ S, ∀ x ∈ S,
      (Q.eval (x ^ (-(p : ℤ)))) ^ (-(m : ℂ)⁻¹) =
        ((Q.eval (x₀ ^ (-(p : ℤ)))) ^ (-(m : ℂ)⁻¹) /
          inversePhaseRoot Q p m x₀) * inversePhaseRoot Q p m x := by
  let f : ℂ → ℂ := fun x => (Q.eval (x ^ (-(p : ℤ)))) ^ (-(m : ℂ)⁻¹)
  have hvalue : ∀ x ∈ S, Q.eval (x ^ (-(p : ℤ))) ≠ 0 := by
    intro x hxs hz
    have hh := hs x hxs
    rw [hz] at hh
    norm_num at hh
  have hf : ContinuousOn f S := by
    have hphase : ContinuousOn (fun x : ℂ => Q.eval (x ^ (-(p : ℤ)))) S :=
      Q.continuous.comp_continuousOn (continuousOn_id.zpow₀ (-(p : ℤ)) (fun x hxs => Or.inl (hx x hxs)))
    exact hphase.cpow continuousOn_const (fun x hxs => Or.inl (hs x hxs))
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hexp : (-(m : ℂ)⁻¹) * m = (-1 : ℂ) := by field_simp
  have hpow : ∀ x ∈ S, (f x)^m = (inversePhaseRoot Q p m x)^m := by
    intro x hxs
    rw [inversePhaseRoot_pow hQ hm hdiv,inversePhase_eq p (hx x hxs)]
    dsimp [f]
    rw [←Complex.cpow_mul_nat,hexp,Complex.cpow_neg_one]
  have hgn : ∀ x ∈ S, inversePhaseRoot Q p m x ≠ 0 := by
    intro x hxs hz
    have hh := hpow x hxs
    rw [hz,zero_pow hm.ne'] at hh
    exact (pow_ne_zero m (Complex.cpow_ne_zero_iff.mpr (Or.inl (hvalue x hxs)))) hh
  exact root_ratio_constant hS hf hg hgn hm hpow

#print axioms root_ratio_constant
#print axioms inversePhaseRoot_pow
end CRGPolynomialKernel
