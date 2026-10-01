import CRGProgress
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
This file states a SMALLER missing input sufficient for the ray proof.
`RationalRayNormalFormGoal` is a DEFINITION of a proposition, not a theorem.
No proof or inhabitant of that proposition is supplied here. It is not an axiom
and is not used to label the main CRG theorem as verified.
WasowDiagonal.lean proves the exact conclusion for diagonal rational systems
and all one-dimensional systems; the general matrix goal remains unproved.

The ray-only gauge conclusion does not require formalizing the entire Wasow book,
sectorial asymptotic series, or Stokes transition matrices. Proving this conclusion
from a rational system would still require the relevant formal reduction and
analytic realization theorem, including repeated eigenvalues.
-/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace CRGNormalFormGoal

/-- A branch of the p-th root on a fixed ray, indexed by the finite choice ℓ. -/
def rootOnRay (p : ℕ) (θ : ℝ) (ℓ : Fin p) (r : ℝ) : ℂ :=
  (r ^ (1 / (p : ℝ)) : ℝ) *
    Complex.exp (((θ + 2 * Real.pi * (ℓ : ℝ)) / (p : ℝ) : ℝ) * Complex.I)

def phaseOnRay (p : ℕ) (G : Polynomial ℂ) (θ : ℝ) (ℓ : Fin p) (r : ℝ) : ℂ :=
  G.eval (rootOnRay p θ ℓ r)

def ray (θ r : ℝ) : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

/-- A rational matrix evaluated on a ray, including the factor dz/dr. Denominator
zeros are excluded by the witness's starting radius, rather than by totalized division. -/
def coefficientOnRay {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (θ r : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => Complex.exp ((θ : ℂ) * Complex.I) *
    RatFunc.eval (RingHom.id ℂ) (ray θ r) (A i j)

/-- Exact C1 gauge data on one ray tail, with polynomial bounds on BOTH T and T⁻¹.
Matrix differentiation is entrywise along the real parameter. The coefficient
bound is explicitly in the induced infinity operator norm, through `mulVec`. -/
structure RayGaugeWitness {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ)
    (q : Fin m → ℝ → ℂ) where
  T : ℝ → Matrix (Fin m) (Fin m) ℂ
  S : ℝ → Matrix (Fin m) (Fin m) ℂ
  T' : ℝ → Matrix (Fin m) (Fin m) ℂ
  R : ℝ
  C : ℝ
  K : ℝ
  R_pos : 0 < R
  C_pos : 0 < C
  K_nonneg : 0 ≤ K
  pole_free : ∀ r > R, ∀ i j,
    (RatFunc.denom (A i j)).eval (ray θ r) ≠ 0
  T_derivative : ∀ r > R, ∀ i j,
    HasDerivAt (fun t => T t i j) (T' r i j) r
  inverse_left : ∀ r > R, S r * T r = 1
  inverse_right : ∀ r > R, T r * S r = 1
  T_bound : ∀ r > R, ∀ x : Fin m → ℂ, ‖(T r).mulVec x‖ ≤ C * r ^ K * ‖x‖
  S_bound : ∀ r > R, ∀ x : Fin m → ℂ, ‖(S r).mulVec x‖ ≤ C * r ^ K * ‖x‖
  gauge_identity : ∀ r > R,
    S r * coefficientOnRay A θ r * T r - S r * T' r =
      Matrix.diagonal (fun i => deriv (q i) r)

/-- The missing ray normal-form EXISTENCE theorem, precisely scoped to rational
systems and a finite family of Puiseux-polynomial phases. This definition has no proof.
No assumption of distinct eigenvalues or diagonal G is imposed. -/
def RationalRayNormalFormGoal : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ A : Matrix (Fin m) (Fin m) (RatFunc ℂ),
    ∃ (p : ℕ), 0 < p ∧ ∃ G : Fin m → Polynomial ℂ,
      (∀ i, (G i).coeff 0 = 0) ∧
      ∀ θ : ℝ, ∃ ℓ : Fin p,
        Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (G i) θ ℓ))

end CRGNormalFormGoal
