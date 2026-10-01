import WasowFundamental
import WasowMatrixBounds
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
Exact realization on a real ray of an actual approximate gauge.  A formal
reduction is not assumed to be analytically realized automatically: the input
contains concrete differentiable gauge matrices, their inverse bounds, and an
exact residual equation.  The mixed Volterra theorem constructs the correcting
matrix.  No sectorial existence theorem or general rational reduction is claimed.
-/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators BoundedContinuousFunction
attribute [local instance] Measure.Subtype.measureSpace
open CRGNormalFormGoal WasowVolterra WasowFundamental

namespace WasowRealization

/-- The matrix of an actual continuous linear remainder in the standard basis. -/
def operatorMatrix {m : ℕ} (R : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) :
    Matrix (Fin m) (Fin m) ℂ := LinearMap.toMatrix' R.toLinearMap

theorem operatorMatrix_mul_apply {m : ℕ}
    (R : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ))
    (U : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    (operatorMatrix R * U) i j = R (fun k => U k j) i := by
  have h := congrFun (LinearMap.toMatrix'_mulVec R.toLinearMap (fun k => U k j)) i
  exact h

theorem matrix_product_hasDerivAt {m : ℕ}
    (H U : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (H' U' : Matrix (Fin m) (Fin m) ℂ) {r : ℝ}
    (hH : ∀ i j, HasDerivAt (fun t => H t i j) (H' i j) r)
    (hU : ∀ i j, HasDerivAt (fun t => U t i j) (U' i j) r) (i j : Fin m) :
    HasDerivAt (fun t => (H t * U t) i j) ((H' * U r + H r * U') i j) r := by
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib, Pi.mul_apply] using
    HasDerivAt.fun_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) =>
      (hH i k).mul (hU k j))

theorem corrected_derivative_identity {m : ℕ}
    (A H H' U U' D B : Matrix (Fin m) (Fin m) ℂ)
    (hH : A * H = H' + H * (D + B))
    (hU : U' = (D + B) * U - U * D) :
    H' * U + H * U' = A * (H * U) - (H * U) * D := by
  rw [hU]
  calc
    H' * U + H * ((D + B) * U - U * D) =
        (H' + H * (D + B)) * U - (H * U) * D := by noncomm_ring
    _ = A * (H * U) - (H * U) * D := by rw [← hH, Matrix.mul_assoc]

/-- The actual near-identity correction is obtained by solving all Volterra
columns on one common half-line. -/
theorem exists_normalized_correction (m : ℕ) (a : ℝ)
    (mode : Fin m → Fin m → Bool) (Q dQ : Fin m → ℝ → ℂ)
    (hQ : ∀ i, Continuous (Q i))
    (hdQ : ∀ i r, a < r → HasDerivAt (Q i) (dQ i r) r)
    (hord : ∀ j i, if mode j i then
      Antitone (fun t : Ici a => (Q i t - Q j t).re)
      else Monotone (fun t : Ici a => (Q i t - Q j t).re))
    (hdecay : ∀ j i, mode j i = true →
      Tendsto (fun r : Ici a => (Q i r - Q j r).re) atTop atBot)
    (R : Ici a → (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) (hR : Continuous R)
    (hL1 : Integrable (fun s : Ici a => ‖R s‖))
    (hsmall : (∫ s : Ici a, ‖R s‖) < 1) :
    ∃ U : ℝ → Matrix (Fin m) (Fin m) ℂ,
      Tendsto U atTop (𝓝 1) ∧ ∀ r : ℝ, a < r → ∀ i j,
        HasDerivAt (fun t => U t i j)
          (((Matrix.diagonal (fun k => dQ k r) + operatorMatrix (extend a R r)) * U r -
            U r * Matrix.diagonal (fun k => dQ k r)) i j) r := by
  classical
  choose u _hu hlim hode using fun j => exists_phase_difference_column_ode m a j
    (mode j) Q dQ hQ hdQ (hord j) (hdecay j) R hR hL1 hsmall
  refine ⟨normalizedMatrix u, normalizedMatrix_tendsto_one u hlim, ?_⟩
  intro r hr i j
  have hh := hasDerivAt_pi.mp (hode j r hr) i
  have heq : (((Matrix.diagonal (fun k => dQ k r) + operatorMatrix (extend a R r)) *
      normalizedMatrix u r - normalizedMatrix u r * Matrix.diagonal (fun k => dQ k r)) i j) =
      (dQ i r - dQ j r) * extend a (u j) r i +
        (extend a R r (extend a (u j) r)) i := by
    simp only [Matrix.add_mul, Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, operatorMatrix_mul_apply, normalizedMatrix]
    ring
  rw [heq]
  exact hh

/-- Concrete input expected from a finite formal truncation.  This records a
residual equation, not the exact normal-form conclusion. -/
structure ApproximateRayGauge {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ a : ℝ)
    (dQ : Fin m → ℝ → ℂ)
    (R : Ici a → (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) where
  H : ℝ → Matrix (Fin m) (Fin m) ℂ
  Hinv : ℝ → Matrix (Fin m) (Fin m) ℂ
  H' : ℝ → Matrix (Fin m) (Fin m) ℂ
  C : ℝ
  K : ℝ
  a_pos : 0 < a
  C_pos : 0 < C
  K_nonneg : 0 ≤ K
  pole_free : ∀ r > a, ∀ i j, (RatFunc.denom (A i j)).eval (ray θ r) ≠ 0
  H_derivative : ∀ r > a, ∀ i j, HasDerivAt (fun t => H t i j) (H' r i j) r
  inverse_left : ∀ r > a, Hinv r * H r = 1
  inverse_right : ∀ r > a, H r * Hinv r = 1
  H_bound : ∀ r > a, ∀ x : Fin m → ℂ, ‖(H r).mulVec x‖ ≤ C * r ^ K * ‖x‖
  Hinv_bound : ∀ r > a, ∀ x : Fin m → ℂ, ‖(Hinv r).mulVec x‖ ≤ C * r ^ K * ‖x‖
  residual_identity : ∀ r > a,
    coefficientOnRay A θ r * H r = H' r + H r *
      (Matrix.diagonal (fun i => dQ i r) + operatorMatrix (extend a R r))

/-- Construct an exact ray gauge by an actual Volterra correction of the
approximate gauge. The input remainder need not vanish. -/
theorem exists_exact_rayGauge {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ a : ℝ)
    (Q dQ : Fin m → ℝ → ℂ)
    (R : Ici a → (Fin m → ℂ) →L[ℂ] (Fin m → ℂ))
    (H : ApproximateRayGauge A θ a dQ R)
    (mode : Fin m → Fin m → Bool)
    (hQ : ∀ i, Continuous (Q i))
    (hdQ : ∀ i r, a < r → HasDerivAt (Q i) (dQ i r) r)
    (hord : ∀ j i, if mode j i then
      Antitone (fun t : Ici a => (Q i t - Q j t).re)
      else Monotone (fun t : Ici a => (Q i t - Q j t).re))
    (hdecay : ∀ j i, mode j i = true →
      Tendsto (fun r : Ici a => (Q i r - Q j r).re) atTop atBot)
    (hR : Continuous R) (hL1 : Integrable (fun s : Ici a => ‖R s‖))
    (hsmall : (∫ s : Ici a, ‖R s‖) < 1) :
    Nonempty (RayGaugeWitness A θ Q) := by
  obtain ⟨U, hUlim, hUode⟩ := exists_normalized_correction m a mode Q dQ
    hQ hdQ hord hdecay R hR hL1 hsmall
  obtain ⟨C, hC, htail⟩ := WasowMatrixBounds.eventually_uniform_mulVec_bounds hUlim
  obtain ⟨B, hB⟩ := eventually_atTop.mp htail
  let U' : ℝ → Matrix (Fin m) (Fin m) ℂ := fun r =>
    (Matrix.diagonal (fun k => dQ k r) + operatorMatrix (extend a R r)) * U r -
      U r * Matrix.diagonal (fun k => dQ k r)
  have ha {r : ℝ} (hr : max a B < r) : a < r := (le_max_left _ _).trans_lt hr
  have hb {r : ℝ} (hr : max a B < r) : B ≤ r := ((le_max_right _ _).trans_lt hr).le
  have hleft {r : ℝ} (hr : max a B < r) :
      ((U r)⁻¹ * H.Hinv r) * (H.H r * U r) = 1 := by
    calc
      _ = (U r)⁻¹ * (H.Hinv r * H.H r) * U r := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [H.inverse_left r (ha hr), Matrix.mul_one, (hB r (hb hr)).1]
  refine ⟨{
    T := fun r => H.H r * U r
    S := fun r => (U r)⁻¹ * H.Hinv r
    T' := fun r => H.H' r * U r + H.H r * U' r
    R := max a B
    C := H.C * C
    K := H.K
    R_pos := H.a_pos.trans_le (le_max_left _ _)
    C_pos := mul_pos H.C_pos hC
    K_nonneg := H.K_nonneg
    pole_free := fun r hr => H.pole_free r (ha hr)
    T_derivative := fun r hr i j => matrix_product_hasDerivAt H.H U (H.H' r) (U' r)
      (H.H_derivative r (ha hr)) (hUode r (ha hr)) i j
    inverse_left := fun _ hr => hleft hr
    inverse_right := ?_
    T_bound := ?_
    S_bound := ?_
    gauge_identity := ?_
  }⟩
  · intro r hr
    calc
      (H.H r * U r) * ((U r)⁻¹ * H.Hinv r) =
          H.H r * (U r * (U r)⁻¹) * H.Hinv r := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [(hB r (hb hr)).2.1, Matrix.mul_one, H.inverse_right r (ha hr)]
  · intro r hr x
    rw [← Matrix.mulVec_mulVec]
    calc
      ‖(H.H r).mulVec ((U r).mulVec x)‖ ≤ H.C * r ^ H.K * ‖(U r).mulVec x‖ :=
        H.H_bound r (ha hr) _
      _ ≤ H.C * r ^ H.K * (C * ‖x‖) :=
        mul_le_mul_of_nonneg_left ((hB r (hb hr)).2.2.1 x)
          (mul_nonneg H.C_pos.le (Real.rpow_nonneg (H.a_pos.trans (ha hr)).le _))
      _ = H.C * C * r ^ H.K * ‖x‖ := by ring
  · intro r hr x
    rw [← Matrix.mulVec_mulVec]
    calc
      ‖((U r)⁻¹).mulVec ((H.Hinv r).mulVec x)‖ ≤ C * ‖(H.Hinv r).mulVec x‖ :=
        (hB r (hb hr)).2.2.2 _
      _ ≤ C * (H.C * r ^ H.K * ‖x‖) :=
        mul_le_mul_of_nonneg_left (H.Hinv_bound r (ha hr) x) hC.le
      _ = H.C * C * r ^ H.K * ‖x‖ := by ring
  · intro r hr
    have hp := corrected_derivative_identity (coefficientOnRay A θ r)
      (H.H r) (H.H' r) (U r) (U' r) (Matrix.diagonal (fun k => dQ k r))
      (operatorMatrix (extend a R r)) (H.residual_identity r (ha hr)) rfl
    rw [hp]
    calc
      (U r)⁻¹ * H.Hinv r * coefficientOnRay A θ r * (H.H r * U r) -
          ((U r)⁻¹ * H.Hinv r) *
            (coefficientOnRay A θ r * (H.H r * U r) -
              (H.H r * U r) * Matrix.diagonal (fun k => dQ k r)) =
          ((U r)⁻¹ * H.Hinv r) * ((H.H r * U r) * Matrix.diagonal (fun k => dQ k r)) := by
        simp only [Matrix.mul_sub, Matrix.mul_assoc]
        abel
      _ = Matrix.diagonal (fun k => dQ k r) := by
        rw [← Matrix.mul_assoc, hleft hr, Matrix.one_mul]
      _ = Matrix.diagonal (fun i => deriv (Q i) r) := by
        congr 1
        funext i
        exact (hdQ i r (ha hr)).deriv.symm

end WasowRealization

#print axioms WasowRealization.operatorMatrix_mul_apply
#print axioms WasowRealization.matrix_product_hasDerivAt
#print axioms WasowRealization.corrected_derivative_identity
#print axioms WasowRealization.exists_normalized_correction
#print axioms WasowRealization.exists_exact_rayGauge
