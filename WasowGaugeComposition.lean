import WasowRationalEvaluation
import WasowGaugeAssembly

/-! Closure of actual ray normal forms under genuine intermediate gauges.
The generic theorem records only the coordinate change between two rational
systems. Concrete constant and integer-shearing changes construct these data. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators Matrix.Norms.Operator
namespace WasowGaugeComposition
open CRGNormalFormGoal WasowRealization WasowGaugeAssembly WasowRationalEvaluation
variable {m : ℕ}

/-- Actual intermediate coordinates, not a final diagonal normal form. -/
structure RayGaugeChange (A B : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ) where
  H : ℝ → Matrix (Fin m) (Fin m) ℂ
  S : ℝ → Matrix (Fin m) (Fin m) ℂ
  H' : ℝ → Matrix (Fin m) (Fin m) ℂ
  R : ℝ
  C : ℝ
  K : ℝ
  R_pos : 0 < R
  C_pos : 0 < C
  K_nonneg : 0 ≤ K
  derivative : ∀ r > R, ∀ i j, HasDerivAt (fun t => H t i j) (H' r i j) r
  inverse_left : ∀ r > R, S r * H r = 1
  inverse_right : ∀ r > R, H r * S r = 1
  H_bound : ∀ r > R, ∀ x : Fin m → ℂ, ‖(H r).mulVec x‖ ≤ C * r ^ K * ‖x‖
  S_bound : ∀ r > R, ∀ x : Fin m → ℂ, ‖(S r).mulVec x‖ ≤ C * r ^ K * ‖x‖
  identity : ∀ r > R, coefficientOnRay A θ r * H r =
    H' r + H r * coefficientOnRay B θ r

/-- Exact algebra of an intermediate change followed by the final gauge. -/
theorem gauge_composition_identity (A B H S H' U V U' : Matrix (Fin m) (Fin m) ℂ)
    (hH : A * H = H' + H * B) (hSH : S * H = 1) :
    (V * S) * A * (H * U) - (V * S) * (H' * U + H * U') =
      V * B * U - V * U' := by
  have hh : S * A * H - S * H' = B := by
    calc
      _ = S * (A * H - H') := by noncomm_ring
      _ = S * (H * B) := by rw [hH]; noncomm_ring
      _ = B := by rw [← Matrix.mul_assoc, hSH, Matrix.one_mul]
  calc
    _ = V * (S * A * H - S * H') * U - V * (S * H) * U' := by noncomm_ring
    _ = _ := by rw [hh, hSH, Matrix.mul_one]

/-- Compose genuine intermediate coordinates with an already constructed
normal form of the transformed system. The original pole-free tail is derived
from rationality, so no new normal form or pole assumption is introduced. -/
theorem pullback_rayGauge (A B : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ)
    (Q : Fin m → ℝ → ℂ) (F : RayGaugeChange A B θ) (W : RayGaugeWitness B θ Q) :
    Nonempty (RayGaugeWitness A θ Q) := by
  obtain ⟨Rp, hp⟩ := eventually_atTop.mp (WasowRamifiedGauge.eventually_original_pole_free A θ)
  let R := max F.R (max W.R Rp)
  have hF {r : ℝ} (hr : R < r) : F.R < r := (le_max_left _ _).trans_lt hr
  have hW {r : ℝ} (hr : R < r) : W.R < r :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hr
  have hRp {r : ℝ} (hr : R < r) : Rp ≤ r :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hr.le
  have hrpos {r : ℝ} (hr : R < r) : 0 < r := F.R_pos.trans (hF hr)
  refine ⟨{
    T := fun r => F.H r * W.T r
    S := fun r => W.S r * F.S r
    T' := fun r => F.H' r * W.T r + F.H r * W.T' r
    R := R, C := F.C * W.C, K := F.K + W.K
    R_pos := F.R_pos.trans_le (le_max_left _ _)
    C_pos := mul_pos F.C_pos W.C_pos
    K_nonneg := add_nonneg F.K_nonneg W.K_nonneg
    pole_free := fun r hr => hp r (hRp hr)
    T_derivative := fun r hr i j => matrix_product_hasDerivAt _ _ _ _
      (F.derivative r (hF hr)) (W.T_derivative r (hW hr)) i j
    inverse_left := ?_
    inverse_right := ?_
    T_bound := ?_
    S_bound := ?_
    gauge_identity := ?_ }⟩
  · intro r hr
    calc
      _ = W.S r * (F.S r * F.H r) * W.T r := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F.inverse_left r (hF hr), Matrix.mul_one, W.inverse_left r (hW hr)]
  · intro r hr
    calc
      _ = F.H r * (W.T r * W.S r) * F.S r := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [W.inverse_right r (hW hr), Matrix.mul_one, F.inverse_right r (hF hr)]
  · intro r hr x
    rw [← Matrix.mulVec_mulVec]
    calc
      _ ≤ F.C * r ^ F.K * ‖(W.T r).mulVec x‖ := F.H_bound r (hF hr) _
      _ ≤ F.C * r ^ F.K * (W.C * r ^ W.K * ‖x‖) := mul_le_mul_of_nonneg_left
        (W.T_bound r (hW hr) x) (mul_nonneg F.C_pos.le (Real.rpow_nonneg (hrpos hr).le _))
      _ = _ := by rw [Real.rpow_add (hrpos hr)]; ring
  · intro r hr x
    rw [← Matrix.mulVec_mulVec]
    calc
      _ ≤ W.C * r ^ W.K * ‖(F.S r).mulVec x‖ := W.S_bound r (hW hr) _
      _ ≤ W.C * r ^ W.K * (F.C * r ^ F.K * ‖x‖) := mul_le_mul_of_nonneg_left
        (F.S_bound r (hF hr) x) (mul_nonneg W.C_pos.le (Real.rpow_nonneg (hrpos hr).le _))
      _ = _ := by rw [Real.rpow_add (hrpos hr)]; ring
  · intro r hr
    exact (gauge_composition_identity _ _ _ _ _ _ _ _
      (F.identity r (hF hr)) (F.inverse_left r (hF hr))).trans (W.gauge_identity r (hW hr))

/-- A constant matrix viewed inside the actual rational-function field. -/
def constantMatrix (C : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) (RatFunc ℂ) :=
  C.map (algebraMap ℂ (RatFunc ℂ))

def constantConjugate (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (C : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) (RatFunc ℂ) :=
  constantMatrix C⁻¹ * A * constantMatrix C

@[simp] theorem value_constantMatrix (C : Matrix (Fin m) (Fin m) ℂ) (θ r : ℝ) :
    (constantMatrix C).map (value θ r) = C := by
  ext i j
  exact value_constant θ r (C i j)

/-- The rational constant similarity agrees with its actual ray evaluation. -/
theorem eventually_constantConjugate (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (C : Matrix (Fin m) (Fin m) ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, coefficientOnRay (constantConjugate A C) θ r =
      C⁻¹ * coefficientOnRay A θ r * C := by
  filter_upwards [eventually_value_matrix_mul (constantMatrix C⁻¹ * A) (constantMatrix C) θ,
    eventually_value_matrix_mul (constantMatrix C⁻¹) A θ] with r h₁ h₂
  have he : (constantConjugate A C).map (value θ r) = C⁻¹ * A.map (value θ r) * C := by
    unfold constantConjugate
    rw [h₁, h₂, value_constantMatrix, value_constantMatrix]
  have hc (M : Matrix (Fin m) (Fin m) (RatFunc ℂ)) :
      coefficientOnRay M θ r = Complex.exp ((θ : ℂ) * Complex.I) • M.map (value θ r) := rfl
  rw [hc, he, hc, Matrix.mul_smul, Matrix.smul_mul]

/-- Construct the genuine constant coordinate change from an arbitrary
nonsingular complex matrix, with actual inverse and finite operator bounds. -/
theorem constant_change (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (C : Matrix (Fin m) (Fin m) ℂ) (hC : C.det ≠ 0) (θ : ℝ) :
    Nonempty (RayGaugeChange A (constantConjugate A C) θ) := by
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (eventually_constantConjugate A C θ)
  let M : ℝ := ‖toOperator C‖ + ‖toOperator C⁻¹‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hCM : ‖toOperator C‖ ≤ M := by dsimp [M]; linarith [norm_nonneg (toOperator C⁻¹)]
  have hSM : ‖toOperator C⁻¹‖ ≤ M := by dsimp [M]; linarith [norm_nonneg (toOperator C)]
  have hi : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.mpr hC)
  have hj : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.mpr hC)
  refine ⟨{
    H := fun _ => C, S := fun _ => C⁻¹, H' := fun _ => 0
    R := max 1 R₀, C := M, K := 0
    R_pos := zero_lt_one.trans_le (le_max_left _ _)
    C_pos := hM, K_nonneg := le_rfl
    derivative := fun r _ i j => hasDerivAt_const r (C i j)
    inverse_left := fun _ _ => hi
    inverse_right := fun _ _ => hj
    H_bound := ?_
    S_bound := ?_
    identity := ?_ }⟩
  · intro r _ x
    simp only [Real.rpow_zero, mul_one]
    exact (ContinuousLinearMap.le_opNorm (toOperator C) x).trans
      (mul_le_mul_of_nonneg_right hCM (norm_nonneg x))
  · intro r _ x
    simp only [Real.rpow_zero, mul_one]
    exact (ContinuousLinearMap.le_opNorm (toOperator C⁻¹) x).trans
      (mul_le_mul_of_nonneg_right hSM (norm_nonneg x))
  · intro r hr
    rw [hR₀ r ((le_max_right _ _).trans hr.le), zero_add, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hj, Matrix.one_mul]

/-- A genuine constant coordinate transformation preserves the exact ray
normal-form conclusion for the same phase functions. -/
theorem pullback_constant_rayGauge (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (C : Matrix (Fin m) (Fin m) ℂ) (hC : C.det ≠ 0) (θ : ℝ)
    (Q : Fin m → ℝ → ℂ) (W : RayGaugeWitness (constantConjugate A C) θ Q) :
    Nonempty (RayGaugeWitness A θ Q) := by
  obtain ⟨F⟩ := constant_change A C hC θ
  exact pullback_rayGauge A _ θ Q F W

end WasowGaugeComposition
#print axioms WasowGaugeComposition.gauge_composition_identity
#print axioms WasowGaugeComposition.pullback_rayGauge
#print axioms WasowGaugeComposition.value_constantMatrix
#print axioms WasowGaugeComposition.eventually_constantConjugate
#print axioms WasowGaugeComposition.constant_change
#print axioms WasowGaugeComposition.pullback_constant_rayGauge
