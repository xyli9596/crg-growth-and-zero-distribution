import CRGGeneralRayGauge
import WasowRamifiedGauge

/-! Actual power substitution for general coefficient functions. The exact
chain-rule identity is kept as an explicit input and all descended gauge
identities, derivatives, and two-sided polynomial bounds are proved. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology
namespace CRGGeneralRayRamification
open CRGNormalFormGoal WasowRamifiedGauge

theorem descend_rayGauge {m : ℕ} (p : ℕ) (hp : 0 < p)
    (A B : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (G : Fin m → Polynomial ℂ) (θ Rmin : ℝ)
    (hcoeff : ∀ r > Rmin, (rootRadiusDerivative p r : ℂ) • B (rootRadius p r) = A r)
    (H : CRGGeneralRayGauge.RayGaugeWitness B
      (fun i => phaseOnRay 1 (G i) (θ / p) 0)) :
    Nonempty (CRGGeneralRayGauge.RayGaugeWitness A
      (fun i => phaseOnRay p (G i) θ ⟨0, hp⟩)) := by
  have ht : Tendsto (rootRadius p) atTop atTop :=
    tendsto_rpow_atTop (by positivity : 0 < 1 / (p : ℝ))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp
    (ht.eventually (eventually_gt_atTop H.R))
  let R := max 1 (max R₀ Rmin)
  have hR : 1 ≤ R := le_max_left _ _
  have htail {r : ℝ} (hr : R < r) : H.R < rootRadius p r :=
    hR₀ r ((le_max_left R₀ Rmin).trans ((le_max_right _ _).trans hr.le))
  have hmin {r : ℝ} (hr : R<r) : Rmin<r :=
    (le_max_right R₀ Rmin).trans_lt ((le_max_right _ _).trans_lt hr)
  have hrpos {r : ℝ} (hr : R < r) : 0 < r := zero_lt_one.trans_le (hR.trans hr.le)
  refine ⟨{
    T := fun r => H.T (rootRadius p r)
    S := fun r => H.S (rootRadius p r)
    T' := fun r => (rootRadiusDerivative p r : ℂ) • H.T' (rootRadius p r)
    R := R, C := H.C, K := H.K / p
    R_pos := zero_lt_one.trans_le hR
    C_pos := H.C_pos
    K_nonneg := div_nonneg H.K_nonneg (Nat.cast_nonneg _)
    T_derivative := ?_
    inverse_left := fun _ hr => H.inverse_left _ (htail hr)
    inverse_right := fun _ hr => H.inverse_right _ (htail hr)
    T_bound := ?_
    S_bound := ?_
    gauge_identity := ?_ }⟩
  · intro r hr i j
    have hh := (H.T_derivative (rootRadius p r) (htail hr) i j).scomp r
      (rootRadius_hasDerivAt p (hrpos hr))
    convert! hh using 1
  · intro r hr x
    simpa only [rootRadius_rpow p (hrpos hr).le] using H.T_bound _ (htail hr) x
  · intro r hr x
    simpa only [rootRadius_rpow p (hrpos hr).le] using H.S_bound _ (htail hr) x
  · intro r hr
    have hh := congrArg (fun M => (rootRadiusDerivative p r : ℂ) • M)
      (H.gauge_identity (rootRadius p r) (htail hr))
    rw [smul_sub, ← Matrix.smul_mul, ← Matrix.mul_smul,
      hcoeff r (hmin hr)] at hh
    rw [← Matrix.mul_smul] at hh
    have hd : (rootRadiusDerivative p r : ℂ) •
        Matrix.diagonal (fun i => deriv (phaseOnRay 1 (G i) (θ / p) 0) (rootRadius p r)) =
      Matrix.diagonal (fun i => deriv (phaseOnRay p (G i) θ ⟨0, hp⟩) r) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul,
        phase_derivative_pullback p hp (G i) θ (hrpos hr)]
      split_ifs <;> simp
    exact hh.trans hd


#print axioms descend_rayGauge
end CRGGeneralRayRamification
