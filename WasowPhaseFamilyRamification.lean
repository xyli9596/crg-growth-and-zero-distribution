import WasowPhaseFamily

/-! Actual pullback of an already ramified phase family through another power
substitution. The output denominator is the product, chosen independently of the
ray. All gauges are differentiated and both inverse bounds are transported. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology
namespace WasowPhaseFamilyRamification
open CRGNormalFormGoal WasowRamifiedGauge WasowRamification

theorem rootOnRay_comp (p d : ℕ) (hp : 0 < p) (hd : 0 < d)
    (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    rootOnRay d (θ / p) ⟨0,hd⟩ (rootRadius p r) =
      rootOnRay (p*d) θ ⟨0,Nat.mul_pos hp hd⟩ r := by
  have he : (1 / (p : ℝ)) * (1 / (d : ℝ)) = 1 / ((p*d : ℕ) : ℝ) := by
    push_cast
    ring
  have ha : (θ / (p : ℝ)) / (d : ℝ) = θ / ((p*d : ℕ) : ℝ) := by
    push_cast
    ring
  simp only [rootOnRay, rootRadius, Nat.cast_zero, mul_zero, add_zero,
    ← Real.rpow_mul hr, he, ha]

theorem phaseOnRay_comp (p d : ℕ) (hp : 0 < p) (hd : 0 < d)
    (F : Polynomial ℂ) (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    phaseOnRay d F (θ / p) ⟨0,hd⟩ (rootRadius p r) =
      phaseOnRay (p*d) F θ ⟨0,Nat.mul_pos hp hd⟩ r := by
  simp only [phaseOnRay, rootOnRay_comp p d hp hd θ hr]

theorem phase_derivative_comp (p d : ℕ) (hp : 0 < p) (hd : 0 < d)
    (F : Polynomial ℂ) (θ : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (phaseOnRay (p*d) F θ ⟨0,Nat.mul_pos hp hd⟩) r =
      (rootRadiusDerivative p r : ℂ) *
        deriv (phaseOnRay d F (θ / p) ⟨0,hd⟩) (rootRadius p r) := by
  have hh := ((WasowPhaseOrdering.phase_hasDerivAt d F (θ / p) ⟨0,hd⟩
    (rootRadius_pos p hr)).differentiableAt.hasDerivAt).scomp r (rootRadius_hasDerivAt p hr)
  have he : (fun t => phaseOnRay d F (θ / p) ⟨0,hd⟩ (rootRadius p t)) =ᶠ[𝓝 r]
      phaseOnRay (p*d) F θ ⟨0,Nat.mul_pos hp hd⟩ := by
    filter_upwards [eventually_gt_nhds hr] with t ht
    exact phaseOnRay_comp p d hp hd F θ ht.le
  have hh' := hh.congr_of_eventuallyEq he.symm
  simpa only [Complex.real_smul, smul_eq_mul] using hh'.deriv

/-- Genuine gauge descent, allowing a nontrivial denominator in the child.
The original rational coefficient and its nonpoles are evaluated exactly. -/
theorem descend_rayGauge {m : ℕ} (p d : ℕ) (hp : 0 < p) (hd : 0 < d)
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (F : Fin m → Polynomial ℂ) (θ : ℝ)
    (H : RayGaugeWitness (rationalCoefficient p hp A) (θ / p)
      (fun i => phaseOnRay d (F i) (θ / p) ⟨0,hd⟩)) :
    Nonempty (RayGaugeWitness A θ
      (fun i => phaseOnRay (p*d) (F i) θ ⟨0,Nat.mul_pos hp hd⟩)) := by
  have ht : Tendsto (rootRadius p) atTop atTop :=
    tendsto_rpow_atTop (by positivity : 0 < 1 / (p : ℝ))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp
    ((ht.eventually (eventually_gt_atTop H.R)).and (eventually_original_pole_free A θ))
  let R := max 1 R₀
  have hR : 1 ≤ R := le_max_left _ _
  have htail {r : ℝ} (hr : R < r) : H.R < rootRadius p r :=
    (hR₀ r ((le_max_right _ _).trans hr.le)).1
  have hpole {r : ℝ} (hr : R < r) : ∀ i j, (A i j).denom.eval (ray θ r) ≠ 0 :=
    (hR₀ r ((le_max_right _ _).trans hr.le)).2
  have hrpos {r : ℝ} (hr : R < r) : 0 < r := zero_lt_one.trans_le (hR.trans hr.le)
  refine ⟨{
    T := fun r => H.T (rootRadius p r)
    S := fun r => H.S (rootRadius p r)
    T' := fun r => (rootRadiusDerivative p r : ℂ) • H.T' (rootRadius p r)
    R := R, C := H.C, K := H.K / p
    R_pos := zero_lt_one.trans_le hR
    C_pos := H.C_pos
    K_nonneg := div_nonneg H.K_nonneg (Nat.cast_nonneg _)
    pole_free := fun _ hr => hpole hr
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
      coefficient_pullback p hp A θ (hrpos hr) (hpole hr)] at hh
    rw [← Matrix.mul_smul] at hh
    have hD : (rootRadiusDerivative p r : ℂ) •
        Matrix.diagonal (fun i => deriv (phaseOnRay d (F i) (θ / p) ⟨0,hd⟩) (rootRadius p r)) =
      Matrix.diagonal (fun i => deriv (phaseOnRay (p*d) (F i) θ ⟨0,Nat.mul_pos hp hd⟩) r) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul,
        phase_derivative_comp p d hp hd (F i) θ (hrpos hr)]
      split_ifs <;> simp
    exact hh.trans hD

/-- The child denominator and its phase polynomials are chosen before the
angle; the same is therefore true of their product denominator in the parent. -/
theorem ramification_family_pullback {m : ℕ} (p d : ℕ) (hp : 0 < p) (hd : 0 < d)
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (F : Fin m → Polynomial ℂ)
    (h : ∀ θ : ℝ, Nonempty (RayGaugeWitness (rationalCoefficient p hp A) θ
      (fun i => phaseOnRay d (F i) θ ⟨0,hd⟩))) :
    ∀ θ : ℝ, Nonempty (RayGaugeWitness A θ
      (fun i => phaseOnRay (p*d) (F i) θ ⟨0,Nat.mul_pos hp hd⟩)) := by
  intro θ
  obtain ⟨W⟩ := h (θ / p)
  exact descend_rayGauge p d hp hd A F θ W

end WasowPhaseFamilyRamification
#print axioms WasowPhaseFamilyRamification.rootOnRay_comp
#print axioms WasowPhaseFamilyRamification.phaseOnRay_comp
#print axioms WasowPhaseFamilyRamification.phase_derivative_comp
#print axioms WasowPhaseFamilyRamification.descend_rayGauge
#print axioms WasowPhaseFamilyRamification.ramification_family_pullback
