import WasowRamification
import WasowPhaseOrdering
import WasowPolynomialPhase
import WasowRational
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Actual analytic descent through a positive power ramification.
The zero root branch suffices for the existential branch in the original goal.
Every chain factor, rational evaluation, and inverse-growth bound is retained. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology
namespace WasowRamifiedGauge
open CRGNormalFormGoal WasowRamification

def rootRadius (p : ℕ) (r : ℝ) : ℝ := r ^ (1 / (p : ℝ))
def rootRadiusDerivative (p : ℕ) (r : ℝ) : ℝ :=
  (1 / (p : ℝ)) * r ^ (1 / (p : ℝ) - 1)

theorem rootRadius_pos (p : ℕ) {r : ℝ} (hr : 0 < r) : 0 < rootRadius p r :=
  Real.rpow_pos_of_pos hr _

theorem rootRadius_pow (p : ℕ) (hp : 0 < p) {r : ℝ} (hr : 0 ≤ r) :
    (rootRadius p r) ^ p = r := by
  simpa only [rootRadius, one_div] using Real.rpow_inv_natCast_pow hr hp.ne'

theorem rootRadius_hasDerivAt (p : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (rootRadius p) (rootRadiusDerivative p r) r :=
  Real.hasDerivAt_rpow_const (Or.inl hr.ne')

/-- Differentiating the true positive-root identity gives the exact reciprocal
chain factor without any asymptotic replacement. -/
theorem rootRadius_chain_factor (p : ℕ) (hp : 0 < p) {r : ℝ} (hr : 0 < r) :
    rootRadiusDerivative p r * ((p : ℝ) * (rootRadius p r) ^ (p - 1)) = 1 := by
  have hh := (rootRadius_hasDerivAt p hr).pow p
  have he : (fun t => (rootRadius p t) ^ p) =ᶠ[𝓝 r] (fun t : ℝ => t) := by
    filter_upwards [eventually_gt_nhds hr] with t ht
    exact rootRadius_pow p hp ht.le
  have hu := (hh.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id r)
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hu

/-- The chosen complex direction has exactly the required p-th power. -/
theorem direction_pow (p : ℕ) (hp : 0 < p) (θ : ℝ) :
    Complex.exp (((θ / p : ℝ) : ℂ) * Complex.I) ^ p =
      Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

/-- The ramified ray maps to the original ray as an actual complex equality. -/
theorem ray_root_pow (p : ℕ) (hp : 0 < p) (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ray (θ / p) (rootRadius p r) ^ p = ray θ r := by
  simp only [ray, mul_pow, ← Complex.ofReal_pow, rootRadius_pow p hp hr,
    direction_pow p hp θ]

/-- Composition gives the actual Puiseux-polynomial phase of the original goal. -/
theorem phase_root_comp (p : ℕ) (hp : 0 < p) (G : Polynomial ℂ) (θ r : ℝ) :
    phaseOnRay 1 G (θ / p) 0 (rootRadius p r) =
      phaseOnRay p G θ ⟨0, hp⟩ r := by
  simp [phaseOnRay, rootOnRay, rootRadius]

/-- The reciprocal chain rule, including the complex ray direction. -/
theorem ray_chain_factor (p : ℕ) (hp : 0 < p) (θ : ℝ) {r : ℝ} (hr : 0 < r) :
    (rootRadiusDerivative p r : ℂ) *
      (Complex.exp (((θ / p : ℝ) : ℂ) * Complex.I) *
        ((p : ℂ) * ray (θ / p) (rootRadius p r) ^ (p - 1))) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
  let u := Complex.exp (((θ / p : ℝ) : ℂ) * Complex.I)
  have hu : u * u ^ (p - 1) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
    exact direction_pow p hp θ
  have hc : (rootRadiusDerivative p r : ℂ) *
      ((p : ℂ) * (rootRadius p r : ℂ) ^ (p - 1)) = 1 := by
    exact_mod_cast rootRadius_chain_factor p hp hr
  change (rootRadiusDerivative p r : ℂ) * (u * ((p : ℂ) *
    ((rootRadius p r : ℂ) * u) ^ (p - 1))) = _
  calc
    _ = ((rootRadiusDerivative p r : ℂ) *
        ((p : ℂ) * (rootRadius p r : ℂ) ^ (p - 1))) * (u * u ^ (p - 1)) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hc, hu, one_mul]

/-- Rational evaluation of the actual ramified matrix, after multiplication
by ds/dr, is exactly the original ray coefficient at genuine nonpoles. -/
theorem coefficient_pullback {m : ℕ} (p : ℕ) (hp : 0 < p)
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ) {r : ℝ} (hr : 0 < r)
    (hpole : ∀ i j, (A i j).denom.eval (ray θ r) ≠ 0) :
    (rootRadiusDerivative p r : ℂ) •
      coefficientOnRay (rationalCoefficient p hp A) (θ / p) (rootRadius p r) =
        coefficientOnRay A θ r := by
  have he := eval_rationalCoefficient p hp A (ray (θ / p) (rootRadius p r))
    (by simpa only [ray_root_pow p hp θ hr.le] using hpole)
  ext i j
  have hij := congrFun (congrFun he i) j
  change RatFunc.eval (RingHom.id ℂ) (ray (θ / p) (rootRadius p r))
      (rationalCoefficient p hp A i j) =
    ((p : ℂ) * ray (θ / p) (rootRadius p r) ^ (p - 1)) *
      RatFunc.eval (RingHom.id ℂ) (ray (θ / p) (rootRadius p r) ^ p) (A i j) at hij
  simp only [Matrix.smul_apply, smul_eq_mul, coefficientOnRay]
  rw [hij, ray_root_pow p hp θ hr.le]
  calc
    _ = ((rootRadiusDerivative p r : ℂ) *
      (Complex.exp (((θ / p : ℝ) : ℂ) * Complex.I) *
        ((p : ℂ) * ray (θ / p) (rootRadius p r) ^ (p - 1)))) *
          RatFunc.eval (RingHom.id ℂ) (ray θ r) (A i j) := by ring
    _ = _ := by rw [ray_chain_factor p hp θ hr]

/-- The phase derivative transforms by the same actual real chain rule. -/
theorem phase_derivative_pullback (p : ℕ) (hp : 0 < p) (G : Polynomial ℂ)
    (θ : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (phaseOnRay p G θ ⟨0, hp⟩) r =
      (rootRadiusDerivative p r : ℂ) *
        deriv (phaseOnRay 1 G (θ / p) 0) (rootRadius p r) := by
  have hh := ((WasowPhaseOrdering.phase_hasDerivAt 1 G (θ / p) 0
    (rootRadius_pos p hr)).differentiableAt.hasDerivAt).scomp r (rootRadius_hasDerivAt p hr)
  have he : (fun t => phaseOnRay 1 G (θ / p) 0 (rootRadius p t)) =
      phaseOnRay p G θ ⟨0, hp⟩ := funext (phase_root_comp p hp G θ)
  change HasDerivAt (fun t => phaseOnRay 1 G (θ / p) 0 (rootRadius p t)) _ r at hh
  rw [he] at hh
  simpa only [Complex.real_smul, smul_eq_mul] using hh.deriv

/-- The two polynomial operator bounds change exponent by exactly `1/p`. -/
theorem rootRadius_rpow (p : ℕ) {r : ℝ} (hr : 0 ≤ r) (K : ℝ) :
    (rootRadius p r) ^ K = r ^ (K / p) := by
  rw [rootRadius, ← Real.rpow_mul hr]
  congr 1
  ring

/-- A finite rational matrix has a genuine common pole-free tail on every ray. -/
theorem eventually_original_pole_free {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ) :
    ∀ᶠ r : ℝ in atTop, ∀ i j, (A i j).denom.eval (ray θ r) ≠ 0 := by
  simp only [Filter.eventually_all]
  intro i j
  obtain ⟨_, _, R, hR, hb⟩ := WasowRational.exists_polynomial_part_tail (A i j)
  filter_upwards [eventually_gt_atTop R] with r hr
  exact (hb (ray θ r) (by rw [WasowRational.norm_ray θ (zero_le_one.trans (hR.trans hr.le))]; exact hr)).1

/-- Descend an actual gauge of the ramified rational system to the original
system. The zero branch is explicit and works at every original angle.
All inverse identities, actual derivatives, nonpoles, and both polynomial
operator bounds are proved for the descended gauge. -/
theorem descend_rayGauge {m : ℕ} (p : ℕ) (hp : 0 < p)
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (G : Fin m → Polynomial ℂ) (θ : ℝ)
    (H : RayGaugeWitness (rationalCoefficient p hp A) (θ / p)
      (fun i => phaseOnRay 1 (G i) (θ / p) 0)) :
    Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (G i) θ ⟨0, hp⟩)) := by
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
    have hd : (rootRadiusDerivative p r : ℂ) •
        Matrix.diagonal (fun i => deriv (phaseOnRay 1 (G i) (θ / p) 0) (rootRadius p r)) =
      Matrix.diagonal (fun i => deriv (phaseOnRay p (G i) θ ⟨0, hp⟩) r) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul,
        phase_derivative_pullback p hp (G i) θ (hrpos hr)]
      split_ifs <;> simp
    exact hh.trans hd

/-- The branch-existential form used by the original normal-form goal. -/
theorem exists_descended_branch {m : ℕ} (p : ℕ) (hp : 0 < p)
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (G : Fin m → Polynomial ℂ) (θ : ℝ)
    (H : RayGaugeWitness (rationalCoefficient p hp A) (θ / p)
      (fun i => phaseOnRay 1 (G i) (θ / p) 0)) :
    ∃ ℓ : Fin p, Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (G i) θ ℓ)) :=
  ⟨⟨0, hp⟩, descend_rayGauge p hp A G θ H⟩

end WasowRamifiedGauge
#print axioms WasowRamifiedGauge.rootRadius_pos
#print axioms WasowRamifiedGauge.rootRadius_pow
#print axioms WasowRamifiedGauge.rootRadius_hasDerivAt
#print axioms WasowRamifiedGauge.rootRadius_chain_factor
#print axioms WasowRamifiedGauge.direction_pow
#print axioms WasowRamifiedGauge.ray_root_pow
#print axioms WasowRamifiedGauge.phase_root_comp
#print axioms WasowRamifiedGauge.ray_chain_factor
#print axioms WasowRamifiedGauge.coefficient_pullback

#print axioms WasowRamifiedGauge.phase_derivative_pullback
#print axioms WasowRamifiedGauge.rootRadius_rpow
#print axioms WasowRamifiedGauge.eventually_original_pole_free
#print axioms WasowRamifiedGauge.descend_rayGauge
#print axioms WasowRamifiedGauge.exists_descended_branch
