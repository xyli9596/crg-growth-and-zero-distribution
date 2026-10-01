import WasowRegularSingular
import WasowRealization
import WasowRamification
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Exact realization of constant regular-singular matrix blocks. The actual
matrix power has its chain-rule derivative and a genuine two-sided inverse.
This includes arbitrary repeated eigenvalues and nilpotent constant parts. -/
set_option autoImplicit false
noncomputable section
open Matrix Set Filter
open scoped Topology
namespace WasowRegularGauge
open WasowRegularSingular CRGNormalFormGoal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rayLog_hasDerivAt (θ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (rayLog θ) ((r : ℂ)⁻¹) r := by
  convert! ((Real.hasDerivAt_log hr).ofReal_comp).add_const ((θ : ℂ)*Complex.I) using 1
  simp only [Complex.ofReal_inv]

/-- Actual entrywise real derivative of the regular-singular matrix power. -/
theorem rayPower_hasDerivAt (G : Matrix ι ι ℂ) (θ : ℝ) {r : ℝ}
    (hr : r ≠ 0) (i j : ι) :
    HasDerivAt (fun t => rayPower G θ t i j)
      ((((r : ℂ)⁻¹) • (G * rayPower G θ r)) i j) r := by
  let B := matrixOperator G
  have h := (hasDerivAt_exp_smul_const' B (rayLog θ r)).clm_apply
    (hasDerivAt_const (rayLog θ r) (Pi.single j (1 : ℂ)))
  have hh := hasDerivAt_pi.mp (h.scomp r (rayLog_hasDerivAt θ hr)) i
  convert! hh using 1
  simp only [map_zero, add_zero, Pi.smul_apply,
    mul_apply_eq_comp, smul_eq_mul]
  change (r : ℂ)⁻¹ * (G * rayPower G θ r) i j =
      (r : ℂ)⁻¹ * G.mulVec (NormedSpace.exp (rayLog θ r • B) (Pi.single j 1)) i
  congr 1

omit [DecidableEq ι] in
/-- Matrix action preserves actual matrix multiplication. -/
theorem matrixOperator_mul (D G : Matrix ι ι ℂ) :
    matrixOperator (D*G) = matrixOperator D * matrixOperator G := by
  ext x i
  exact congrFun (Matrix.mulVec_mulVec x D G).symm i

/-- The constant matrix action returns the original matrix in coordinates. -/
theorem toMatrix_matrixOperator (G : Matrix ι ι ℂ) :
    LinearMap.toMatrix' (matrixOperator G).toLinearMap = G := by
  ext i j
  simp [matrixOperator, LinearMap.toMatrix'_apply, Matrix.mulVec_single]

/-- Constant matrices commuting with the residue also commute with its
actual exponential gauge. -/
theorem commute_rayPower (D G : Matrix ι ι ℂ) (hDG : Commute D G) (θ r : ℝ) :
    Commute D (rayPower G θ r) := by
  have h : Commute (matrixOperator D) (matrixOperator G) := by
    change matrixOperator D * matrixOperator G = matrixOperator G * matrixOperator D
    rw [← matrixOperator_mul, ← matrixOperator_mul, hDG.eq]
  have hs : Commute (matrixOperator D) (rayLog θ r • matrixOperator G) := by
    change matrixOperator D * (rayLog θ r • matrixOperator G) =
      (rayLog θ r • matrixOperator G) * matrixOperator D
    apply ContinuousLinearMap.ext
    intro x
    change matrixOperator D (rayLog θ r • matrixOperator G x) =
      rayLog θ r • matrixOperator G (matrixOperator D x)
    rw [map_smul]
    exact congrArg (fun v => rayLog θ r • v) (congrArg (fun U => U x) h.eq)
  have he := congrArg (fun U : (ι → ℂ) →L[ℂ] (ι → ℂ) =>
    LinearMap.toMatrix' U.toLinearMap) hs.exp_right.eq
  simp only [ContinuousLinearMap.toLinearMap_mul, LinearMap.toMatrix'_mul,
    toMatrix_matrixOperator] at he
  exact he

/-- Continuity of the actual gauge on every nonzero radial parameter. -/
theorem rayPower_continuousAt (G : Matrix ι ι ℂ) (θ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContinuousAt (rayPower G θ) r := by
  exact continuousAt_pi.mpr (fun i => continuousAt_pi.mpr
    (fun j => (rayPower_hasDerivAt G θ hr i j).continuousAt))

/-- The displayed inverse really is the negative-residue power. -/
theorem rayPowerInverse_eq (G : Matrix ι ι ℂ) (θ r : ℝ) :
    rayPowerInverse G θ r = rayPower (-G) θ r := by
  have hneg : matrixOperator (-G) = -matrixOperator G := by
    ext x i
    simp [matrixOperator]
  simp only [rayPowerInverse, rayPower, hneg, smul_neg]

theorem rayPowerInverse_continuousAt (G : Matrix ι ι ℂ) (θ : ℝ)
    {r : ℝ} (hr : r ≠ 0) : ContinuousAt (rayPowerInverse G θ) r := by
  rw [show rayPowerInverse G θ = rayPower (-G) θ from funext (rayPowerInverse_eq G θ)]
  exact rayPower_continuousAt (-G) θ hr

/-- A rational matrix whose actual ray coefficient is `G/r` has a complete
zero-phase gauge with polynomial bounds in both directions. -/
theorem exists_constant_regular_rayGauge {m : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (G : Matrix (Fin m) (Fin m) ℂ)
    (θ : ℝ) (a : ℝ) (ha : 1 ≤ a)
    (hpoles : ∀ r > a, ∀ i j, (A i j).denom.eval (ray θ r) ≠ 0)
    (hcoeff : ∀ r > a, coefficientOnRay A θ r = ((r : ℂ)⁻¹) • G) :
    Nonempty (RayGaugeWitness A θ (fun _ _ => 0)) := by
  obtain ⟨C,K,hC,hK,hbound⟩ := exists_polynomial_bounds G θ
  refine ⟨{
    T := rayPower G θ
    S := rayPowerInverse G θ
    T' := fun r => ((r : ℂ)⁻¹) • (G * rayPower G θ r)
    R := a, C := C, K := K
    R_pos := zero_lt_one.trans_le ha
    C_pos := hC
    K_nonneg := hK
    pole_free := hpoles
    T_derivative := fun r hr i j => rayPower_hasDerivAt G θ
      (ne_of_gt ((zero_lt_one.trans_le ha).trans hr)) i j
    inverse_left := fun r _ => rayPowerInverse_mul_rayPower G θ r
    inverse_right := fun r _ => rayPower_mul_rayPowerInverse G θ r
    T_bound := fun r hr x => (hbound r (ha.trans hr.le) x).1
    S_bound := fun r hr x => (hbound r (ha.trans hr.le) x).2
    gauge_identity := ?_ }⟩
  intro r hr
  rw [hcoeff r hr, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  simp

end WasowRegularGauge
#print axioms WasowRegularGauge.rayLog_hasDerivAt
#print axioms WasowRegularGauge.rayPower_hasDerivAt
#print axioms WasowRegularGauge.exists_constant_regular_rayGauge

#print axioms WasowRegularGauge.matrixOperator_mul
#print axioms WasowRegularGauge.toMatrix_matrixOperator
#print axioms WasowRegularGauge.commute_rayPower
#print axioms WasowRegularGauge.rayPower_continuousAt
#print axioms WasowRegularGauge.rayPowerInverse_eq
#print axioms WasowRegularGauge.rayPowerInverse_continuousAt
