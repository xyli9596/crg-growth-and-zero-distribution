import WasowLaurentClearing
import WasowLaurentRemainder
import WasowLaurentTail

/-! Finite actual realization of a genuine Laurent differential gauge.
The actual analytic input c is the pole-cleared coefficient: its Taylor series
is clearAt h A at any sufficient common pole order h. Only finite polynomials are evaluated. The
formal gauge and target are never assumed convergent. -/
set_option autoImplicit false
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Filter Set Asymptotics MeasureTheory
namespace WasowLaurentFiniteRealization
open WasowLaurentGauge WasowLaurentClearing WasowLaurentTruncation
variable {m : ℕ}
abbrev Mat := Matrix (Fin m) (Fin m) ℂ
abbrev LMat := Matrix (Fin m) (Fin m) L

local instance : ContinuousENorm (Mat (m := m)) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by
    simp_rw [Matrix.linfty_opNNNorm_def]
    fun_prop

def truncationOrder (h : ℕ) (G H : LMat (m := m)) (k : ℕ) : ℕ :=
  poleOrder G + poleOrder H + h + k

/-- A concrete finite Laurent-polynomial gauge. Its inverse below is the
actual matrix inverse, rather than a truncation of the formal inverse. -/
def gauge (h : ℕ) (G H : LMat (m := m)) (k : ℕ) : ℂ → Mat (m := m) :=
  WasowLaurentInverse.finiteGauge (cleared G) (poleOrder G) (truncationOrder h G H k)

def actualCoefficient (h : ℕ) (c : ℂ → Mat (m := m)) (z : ℂ) : Mat (m := m) :=
  z ^ (-(h : ℤ)) • c z

def target (h : ℕ) (B G H : LMat (m := m)) (k : ℕ) (z : ℂ) : Mat (m := m) :=
  z ^ (-(h : ℤ)) •
    WasowMatrixPolynomial.eval (PowerSeries.trunc (truncationOrder h G H k)
      (clearAt h B)) z

def residual (h : ℕ) (B G H : LMat (m := m)) (c : ℂ → Mat (m := m)) (k : ℕ) : ℂ → Mat (m := m) :=
  WasowLaurentRemainder.remainder (poleOrder G) h
    (truncationOrder h G H k) c (cleared G) (clearAt h B)

theorem gauge_differentiableAt (h : ℕ) (G H : LMat (m := m)) (k : ℕ)
    {z : ℂ} (hz : z ≠ 0) : DifferentiableAt ℂ (gauge h G H k) z :=
  (WasowLaurentInverse.finiteGauge_hasDerivAt _ _ _ hz).differentiableAt

/-- Exact transformed equation for the actual finite matrices. -/
theorem transformed_equation (h : ℕ) (B G H : LMat (m := m)) (c : ℂ → Mat (m := m)) (k : ℕ)
    (z : ℂ) (hinv : gauge h G H k z * (gauge h G H k z)⁻¹ = 1) :
    actualCoefficient h c z * gauge h G H k z =
      deriv (gauge h G H k) z +
        gauge h G H k z * (target h B G H k z + residual h B G H c k z) := by
  unfold residual WasowLaurentRemainder.remainder
  change _ = deriv (gauge h G H k) z +
    gauge h G H k z * (target h B G H k z +
      (gauge h G H k z)⁻¹ * WasowLaurentActualResidual.rawDefect
        (poleOrder G) h (truncationOrder h G H k) c
        (cleared G) (clearAt h B) z)
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  unfold WasowLaurentActualResidual.rawDefect
  rw [WasowLaurentRemainder.finiteGauge_eq]
  change _ = deriv (gauge h G H k) z +
    (gauge h G H k z * target h B G H k z +
      (actualCoefficient h c z * gauge h G H k z -
        gauge h G H k z * target h B G H k z - deriv (gauge h G H k) z))
  abel

/-- Arbitrary residual order from only the actual Laurent equation and inverse
pair; the cleared equation and pole budget are derived automatically. -/
theorem residual_isBigO (A B G H : LMat (m := m))
    (h : ℕ) (hh : 0 < h) (hA : poleOrder A ≤ h) (hB : poleOrder B ≤ h)
    (hGH : G*H=1) (heq : GaugeEquation A G B)
    {c : ℂ → Mat (m := m)} {s : FormalMultilinearSeries ℂ ℂ (Mat (m := m))}
    (hc : HasFPowerSeriesAt c s 0)
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n (clearAt h A))
    (k : ℕ) :
    residual h B G H c k =O[𝓝[≠] (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ k) := by
  exact WasowLaurentRemainder.remainder_isBigO (poleOrder G) (poleOrder H)
    h k hh hc (clearAt h A) (cleared G)
    (cleared H) (clearAt h B) hcoeff (cleared_mul G H hGH)
    (equation_clearAt _ hh A B G hA hB heq)

/-- For every requested order k, N=a+b+h+k is an actual finite realization.
The determinant, true inverse, derivative, transformed equation, and residual
estimate are all proved. The pole exponents a,b do not depend on k. -/
theorem finite_realization (A B G H : LMat (m := m))
    (h : ℕ) (hh : 0 < h) (hA : poleOrder A ≤ h) (hB : poleOrder B ≤ h)
    (hGH : G*H=1) (hHG : H*G=1) (heq : GaugeEquation A G B)
    {c : ℂ → Mat (m := m)} {s : FormalMultilinearSeries ℂ ℂ (Mat (m := m))}
    (hc : HasFPowerSeriesAt c s 0)
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n (clearAt h A))
    (k : ℕ) :
    residual h B G H c k =O[𝓝[≠] (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ k) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      (gauge h G H k z).det ≠ 0 ∧
      (gauge h G H k z)⁻¹ * gauge h G H k z = 1 ∧
      gauge h G H k z * (gauge h G H k z)⁻¹ = 1 ∧
      ‖gauge h G H k z‖ ≤ C / ‖z‖ ^ poleOrder G ∧
      ‖(gauge h G H k z)⁻¹‖ ≤ C / ‖z‖ ^ poleOrder H ∧
      DifferentiableAt ℂ (gauge h G H k) z ∧
      actualCoefficient h c z * gauge h G H k z =
        deriv (gauge h G H k) z +
          gauge h G H k z * (target h B G H k z + residual h B G H c k z) := by
  refine ⟨residual_isBigO A B G H h hh hA hB hGH heq hc hcoeff k, ?_⟩
  obtain ⟨C,hC,hb⟩ := WasowLaurentInverse.eventually_inverse_bounds_of_laurent G H
    hGH hHG (truncationOrder h G H k) (by unfold truncationOrder; omega)
  refine ⟨C,hC,?_⟩
  filter_upwards [hb, self_mem_nhdsWithin] with z hz hzne
  exact ⟨hz.1,hz.2.1,hz.2.2.1,hz.2.2.2.1,hz.2.2.2.2,
    gauge_differentiableAt h G H k hzne,
    transformed_equation h B G H c k z hz.2.2.1⟩

/-- Every unit direction has an actual continuous, integrable residual tail
with arbitrarily small L1 norm when the requested order is at least two. -/
theorem residual_small_ray_tail (A B G H : LMat (m := m))
    (h : ℕ) (hh : 0 < h) (hA : poleOrder A ≤ h) (hB : poleOrder B ≤ h)
    (hGH : G*H=1) (heq : GaugeEquation A G B)
    {c : ℂ → Mat (m := m)} {s : FormalMultilinearSeries ℂ ℂ (Mat (m := m))}
    (hc : HasFPowerSeriesAt c s 0)
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n (clearAt h A))
    (k : ℕ) (hk : 2 ≤ k) {u : ℂ} (hu : ‖u‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (fun r : ℝ => residual h B G H c k (u*(r:ℂ)⁻¹)) (Ici R) ∧
      IntegrableOn (fun r : ℝ => residual h B G H c k (u*(r:ℂ)⁻¹)) (Ici R) ∧
      (∫ r in Ici R, ‖residual h B G H c k (u*(r:ℂ)⁻¹)‖) < ε := by
  exact WasowLaurentTail.remainder_small_ray_tail (poleOrder G) (poleOrder H)
    h k hh hk hc (clearAt h A) (cleared G)
    (cleared H) (clearAt h B) hcoeff (cleared_mul G H hGH)
    (equation_clearAt _ hh A B G hA hB heq) hu hε

/-- Default realization uses the automatically computed common pole order. -/
theorem finite_realization_common (A B G H : LMat (m := m))
    (hGH : G*H=1) (hHG : H*G=1) (heq : GaugeEquation A G B)
    {c : ℂ → Mat (m := m)} {s : FormalMultilinearSeries ℂ ℂ (Mat (m := m))}
    (hc : HasFPowerSeriesAt c s 0)
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n (clearAt ((commonOrder A B)) A))
    (k : ℕ) :
    residual (commonOrder A B) B G H c k =O[𝓝[≠] (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ k) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      (gauge (commonOrder A B) G H k z).det ≠ 0 ∧
      (gauge (commonOrder A B) G H k z)⁻¹ * gauge (commonOrder A B) G H k z = 1 ∧
      gauge (commonOrder A B) G H k z * (gauge (commonOrder A B) G H k z)⁻¹ = 1 ∧
      ‖gauge (commonOrder A B) G H k z‖ ≤ C / ‖z‖ ^ poleOrder G ∧
      ‖(gauge (commonOrder A B) G H k z)⁻¹‖ ≤ C / ‖z‖ ^ poleOrder H ∧
      DifferentiableAt ℂ (gauge (commonOrder A B) G H k) z ∧
      actualCoefficient (commonOrder A B) c z * gauge (commonOrder A B) G H k z =
        deriv (gauge (commonOrder A B) G H k) z +
          gauge (commonOrder A B) G H k z * (target (commonOrder A B) B G H k z + residual (commonOrder A B) B G H c k z) := by
  obtain ⟨hh,hA,hB⟩ := commonOrder_bounds A B
  exact finite_realization A B G H (commonOrder A B) hh hA hB hGH hHG heq hc hcoeff k

#print axioms finite_realization_common

#print axioms gauge_differentiableAt
#print axioms transformed_equation
#print axioms residual_isBigO
#print axioms finite_realization
#print axioms residual_small_ray_tail
end WasowLaurentFiniteRealization
