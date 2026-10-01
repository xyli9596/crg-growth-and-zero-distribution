import WasowGlobalFormalSquare
import WasowLaurentFiniteRealization
import WasowAnalyticPowerPullback
import WasowRamifiedCoefficient

/-! Automatic finite analytic realization of the complete formal reduction.
The original coefficient germ is the only analytic input. The full formal
reduction chooses one ramification, one finite phase family, one Laurent gauge
and its formal inverse before any requested residual order or ray. Each finite
truncation then has a true matrix inverse and arbitrarily high residual order.
This is an approximate canonical system, not yet the exact asymptotic witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Filter Set Asymptotics MeasureTheory
namespace WasowGlobalFiniteRealization
open WasowLaurentGauge WasowLaurentRamification WasowGlobalFormalCanonical
open WasowGlobalFormalSquare WasowLaurentClearing WasowLaurentTruncation
open WasowLaurentFiniteRealization WasowRamifiedCoefficient
variable {m : ℕ}

local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by
    simp_rw [Matrix.linfty_opNNNorm_def]
    fun_prop

/-- The actual differential coefficient after t ↦ t^p, including its Jacobian. -/
def ramifiedCoefficient (p q : ℕ) (a : ℂ → Mat (m := m)) (z : ℂ) : Mat (m := m) :=
  (-(p : ℂ) * z ^ (-(pole p q : ℤ))) • a (z ^ p)

/-- A common clearing chosen from the complete global formal data, before N. -/
def clearingOrder {A : PowerSeries (Mat (m := m))} {q : ℕ}
    (W : SquareRealization (differentialCoefficient q A)) : ℕ :=
  max (commonOrder (pullback W.denominator W.positive (differentialCoefficient q A))
    (coefficient W.normal)) (pole W.denominator q)

/-- Explicit analytic numerator obtained solely from the original analytic germ. -/
def clearedCoefficient (a : ℂ → Mat (m := m)) (p q h : ℕ) (z : ℂ) : Mat (m := m) :=
  (-(p : ℂ) * z ^ (h - pole p q)) • a (z ^ p)

theorem clearingOrder_bounds {A : PowerSeries (Mat (m := m))} {q : ℕ}
    (W : SquareRealization (differentialCoefficient q A)) :
    0 < clearingOrder W ∧
    poleOrder (pullback W.denominator W.positive (differentialCoefficient q A)) ≤ clearingOrder W ∧
    poleOrder (coefficient W.normal) ≤ clearingOrder W ∧
    pole W.denominator q ≤ clearingOrder W := by
  obtain ⟨hpos, hleft, hright⟩ := commonOrder_bounds
    (pullback W.denominator W.positive (differentialCoefficient q A)) (coefficient W.normal)
  unfold clearingOrder
  omega

/-- Clearing the known pole preserves precisely the original ramified ODE. -/
theorem actualCoefficient_cleared (a : ℂ → Mat (m := m)) (p q h : ℕ)
    (hh : pole p q ≤ h) {z : ℂ} (hz : z ≠ 0) :
    actualCoefficient h (clearedCoefficient a p q h) z = ramifiedCoefficient p q a z := by
  unfold actualCoefficient clearedCoefficient ramifiedCoefficient
  rw [smul_smul]
  congr 1
  calc
    z ^ (-(h : ℤ)) * (-(p : ℂ) * z ^ (h - pole p q)) =
        -(p : ℂ) * (z ^ (-(h : ℤ)) * z ^ ((h - pole p q : ℕ) : ℤ)) := by
      rw [zpow_natCast]
      ring
    _ = -(p : ℂ) * z ^ (-(pole p q : ℤ)) := by
      rw [← zpow_add₀ hz]
      congr 2
      rw [Nat.cast_sub hh]
      ring

/-- No analytic compatibility remains to be supplied after the global formal
reduction: its cleared source is the actual pulled-back original Taylor series. -/
theorem clearedCoefficient_expansion {a : ℂ → Mat (m := m)}
    {s : FormalMultilinearSeries ℂ ℂ (Mat (m := m))}
    (ha : HasFPowerSeriesAt a s 0) (A : PowerSeries (Mat (m := m)))
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n A) (q : ℕ)
    (W : SquareRealization (differentialCoefficient q A)) :
    let h := clearingOrder W
    let p := W.denominator
    let t := WasowAnalyticPowerPullback.monomialF (-(p : ℂ)) (h - pole p q)
      (WasowAnalyticPowerPullback.expandF p s)
    HasFPowerSeriesAt (clearedCoefficient a p q h) t 0 ∧
    (∀ n, t.coeff n = PowerSeries.coeff n
      (clearAt h (pullback p W.positive (differentialCoefficient q A)))) := by
  dsimp only
  have hb := clearingOrder_bounds W
  have hx := WasowAnalyticPowerPullback.analytic_formal_cleared_pullback ha A hcoeff
    W.denominator W.positive (-(W.denominator : ℂ)) (clearingOrder W - pole W.denominator q)
  refine ⟨hx.1, ?_⟩
  intro n
  rw [clearAt_pullback W.denominator q (clearingOrder W) W.positive A hb.2.1 hb.2.2.2,
    mul_smul_comm]
  exact hx.2 n

/-- All analytic assertions for one finite truncation. The differential
coefficient is the explicit pullback of a, rather than an unrelated germ. -/
structure FiniteControl (a : ℂ → Mat (m := m)) (A : PowerSeries (Mat (m := m)))
    (q : ℕ) (W : SquareRealization (differentialCoefficient q A)) (h k : ℕ) : Prop where
  estimate : residual h (coefficient W.normal) W.change.G W.change.H
    (clearedCoefficient a W.denominator q h) k =O[𝓝[≠] (0 : ℂ)]
      (fun z : ℂ => ‖z‖ ^ k)
  inverseBounds : ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
    (gauge h W.change.G W.change.H k z).det ≠ 0 ∧
    (gauge h W.change.G W.change.H k z)⁻¹ * gauge h W.change.G W.change.H k z = 1 ∧
    gauge h W.change.G W.change.H k z * (gauge h W.change.G W.change.H k z)⁻¹ = 1 ∧
    ‖gauge h W.change.G W.change.H k z‖ ≤ C / ‖z‖ ^ poleOrder W.change.G ∧
    ‖(gauge h W.change.G W.change.H k z)⁻¹‖ ≤ C / ‖z‖ ^ poleOrder W.change.H ∧
    DifferentiableAt ℂ (gauge h W.change.G W.change.H k) z ∧
    ramifiedCoefficient W.denominator q a z * gauge h W.change.G W.change.H k z =
      deriv (gauge h W.change.G W.change.H k) z +
        gauge h W.change.G W.change.H k z *
          (target h (coefficient W.normal) W.change.G W.change.H k z +
            residual h (coefficient W.normal) W.change.G W.change.H
              (clearedCoefficient a W.denominator q h) k z)
  smallTails : 2 ≤ k → ∀ (u : ℂ), ‖u‖ = 1 → ∀ ε : ℝ, 0 < ε →
    ∃ R : ℝ, 1 ≤ R ∧
      ContinuousOn (fun r : ℝ => residual h (coefficient W.normal) W.change.G W.change.H
        (clearedCoefficient a W.denominator q h) k (u*(r:ℂ)⁻¹)) (Ici R) ∧
      IntegrableOn (fun r : ℝ => residual h (coefficient W.normal) W.change.G W.change.H
        (clearedCoefficient a W.denominator q h) k (u*(r:ℂ)⁻¹)) (Ici R) ∧
      (∫ r in Ici R, ‖residual h (coefficient W.normal) W.change.G W.change.H
        (clearedCoefficient a W.denominator q h) k (u*(r:ℂ)⁻¹)‖) < ε

/-- Every square global formal reduction has the genuine analytic finite
realization from the original fixed Taylor germ, to every requested order. -/
theorem finiteControl_of_square {a : ℂ → Mat (m := m)}
    {s : FormalMultilinearSeries ℂ ℂ (Mat (m := m))}
    (ha : HasFPowerSeriesAt a s 0) (A : PowerSeries (Mat (m := m)))
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n A) (q : ℕ)
    (W : SquareRealization (differentialCoefficient q A)) (k : ℕ) :
    FiniteControl a A q W (clearingOrder W) k := by
  have hb := clearingOrder_bounds W
  obtain ⟨hc, hmatch⟩ := clearedCoefficient_expansion ha A hcoeff q W
  have hfin := finite_realization _ _ _ _ (clearingOrder W) hb.1 hb.2.1 hb.2.2.1
    W.change.GH W.change.HG W.change.equation hc hmatch k
  refine ⟨hfin.1, ?_, ?_⟩
  · obtain ⟨C, hC, hbound⟩ := hfin.2
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound, self_mem_nhdsWithin] with z hz hzne
    refine ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1, ?_⟩
    simpa only [actualCoefficient_cleared a W.denominator q (clearingOrder W) hb.2.2.2 hzne]
      using hz.2.2.2.2.2.2
  · intro hk u hu ε hε
    exact residual_small_ray_tail _ _ _ _ (clearingOrder W) hb.1 hb.2.1 hb.2.2.1
      W.change.GH W.change.equation hc hmatch k hk hu hε

/-- Automatic capstone: no ramification, phases, Laurent gauge, or inverse
are hypotheses. They and h are fixed before the arbitrary precision k and ray. -/
theorem exists_global_finite_realization {a : ℂ → Mat (m := m)}
    {s : FormalMultilinearSeries ℂ ℂ (Mat (m := m))}
    (ha : HasFPowerSeriesAt a s 0) (A : PowerSeries (Mat (m := m)))
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n A) (q : ℕ) :
    ∃ W : SquareRealization (differentialCoefficient q A), ∃ h : ℕ,
      h = clearingOrder W ∧ 0 < h ∧ ∀ k : ℕ, FiniteControl a A q W h k := by
  obtain ⟨W⟩ := exists_square_global_realization A q
  exact ⟨W, clearingOrder W, rfl, (clearingOrder_bounds W).1,
    finiteControl_of_square ha A hcoeff q W⟩

/-- For rational systems the explicit coefficient is exactly the pullback
under x=t^(-p), with the genuine derivative factor -p*t^(-p-1). -/
theorem ramifiedCoefficient_rational
    (B : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (p : ℕ)
    {z : ℂ} (hz : z ≠ 0) :
    ramifiedCoefficient p (WasowRationalAtInfinity.order B)
      (WasowRationalAtInfinity.coefficient B) z =
      (-(p : ℂ) * z ^ (-(p : ℤ) - 1)) •
        B.map (RatFunc.eval (RingHom.id ℂ) ((z ^ p)⁻¹)) := by
  unfold ramifiedCoefficient
  rw [WasowRationalAtInfinity.coefficient_eq B (pow_ne_zero _ hz), smul_smul]
  congr 1
  calc
    (-(p : ℂ) * z ^ (-(pole p (WasowRationalAtInfinity.order B) : ℤ))) *
        (z ^ p) ^ WasowRationalAtInfinity.order B =
      -(p : ℂ) * (z ^ (-(pole p (WasowRationalAtInfinity.order B) : ℤ)) *
        z ^ ((p * WasowRationalAtInfinity.order B : ℕ) : ℤ)) := by
      rw [zpow_natCast, pow_mul]
      ring
    _ = -(p : ℂ) * z ^ (-(p : ℤ) - 1) := by
      rw [← zpow_add₀ hz]
      congr 2
      simp only [pole, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring

/-- Every rational matrix automatically supplies the original analytic germ
and Taylor data, hence the same all-order finite realization. -/
theorem exists_rational_global_finite_realization
    (B : Matrix (Fin m) (Fin m) (RatFunc ℂ)) :
    ∃ (s : FormalMultilinearSeries ℂ ℂ (Mat (m := m)))
      (A : PowerSeries (Mat (m := m))),
      HasFPowerSeriesAt (WasowRationalAtInfinity.coefficient B) s 0 ∧
      (∀ n, s.coeff n = PowerSeries.coeff n A) ∧
      ∃ W : SquareRealization (differentialCoefficient (WasowRationalAtInfinity.order B) A),
        ∃ h : ℕ, h = clearingOrder W ∧ 0 < h ∧ ∀ k : ℕ,
          FiniteControl (WasowRationalAtInfinity.coefficient B) A
            (WasowRationalAtInfinity.order B) W h k := by
  obtain ⟨s, A, hs, hcoeff⟩ := WasowRationalAtInfinity.exists_formal_expansion B
  exact ⟨s, A, hs, hcoeff,
    exists_global_finite_realization hs A hcoeff (WasowRationalAtInfinity.order B)⟩

#print axioms clearingOrder_bounds
#print axioms actualCoefficient_cleared
#print axioms clearedCoefficient_expansion
#print axioms finiteControl_of_square
#print axioms exists_global_finite_realization
#print axioms ramifiedCoefficient_rational
#print axioms exists_rational_global_finite_realization
end WasowGlobalFiniteRealization
