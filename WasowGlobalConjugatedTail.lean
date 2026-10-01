import WasowGlobalFiniteRealization
import WasowLaurentChainTail
import WasowLaurentExactAssemblyData

/-! The actual global finite residual supplies the complete small-tail input
of exact Volterra realization after the regular factor and true ray Jacobian. -/
set_option autoImplicit false
noncomputable section
open Filter Set Asymptotics MeasureTheory
open scoped Topology Matrix.Norms.Operator
namespace WasowGlobalConjugatedTail
open WasowGlobalFiniteRealization WasowGlobalFormalSquare WasowGlobalFormalCanonical
open WasowLaurentGauge WasowLaurentTruncation WasowLaurentClearing WasowLaurentFiniteRealization
variable {m : ℕ}

def error {A : PowerSeries (Mat (m := m))} {q : ℕ}
    (a : ℂ → Mat (m := m)) (W : SquareRealization (differentialCoefficient q A)) (k : ℕ) :
    ℂ → Mat (m := m) :=
  residual (clearingOrder W) (coefficient W.normal) W.change.G W.change.H
    (clearedCoefficient a W.denominator q (clearingOrder W)) k

theorem eventually_error_continuousAt {a : ℂ → Mat (m := m)}
    {s : FormalMultilinearSeries ℂ ℂ (Mat (m := m))}
    (ha : HasFPowerSeriesAt a s 0) (A : PowerSeries (Mat (m := m)))
    (hcoeff : ∀n, s.coeff n = PowerSeries.coeff n A) (q : ℕ)
    (W : SquareRealization (differentialCoefficient q A)) (k : ℕ) :
    ∀ᶠ z in 𝓝[≠] (0:ℂ), ContinuousAt (error a W k) z := by
  obtain ⟨hc,_⟩ := clearedCoefficient_expansion ha A hcoeff q W
  have hb := clearingOrder_bounds W
  exact WasowLaurentTail.eventually_remainder_continuousAt
    (poleOrder W.change.G) (poleOrder W.change.H) (clearingOrder W)
    (truncationOrder (clearingOrder W) W.change.G W.change.H k) hb.1 hc.analyticAt
    (cleared W.change.G) (cleared W.change.H) (clearAt (clearingOrder W) (coefficient W.normal))
    (cleared_mul _ _ W.change.GH) (by unfold truncationOrder; omega)

/-- The required small conjugated remainder is derived from the original
analytic germ and actual global formal data; it is not an assembly hypothesis. -/
theorem smallConjugatedTails {a : ℂ → Mat (m := m)}
    {s : FormalMultilinearSeries ℂ ℂ (Mat (m := m))}
    (ha : HasFPowerSeriesAt a s 0) (A : PowerSeries (Mat (m := m)))
    (hcoeff : ∀n, s.coeff n = PowerSeries.coeff n A) (q : ℕ)
    (W : SquareRealization (differentialCoefficient q A))
    (T S : ℝ → Mat (m := m)) (L : ℕ) (ctrl : WasowPolynomialTail.Control T S L)
    {u : ℂ} (hu : ‖u‖=1) :
    WasowLaurentExactAssembly.SmallConjugatedTails T S
      (WasowLaurentRayEquation.coefficientOnRay (error a W (2*L+2)) u) := by
  intro Rmin ε hε
  exact WasowLaurentChainTail.exists_small_tail T S L ctrl hu
    (eventually_error_continuousAt ha A hcoeff q W (2*L+2))
    (finiteControl_of_square ha A hcoeff q W (2*L+2)).estimate Rmin hε

#print axioms eventually_error_continuousAt
#print axioms smallConjugatedTails
end WasowGlobalConjugatedTail
