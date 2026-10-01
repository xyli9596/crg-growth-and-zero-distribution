import CRGPolynomialKernelRamification
import CRGWatsonSourceExpansion
import CRGPuiseuxCoordinates

set_option autoImplicit false
noncomputable section
open Filter Set Polynomial Asymptotics
open scoped Topology
namespace CRGPolynomialKernel
open CRGExponentialCoefficients CRGPuiseuxCoordinates

/-- Actual angular geometry of one coefficient sign cell. All fields concern
polynomial phase values and holomorphic root germs, with no formal expansions. -/
structure Cell {n : ℕ} (D : CoefficientData n) where
  denominator : ℕ
  positive : 0<denominator
  angles : Set ℝ
  growing : Fin D.count → Bool
  root : Fin D.count → ℂ → ℂ
  root_analytic : ∀ell,growing ell=false → AnalyticAt ℂ (root ell) 0
  root_zero : ∀ell,growing ell=false → root ell 0=0
  growing_geometry : ∀ell,growing ell=true → ∀θ∈angles,
    Tendsto (fun x=>‖(normalizedExponent (D.phase ell)).eval (originalPoint denominator x)‖)
      (CRGAsymptoticCoefficientRayTail.rayFilter (WasowGlobalRayData.direction (θ/denominator))) atTop ∧
    ∃c : ℝ,0<c ∧ ∀ᶠx in
      CRGAsymptoticCoefficientRayTail.rayFilter (WasowGlobalRayData.direction (θ/denominator)),
      c*‖(normalizedExponent (D.phase ell)).eval (originalPoint denominator x)‖≤
        ((normalizedExponent (D.phase ell)).eval (originalPoint denominator x)).re
  decaying_geometry : ∀ell,growing ell=false → ∀θ∈angles,
    Tendsto (fun x=>‖-(D.phase ell).eval (originalPoint denominator x)‖)
      (CRGAsymptoticCoefficientRayTail.rayFilter (WasowGlobalRayData.direction (θ/denominator))) atTop ∧
    (∃c : ℝ,0<c ∧ ∀ᶠx in
      CRGAsymptoticCoefficientRayTail.rayFilter (WasowGlobalRayData.direction (θ/denominator)),
      c*‖-(D.phase ell).eval (originalPoint denominator x)‖≤
        (-(D.phase ell).eval (originalPoint denominator x)).re) ∧
    (∀ᶠx in CRGAsymptoticCoefficientRayTail.rayFilter (WasowGlobalRayData.direction (θ/denominator)),
      root ell x=(-(D.phase ell).eval (originalPoint denominator x))^(-(D.power ell:ℂ)⁻¹))

end CRGPolynomialKernel
