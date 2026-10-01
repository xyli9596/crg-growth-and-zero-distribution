import WasowCanonicalRegularGauge
import WasowGlobalExactAssembly

/-! The rational ray normal-form goal is now proved for arbitrary matrices.
One ramification and one normalized polynomial phase family are constructed
before choosing any direction. The gauge is a genuine exact RayGaugeWitness
with two-sided inverse, actual derivatives, nonpoles and polynomial bounds.
This proves the ray-only goal in NormalFormGoal, not all sectorial statements
or Stokes theorems of the original monograph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix.Norms.Operator
namespace WasowRationalNormalForm
open CRGNormalFormGoal WasowLaurentGauge WasowGlobalFormalSquare
variable {m : ℕ}

/-- Every actual global formal normal form is exactly realized on any ray of
the ramified rational system. All regular and residual inputs are constructed. -/
theorem ramified_ray_normal_form
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (F : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    {s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt (WasowRationalAtInfinity.coefficient A) s 0)
    (hcoeff : ∀n, s.coeff n = PowerSeries.coeff n F)
    (W : SquareRealization (differentialCoefficient (WasowRationalAtInfinity.order A) F))
    (φ : ℝ) :
    Nonempty (RayGaugeWitness (WasowRamification.rationalCoefficient W.denominator W.positive A)
      φ (fun i => phaseOnRay 1 (W.normal.phase i) φ 0)) := by
  obtain ⟨L,hL⟩ := WasowCanonicalRegularGauge.exists_uniform_regular_family W.normal
  exact WasowGlobalExactAssembly.exact_of_regularFamily A F ha hcoeff W φ L (hL φ)

/-- Ramified descent preserves the same fixed phase family and gives the
explicit zero branch at every original direction. -/
theorem original_ray_normal_form
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (F : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    {s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt (WasowRationalAtInfinity.coefficient A) s 0)
    (hcoeff : ∀n, s.coeff n = PowerSeries.coeff n F)
    (W : SquareRealization (differentialCoefficient (WasowRationalAtInfinity.order A) F))
    (θ : ℝ) :
    Nonempty (RayGaugeWitness A θ
      (fun i => phaseOnRay W.denominator (W.normal.phase i) θ ⟨0,W.positive⟩)) := by
  obtain ⟨H⟩ := ramified_ray_normal_form A F ha hcoeff W (θ/W.denominator)
  exact WasowRamifiedGauge.descend_rayGauge W.denominator W.positive A W.normal.phase θ H

/-- Arbitrary rational matrices have a fixed normalized finite phase family
and an exact polynomially bounded gauge on every ray. No normal-form data,
regular factor, approximate gauge or remainder estimate is a hypothesis. -/
theorem exists_fixed_phase_normal_form (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) :
    ∃ p : ℕ, ∃ hp : 0<p, ∃ G : Fin m → Polynomial ℂ,
      (∀i, (G i).coeff 0=0) ∧
      ∀ θ : ℝ, Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (G i) θ ⟨0,hp⟩)) := by
  obtain ⟨s,F,ha,hcoeff⟩ := WasowRationalAtInfinity.exists_formal_expansion A
  obtain ⟨W⟩ := exists_square_global_realization F (WasowRationalAtInfinity.order A)
  exact ⟨W.denominator,W.positive,W.normal.phase,W.normal.phase_zero,
    original_ray_normal_form A F ha hcoeff W⟩

/-- The previously uninhabited general rational ray normal-form goal is proved. -/
theorem rational_ray_normal_form : RationalRayNormalFormGoal := by
  intro m _ A
  obtain ⟨p,hp,G,hG,h⟩ := exists_fixed_phase_normal_form A
  exact ⟨p,hp,G,hG,fun θ => ⟨⟨0,hp⟩,h θ⟩⟩

#print axioms ramified_ray_normal_form
#print axioms original_ray_normal_form
#print axioms exists_fixed_phase_normal_form
#print axioms rational_ray_normal_form
end WasowRationalNormalForm
