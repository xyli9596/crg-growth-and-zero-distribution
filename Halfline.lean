import MixedVolterra
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Interval.Set.Infinite

/-! Concrete instantiation on the manuscript's real half-line, with its induced
Lebesgue measure. This proves existence and the normalized-column limit for the
actual integral equation. Differentiation into the ODE remains separate. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
attribute [local instance] Measure.Subtype.measureSpace
namespace CRGHalfline

local instance halflineNullSingleton (r₀ : ℝ) :
    NullSingletonClass (volume : Measure (Ici r₀)) := by
  refine ⟨fun x => ?_⟩
  rw [Measure.Subtype.volume_def, comap_subtype_coe_apply measurableSet_Ici]
  simp

/-- All completeness, order/filter, and non-atomic measure instances used by the
mixed-operator proof are discharged by mathlib on this actual half-line. -/
theorem exists_column (m : ℕ) (r₀ : ℝ)
    (mode : Fin m → Bool) (q : Fin m → Ici r₀ → ℂ)
    (hq : ∀ i, Continuous (q i))
    (hord : ∀ i, if mode i then Antitone (fun t => (q i t).re)
      else Monotone (fun t => (q i t).re))
    (hdecay : ∀ i, mode i = true → Tendsto (fun r => (q i r).re) atTop atBot)
    (R : Ici r₀ → (Fin m → ℂ) →L[ℂ] (Fin m → ℂ))
    (hR : Continuous R) (hL1 : Integrable (fun s => ‖R s‖))
    (hsmall : (∫ s : Ici r₀, ‖R s‖) < 1) (v : Fin m → ℂ) :
    ∃ u : Ici r₀ →ᵇ (Fin m → ℂ),
      (∀ r i, u r i = v i +
        ∫ s : Ici r₀, MixedVolterra.kernel (mode i) (q i) r s * (R s (u s)) i) ∧
      Tendsto u atTop (𝓝 v) := by
  obtain ⟨u, hu, _hunique⟩ := MixedVolterra.exists_unique_fixed_point
    (volume : Measure (Ici r₀)) mode q hq hord R hR (fun s => ‖R s‖) hL1
    (fun _ => le_rfl) (BoundedContinuousFunction.const (Ici r₀) v) hsmall
  refine ⟨u, ?_, MixedVolterra.fixed_point_tendsto
    volume mode q hq hord R hR (fun s => ‖R s‖) hL1 (fun _ => le_rfl) hdecay v u hu⟩
  intro r i
  have hx := congrArg (fun f : Ici r₀ →ᵇ (Fin m → ℂ) => f r i) hu
  exact hx

#print axioms exists_column
end CRGHalfline
