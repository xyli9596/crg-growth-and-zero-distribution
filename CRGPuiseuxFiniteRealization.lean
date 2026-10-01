import CRGAsymptoticCoefficientPullback
import WasowGlobalFiniteRealization

/-! Automatic global formal reduction and finite analytic realization for
complete sectorial asymptotic coefficients. The coefficient formal series may
diverge. All phase, ramification, gauge, and inverse choices precede any ray
filter and requested residual order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Filter Asymptotics
namespace CRGPuiseuxFiniteRealization
open CRGAsymptoticCoefficientCompleteExpansion CRGAsymptoticCoefficientPullback
open WasowLaurentGauge WasowLaurentRamification WasowGlobalFormalCanonical
open WasowGlobalFormalSquare WasowLaurentClearing WasowLaurentTruncation
open WasowLaurentFiniteRealization WasowRamifiedCoefficient
open WasowGlobalFiniteRealization
variable {m : ℕ}

/-- Pole clearing and ramification transport the actual complete expansion
to exactly the cleared formal coefficient chosen by the global reduction. -/
theorem clearedCoefficient_completeExpansion
    {l l' : Filter ℂ} (hl : l ≤ 𝓝[≠] (0 : ℂ))
    {a : ℂ → Mat (m := m)} {A : PowerSeries (Mat (m := m))}
    (ha : CompleteExpansion l' a A) (q : ℕ)
    (W : SquareRealization (differentialCoefficient q A))
    (ht : Tendsto (fun z : ℂ => z^W.denominator) l l') :
    CompleteExpansion l (clearedCoefficient a W.denominator q (clearingOrder W))
      (clearAt (clearingOrder W)
        (pullback W.denominator W.positive (differentialCoefficient q A))) := by
  have hp := completeExpansion_power_pullback (hl.trans nhdsWithin_le_nhds)
    ha W.denominator W.positive ht
  have hx := completeExpansion_monomial (hl.trans nhdsWithin_le_nhds) hp
    (-(W.denominator : ℂ)) (clearingOrder W - pole W.denominator q)
  have hb := clearingOrder_bounds W
  rw [clearAt_pullback W.denominator q (clearingOrder W) W.positive A hb.2.1 hb.2.2.2,
    mul_smul_comm]
  exact hx

/-- All analytic assertions for one finite actual Laurent gauge. The actual
source is the true pullback of a, including its differential Jacobian. -/
structure FiniteControl (l : Filter ℂ) (a : ℂ → Mat (m := m))
    (A : PowerSeries (Mat (m := m))) (q : ℕ)
    (W : SquareRealization (differentialCoefficient q A)) (k : ℕ) : Prop where
  estimate : residual (clearingOrder W) (coefficient W.normal) W.change.G W.change.H
    (clearedCoefficient a W.denominator q (clearingOrder W)) k =O[l]
      (fun z : ℂ => ‖z‖^k)
  inverseBounds : ∃ C : ℝ, 0<C ∧ ∀ᶠ z in l,
    (gauge (clearingOrder W) W.change.G W.change.H k z).det ≠ 0 ∧
    (gauge (clearingOrder W) W.change.G W.change.H k z)⁻¹ *
      gauge (clearingOrder W) W.change.G W.change.H k z = 1 ∧
    gauge (clearingOrder W) W.change.G W.change.H k z *
      (gauge (clearingOrder W) W.change.G W.change.H k z)⁻¹ = 1 ∧
    ‖gauge (clearingOrder W) W.change.G W.change.H k z‖ ≤ C / ‖z‖^poleOrder W.change.G ∧
    ‖(gauge (clearingOrder W) W.change.G W.change.H k z)⁻¹‖ ≤ C / ‖z‖^poleOrder W.change.H ∧
    DifferentiableAt ℂ (gauge (clearingOrder W) W.change.G W.change.H k) z ∧
    ramifiedCoefficient W.denominator q a z *
      gauge (clearingOrder W) W.change.G W.change.H k z =
      deriv (gauge (clearingOrder W) W.change.G W.change.H k) z +
        gauge (clearingOrder W) W.change.G W.change.H k z *
          (target (clearingOrder W) (coefficient W.normal) W.change.G W.change.H k z +
            residual (clearingOrder W) (coefficient W.normal) W.change.G W.change.H
              (clearedCoefficient a W.denominator q (clearingOrder W)) k z)

/-- The original complete expansion is the only coefficient expansion input;
no convergence, finite gauge, transformed remainder, or inverse is assumed. -/
theorem finiteControl_of_square
    {l l' : Filter ℂ} (hl : l ≤ 𝓝[≠] (0 : ℂ))
    {a : ℂ → Mat (m := m)} {A : PowerSeries (Mat (m := m))}
    (ha : CompleteExpansion l' a A) (q : ℕ)
    (W : SquareRealization (differentialCoefficient q A))
    (ht : Tendsto (fun z : ℂ => z^W.denominator) l l') (k : ℕ) :
    FiniteControl l a A q W k := by
  have hb := clearingOrder_bounds W
  have hc := clearedCoefficient_completeExpansion hl ha q W ht
  obtain ⟨hr,C,hC,hbound⟩ := finite_realization_of_completeExpansion hl
    _ _ _ _ (clearingOrder W) hb.1 hb.2.1 hb.2.2.1
    W.change.GH W.change.HG W.change.equation hc k
  refine ⟨hr,C,hC,?_⟩
  filter_upwards [hbound,
    (show ∀ᶠ z in l, z≠0 from Filter.Eventually.filter_mono hl self_mem_nhdsWithin)] with z hz hzne
  refine ⟨hz.1,hz.2.1,hz.2.2.1,hz.2.2.2.1,hz.2.2.2.2.1,hz.2.2.2.2.2.1,?_⟩
  simpa only [actualCoefficient_cleared a W.denominator q (clearingOrder W) hb.2.2.2 hzne]
    using hz.2.2.2.2.2.2

/-- An arbitrary full formal matrix coefficient determines one ramification,
one finite polynomial phase family, one Laurent gauge and one formal inverse.
Every compatible closed-subsector approach then realizes these fixed choices
to every residual order. No output choices depend on the solution or the ray. -/
theorem exists_global_finite_realization
    {l' : Filter ℂ} {a : ℂ → Mat (m := m)} {A : PowerSeries (Mat (m := m))}
    (ha : CompleteExpansion l' a A) (q : ℕ) :
    ∃ W : SquareRealization (differentialCoefficient q A),
      ∀ l : Filter ℂ, l ≤ 𝓝[≠] (0 : ℂ) →
        Tendsto (fun z : ℂ => z^W.denominator) l l' →
        ∀ k : ℕ, FiniteControl l a A q W k := by
  obtain ⟨W⟩ := exists_square_global_realization A q
  exact ⟨W,fun l hl ht k => finiteControl_of_square hl ha q W ht k⟩

#print axioms clearedCoefficient_completeExpansion
#print axioms finiteControl_of_square
#print axioms exists_global_finite_realization
end CRGPuiseuxFiniteRealization
