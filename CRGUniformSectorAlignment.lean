import CRGPuiseuxMonic

/-! Closed-subsector source conditions for manuscript Proposition 5.1.
The inverse coordinate x=z^(-1/p) and a common clearing power encode
Laurent-Puiseux series with finitely many positive powers. Every finite
remainder is controlled uniformly on each closed angular subinterval.
The ray-packet conversion is a theorem, not an additional source premise. -/
set_option autoImplicit false
noncomputable section
open Filter Set Asymptotics MeasureTheory Polynomial
open scoped Topology
namespace CRGUniformSectorAlignment
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientRayTail
open CRGPuiseuxRayReduction WasowGlobalRayData WasowLaurentRayEquation

/-- All inverse radii tend to infinity while the angle ranges throughout
the indicated closed interval; Big-O on this filter is uniform in angle. -/
def closedSubsectorFilter (p : ℕ) (u v : ℝ) : Filter ℂ :=
  Filter.map (fun t : ℝ × ℝ => inverseRay (direction (t.1/p)) t.2)
    ((Filter.principal (Icc u v)) ×ˢ (atTop : Filter ℝ))

theorem rayFilter_le_closedSubsector (p : ℕ) {u v θ : ℝ} (hθ : θ ∈ Icc u v) :
    rayFilter (direction (θ/p)) ≤ closedSubsectorFilter p u v := by
  have hc : Tendsto (fun _ : ℝ => θ) atTop (Filter.principal (Icc u v)) := by
    rw [tendsto_principal]
    exact Eventually.of_forall (fun _ => hθ)
  have ht := hc.prodMk (tendsto_id : Tendsto (fun r : ℝ => r) atTop atTop)
  have hm := Filter.map_mono (m := fun t : ℝ × ℝ => inverseRay (direction (t.1/p)) t.2) ht
  simpa only [rayFilter,closedSubsectorFilter,Filter.map_map,Function.comp_def,id_eq] using hm

/-- The manuscript's stronger sector source condition in the same cleared
inverse coordinate used by the analytic proof. No solution, phase, gauge,
derivative bound or residual estimate is included in these coefficient data. -/
structure UniformSector {n : ℕ} (a : Fin (n+1) → ℂ → ℂ) where
  denominator : ℕ
  positive : 0 < denominator
  clearing : ℕ
  left : ℝ
  right : ℝ
  ordered : left < right
  multiplier : ℂ → ℂ
  series : Fin (n+1) → PowerSeries ℂ
  some_nonzero : ∃ j, series j ≠ 0
  regular : ∀ u v : ℝ, u < v → Icc u v ⊆ Ioo left right →
    ∀ᶠ x in closedSubsectorFilter denominator u v,
      AnalyticAt ℂ multiplier x ∧ multiplier x ≠ 0
  expansion : ∀ u v : ℝ, u < v → Icc u v ⊆ Ioo left right → ∀ j,
    CompleteExpansion (closedSubsectorFilter denominator u v)
      (clearedCoefficients a denominator clearing multiplier j) (series j)

theorem UniformSector.ray_data {n : ℕ} {a : Fin (n+1) → ℂ → ℂ}
    (S : UniformSector a) (θ : ℝ) (hθ : θ ∈ Ioo S.left S.right) :
    (∀ᶠ x in rayFilter (direction (θ/S.denominator)),
      ContinuousAt S.multiplier x ∧ S.multiplier x ≠ 0) ∧
    ∀ j, CompleteExpansion (rayFilter (direction (θ/S.denominator)))
      (clearedCoefficients a S.denominator S.clearing S.multiplier j) (S.series j) := by
  let u := (S.left+θ)/2
  let v := (θ+S.right)/2
  have huv : u < v := by dsimp [u,v]; linarith [S.ordered]
  have hsub : Icc u v ⊆ Ioo S.left S.right := by
    intro t ht
    dsimp [u,v] at ht
    constructor <;> linarith [hθ.1,hθ.2,ht.1,ht.2]
  have ht : θ ∈ Icc u v := by dsimp [u,v]; constructor <;> linarith [hθ.1,hθ.2]
  have hl := rayFilter_le_closedSubsector S.denominator ht
  refine ⟨?_,?_⟩
  · filter_upwards [(S.regular u v huv hsub).filter_mono hl] with x hx
    exact ⟨hx.1.differentiableAt.continuousAt,hx.2⟩
  · intro j N
    exact (S.expansion u v huv hsub j N).mono hl

def UniformSector.toRaySector {n : ℕ} {a : Fin (n+1) → ℂ → ℂ}
    (S : UniformSector a) : CRGPuiseuxSector.Sector a where
  denominator := S.denominator
  positive := S.positive
  clearing := S.clearing
  angles := Ioo S.left S.right
  multiplier := S.multiplier
  series := S.series
  some_nonzero := S.some_nonzero
  multiplier_continuous := fun θ hθ => ((S.ray_data θ hθ).1).mono (fun _ h => h.1)
  multiplier_nonzero := fun θ hθ => ((S.ray_data θ hθ).1).mono (fun _ h => h.2)
  expansion := fun θ hθ => (S.ray_data θ hθ).2

/-- Proposition 5.1 from uniform closed-subsector expansions for the original
monic equation. The phase family is fixed by the coefficient packets and
the complete analytic growth and ray-tail conclusions are proved. -/
theorem proposition_5_1_uniform {n : ℕ} {ι : Type*} [Fintype ι]
    (a : Fin n → ℂ → ℂ)
    (S : ι → UniformSector (CRGPuiseuxMonic.fullCoefficient a))
    (ha : ∀ j, Differentiable ℂ (a j))
    (hcover : ∀ᵐ θ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),
      ∃ i, θ ∈ Ioo (S i).left (S i).right)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬∃ P : Polynomial ℂ, ∀ z, f z = P.eval z)
    (heq : CRGExponentialCoefficients.SolvesMonicEquation n a f) :
    ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ:ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ:ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ:ℝ) ∧
      CRGPuiseuxProposition.PhaseComparison (fun i => (S i).toRaySector) f := by
  exact CRGPuiseuxMonic.proposition_5_1_monic a (fun i => (S i).toRaySector)
    ha hcover f hf hfinite htrans heq

#print axioms rayFilter_le_closedSubsector
#print axioms UniformSector.ray_data
#print axioms proposition_5_1_uniform
end CRGUniformSectorAlignment
