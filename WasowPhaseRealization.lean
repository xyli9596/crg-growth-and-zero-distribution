import WasowPhaseOrdering
import WasowRealization

/-! Automatic phase-direction data for exact analytic realization. The tail
and modes are constructed from the fixed Puiseux-polynomial phases; all later
tails retain the same directions. The remaining inputs are actual approximate
gauge data and a small continuous L1 remainder. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
namespace WasowPhaseRealization
open CRGNormalFormGoal WasowRealization WasowPhaseOrdering

def OrderedOn {ι : Type*} (Q : ι → ℝ → ℂ) (mode : ι → ι → Bool) (a : ℝ) : Prop :=
  (∀ j i, if mode j i then Antitone (fun t : Ici a => (Q i t-Q j t).re)
    else Monotone (fun t : Ici a => (Q i t-Q j t).re)) ∧
  (∀ j i, mode j i = true →
    Tendsto (fun t : Ici a => (Q i t-Q j t).re) atTop atBot)

/-- Integration directions already valid on one tail remain valid on every
later tail, including their actual decay limits. -/
theorem orderedOn_mono {ι : Type*} {Q : ι → ℝ → ℂ} {mode : ι → ι → Bool}
    {a b : ℝ} (hab : a ≤ b) (h : OrderedOn Q mode a) : OrderedOn Q mode b := by
  let e : Ici b → Ici a := fun t => ⟨t,hab.trans t.property⟩
  have he : Monotone e := fun _ _ hxy => hxy
  have ht : Tendsto e atTop atTop := tendsto_Ici_atTop.mpr
    (show Tendsto (fun t : Ici b => (t : ℝ)) atTop atTop from
      tendsto_Ici_atTop.mp tendsto_id)
  constructor
  · intro j i
    have ho := h.1 j i
    cases hm : mode j i <;> simp only [hm, Bool.false_eq_true, ↓reduceIte] at ho ⊢
    · exact fun _ _ hxy => ho (he hxy)
    · exact fun _ _ hxy => ho (he hxy)
  · intro j i hm
    exact (h.2 j i hm).comp ht

/-- Construct one common phase-ordering threshold and reuse its directions
at every later radius. No exceptional ray angle is excluded. -/
theorem exists_persistent_phase_ordering {ι : Type*} [Fintype ι]
    (p : ℕ) (hp : 0 < p) (G : ι → Polynomial ℂ) (θ : ℝ) (ℓ : Fin p) (a₀ : ℝ) :
    ∃ a : ℝ, a₀ ≤ a ∧ 1 ≤ a ∧ ∃ mode : ι → ι → Bool,
      ∀ b : ℝ, a ≤ b → OrderedOn (fun i => phaseOnRay p (G i) θ ℓ) mode b := by
  obtain ⟨a,ha,mode,ho,hd⟩ := exists_common_phase_ordering p hp G θ ℓ
  exact ⟨max a₀ a, le_max_left _ _, ha.trans (le_max_right _ _), mode,
    fun b hb => orderedOn_mono ((le_max_right _ _).trans hb) ⟨ho,hd⟩⟩

/-- Once the actual approximate gauge and integrable remainder are supplied,
finite Puiseux phases themselves provide every direction and derivative input
needed for an exact gauge. The same phase polynomials work for every angle. -/
theorem exists_exact_rayGauge_of_puiseux_phases {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (p : ℕ) (hp : 0 < p) (G : Fin m → Polynomial ℂ) (θ : ℝ) (ℓ : Fin p) (a₀ : ℝ) :
    ∃ a : ℝ, a₀ ≤ a ∧ 1 ≤ a ∧ ∀ b : ℝ, a ≤ b →
      ∀ R : Ici b → (Fin m → ℂ) →L[ℂ] (Fin m → ℂ),
      ApproximateRayGauge A θ b (fun i => deriv (phaseOnRay p (G i) θ ℓ)) R →
      Continuous R → Integrable (fun t : Ici b => ‖R t‖) →
      (∫ t : Ici b, ‖R t‖) < 1 →
      Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (G i) θ ℓ)) := by
  obtain ⟨a,ha₀,ha,mode,hm⟩ := exists_persistent_phase_ordering p hp G θ ℓ a₀
  refine ⟨a,ha₀,ha,?_⟩
  intro b hb R H hR hL1 hsmall
  apply exists_exact_rayGauge A θ b (fun i => phaseOnRay p (G i) θ ℓ)
    (fun i => deriv (phaseOnRay p (G i) θ ℓ)) R H mode
    (fun i => phase_continuous p hp (G i) θ ℓ) ?_ (hm b hb).1 (hm b hb).2 hR hL1 hsmall
  intro i r hr
  have hh := WasowPhaseOrdering.phase_hasDerivAt p (G i) θ ℓ
    (show 0 < r from lt_of_lt_of_le zero_lt_one (ha.trans (hb.trans hr.le)))
  exact hh.deriv.symm ▸ hh

end WasowPhaseRealization

#print axioms WasowPhaseRealization.orderedOn_mono
#print axioms WasowPhaseRealization.exists_persistent_phase_ordering
#print axioms WasowPhaseRealization.exists_exact_rayGauge_of_puiseux_phases
