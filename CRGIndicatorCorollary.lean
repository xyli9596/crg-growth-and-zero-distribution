import CRGIndicatorFinite

/-! The complete first assertion of manuscript Corollary 3.6 for a fixed
possibly nonmonic exponential-polynomial differential equation. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Polynomial
open scoped Topology
namespace CRGIndicatorCorollary
open CRGIndicatorFixedPhases CRGIndicatorAlternatives CRGIndicatorPartition
open CRGFinitePhaseEndgame CRGPhaseDirections

/-- A genuine finite-order transcendental entire solution, with its actual
order and unrestricted continuous indicator. -/
def SolutionIndicatorPair {n : ℕ} (E : EquationData n)
    (x : ℚ × (LevinGrowth.Direction → ℝ)) : Prop :=
  ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ CRGOrder.FiniteOrder f ∧
    (¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z) ∧ E.Solves f ∧
    CRGOrder.IsOrder f (x.1 : ℝ) ∧ LevinGrowth.IsIndicator f (x.1 : ℝ) x.2

/-- Corollary 3.6(1), its finiteness clause: for a fixed actual coefficient
collection only finitely many order/indicator pairs occur. -/
theorem finite_solution_indicator_pairs {n : ℕ} (E : EquationData n) :
    {x | SolutionIndicatorPair E x}.Finite := by
  classical
  obtain ⟨ι, inst, p, hp, P, hP0, hcompare⟩ := E.exists_fixed_phases
  letI := inst
  let d : ι → ℚ := fun i => ((P i).natDegree : ℚ) / (p i : ℚ)
  let C : ℚ → Finset ℂ := fun σ => Finset.univ.image
    (fun i => if (d i : ℝ) = (σ : ℝ) then (P i).leadingCoeff else 0)
  let H : ι → Set (LevinGrowth.Direction → ℝ) := fun i =>
    {h | Continuous h ∧ ∀ θ : ℝ, ∃ c ∈ C (d i),
      h (CRGOrderLevin.angleDirection θ) = leadingReal c (d i : ℝ) θ}
  let I := {i : ι // 0 < d i}
  have hH (i : I) : (H i.val).Finite :=
    CRGIndicatorFinite.finite_continuous_indicators (C (d i.val))
      (by exact_mod_cast i.property)
  have hfin : (⋃ i : I, (fun h => (d i.val, h)) '' H i.val).Finite :=
    Set.finite_iUnion (fun i => (hH i).image _)
  apply hfin.subset
  rintro ⟨σ, h⟩ ⟨f, hf, hfinite, htrans, heq, horder, hi⟩
  obtain ⟨τ, hτ, hoτ, htτ, hman⟩ :=
    CRGTheorem11.of_collected_equation (E.withSolution f heq) hf hfinite htrans
  have hστ : σ = τ := Rat.cast_injective (isOrder_unique horder hoτ)
  subst τ
  obtain ⟨h₀, hcrg₀, hi₀⟩ := hman
  have hh : h₀ = h := by
    funext ζ
    exact EReal.coe_injective ((hi₀ ζ).symm.trans (hi ζ))
  subst h₀
  have hσ := hτ
  have htype := htτ
  have hcrg := hcrg₀
  have hphase := hcompare f hf hfinite htrans heq
  have hdata := ae_rayData_of_phase_comparison p hp P hP0 hphase
  obtain ⟨i, hdi, hoi, _hti⟩ := order_mem_of_ae_rayData hf hfinite htrans d
    (fun i θ => leading (p i) (P i) θ) hdata
  have hσi : σ = d i := Rat.cast_injective (isOrder_unique horder hoi)
  subst σ
  apply mem_iUnion.mpr
  refine ⟨⟨i, hdi⟩, h, ⟨hcrg.1, ?_⟩, rfl⟩
  intro θ
  obtain ⟨j, hj⟩ := indicator_alternatives hf (by exact_mod_cast hdi)
    horder htype p hp P hP0 hphase hcrg hi θ
  refine ⟨if (d j : ℝ) = (d i : ℝ) then (P j).leadingCoeff else 0,
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
  simpa only [d, Rat.cast_div, Rat.cast_natCast] using hj


/-- The finite-pairs conclusion expressed directly in the original nonmonic
ODE, with no CRG or phase assumption in the set being bounded. -/
theorem finite_actual_solution_indicator_pairs {n : ℕ}
    (A : Fin (n+1) → ℂ → ℂ)
    (hA : ∀ j, CRGExponentialCoefficients.IsExponentialPolynomial (A j))
    (htop : ∃ z : ℂ, A (Fin.last n) z ≠ 0) :
    {x : ℚ × (LevinGrowth.Direction → ℝ) |
      ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ CRGOrder.FiniteOrder f ∧
        (¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z) ∧
        SolvesEquation A f ∧ CRGOrder.IsOrder f (x.1 : ℝ) ∧
        LevinGrowth.IsIndicator f (x.1 : ℝ) x.2}.Finite := by
  obtain ⟨E, hE⟩ := exists_fixed_equation_data A hA htop
  apply (finite_solution_indicator_pairs E).subset
  rintro x ⟨f, hf, hfinite, htrans, heq, horder, hi⟩
  exact ⟨f, hf, hfinite, htrans, (hE f).mp heq, horder, hi⟩

/-- Corollary 3.6(1), its ray-partition clause. One finite set of rays works
simultaneously for all solutions of the fixed coefficient collection. On
any interval between these rays the unrestricted indicator has the stated
single harmonic-monomial formula. -/
theorem exists_fixed_indicator_partition {n : ℕ} (E : EquationData n) :
    ∃ R : Finset ℝ, (∀ θ ∈ R, θ ∈ Icc 0 (2 * Real.pi)) ∧
      ∀ f : ℂ → ℂ, Differentiable ℂ f → CRGOrder.FiniteOrder f →
        (¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z) → E.Solves f →
        ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ : ℝ) ∧
          LevinGrowth.FinitePositiveType f (σ : ℝ) ∧
          ∃ h : LevinGrowth.Direction → ℝ, LevinGrowth.DiskRegular f (σ : ℝ) h ∧
            LevinGrowth.IsIndicator f (σ : ℝ) h ∧
            ∀ u v : ℝ, u < v → Ioo u v ⊆ Icc 0 (2 * Real.pi) →
              Disjoint (Ioo u v) (R : Set ℝ) →
              ∃ c : ℂ, ∀ θ ∈ Ioo u v,
                h (CRGOrderLevin.angleDirection θ) = leadingReal c (σ : ℝ) θ := by
  classical
  obtain ⟨ι, inst, p, hp, P, hP0, hcompare⟩ := E.exists_fixed_phases
  letI := inst
  let d : ι → ℚ := fun i => ((P i).natDegree : ℚ) / (p i : ℚ)
  let C : ℚ → Finset ℂ := fun σ => Finset.univ.image
    (fun i => if (d i : ℝ) = (σ : ℝ) then (P i).leadingCoeff else 0)
  let I := {i : ι // 0 < d i}
  let T : Set ℝ := ⋃ i : I, collisionDirections (C (d i.val)) (d i.val : ℝ) 0 (2 * Real.pi)
  have hT : T.Finite := Set.finite_iUnion (fun i =>
    collisionDirections_finite _ (by exact_mod_cast i.property))
  let R := insert 0 (insert (2 * Real.pi) hT.toFinset)
  have hTR : T ⊆ (R : Set ℝ) := by
    intro θ hθ
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hT.mem_toFinset.mpr hθ))
  refine ⟨R, ?_, ?_⟩
  · intro θ hθ
    simp only [R, Finset.mem_insert] at hθ
    rcases hθ with rfl | rfl | hθ
    · exact ⟨le_rfl, by positivity⟩
    · exact ⟨by positivity, le_rfl⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hT.mem_toFinset.mp hθ)
      exact hi.1
  · intro f hf hfinite htrans heq
    have hphase := hcompare f hf hfinite htrans heq
    have hdata := ae_rayData_of_phase_comparison p hp P hP0 hphase
    obtain ⟨i, hdi, horder, htype⟩ := order_mem_of_ae_rayData hf hfinite htrans d
      (fun i θ => leading (p i) (P i) θ) hdata
    obtain ⟨σ, hσ, hoσ, _htσ, hman⟩ :=
      complete_of_finite_phases hf hfinite htrans p hp P hP0 hphase
    have he : σ = d i := Rat.cast_injective (isOrder_unique hoσ horder)
    subst σ
    obtain ⟨h, hcrg, hi⟩ := hman
    refine ⟨d i, hdi, horder, htype, h, hcrg, hi, ?_⟩
    have halt : ∀ θ : ℝ, ∃ c ∈ C (d i),
        h (CRGOrderLevin.angleDirection θ) = leadingReal c (d i : ℝ) θ := by
      intro θ
      obtain ⟨j, hj⟩ := indicator_alternatives hf (by exact_mod_cast hdi)
        horder htype p hp P hP0 hphase hcrg hi θ
      refine ⟨if (d j : ℝ) = (d i : ℝ) then (P j).leadingCoeff else 0,
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
      simpa only [d, Rat.cast_div, Rat.cast_natCast] using hj
    intro u v huv hsub havoid
    have havoid' : Disjoint (Ioo u v)
        (collisionDirections (C (d i)) (d i : ℝ) 0 (2 * Real.pi)) := by
      apply havoid.mono_right
      intro θ hθ
      exact hTR (mem_iUnion.mpr ⟨⟨i, hdi⟩, hθ⟩)
    obtain ⟨c, _hc, heq⟩ := indicator_on_interval (C (d i))
      (by exact_mod_cast hdi) huv hsub havoid'
      (fun θ => h (CRGOrderLevin.angleDirection θ))
      (hcrg.1.comp CRGOrderLevin.continuous_angleDirection) halt
    exact ⟨c, heq⟩

/-- The first assertion applies to the manuscript's original nonmonic
exponential-polynomial coefficients, without any phase or CRG hypothesis. -/
theorem corollary_3_6_part_one {n : ℕ} (A : Fin (n+1) → ℂ → ℂ)
    (hA : ∀ j, CRGExponentialCoefficients.IsExponentialPolynomial (A j))
    (htop : ∃ z : ℂ, A (Fin.last n) z ≠ 0) :
    ∃ E : EquationData n, (∀ f : ℂ → ℂ, SolvesEquation A f ↔ E.Solves f) ∧
      {x | SolutionIndicatorPair E x}.Finite ∧
      ∃ R : Finset ℝ, (∀ θ ∈ R, θ ∈ Icc 0 (2 * Real.pi)) ∧
        ∀ f : ℂ → ℂ, Differentiable ℂ f → CRGOrder.FiniteOrder f →
          (¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z) → SolvesEquation A f →
          ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ : ℝ) ∧
            LevinGrowth.FinitePositiveType f (σ : ℝ) ∧
            ∃ h : LevinGrowth.Direction → ℝ, LevinGrowth.DiskRegular f (σ : ℝ) h ∧
              LevinGrowth.IsIndicator f (σ : ℝ) h ∧
              ∀ u v : ℝ, u < v → Ioo u v ⊆ Icc 0 (2 * Real.pi) →
                Disjoint (Ioo u v) (R : Set ℝ) →
                ∃ c : ℂ, ∀ θ ∈ Ioo u v,
                  h (CRGOrderLevin.angleDirection θ) = leadingReal c (σ : ℝ) θ := by
  obtain ⟨E, hE⟩ := exists_fixed_equation_data A hA htop
  obtain ⟨R, hR, hpartition⟩ := exists_fixed_indicator_partition E
  exact ⟨E, hE, finite_solution_indicator_pairs E, R, hR,
    fun f hf hfinite htrans heq => hpartition f hf hfinite htrans ((hE f).mp heq)⟩

#print axioms finite_solution_indicator_pairs
#print axioms finite_actual_solution_indicator_pairs
#print axioms exists_fixed_indicator_partition
#print axioms corollary_3_6_part_one
end CRGIndicatorCorollary
