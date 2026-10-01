import WasowRecursiveTree
import WasowPhaseTree
import WasowScalarPhase

/-! Extract fixed Puiseux phase families from the ACTUAL finite full-series
reduction tree. The scalar eigenvalues, integer ranks and ramification factors
are read from its verified edges, never chosen from a ray. Dimension identities
follow from its actual coordinate inverses. This is the phase algebra of that
formal tree; analytic realization of every formal edge is a separate question.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace WasowRecursivePhases
open CRGNormalFormGoal WasowFormalSuccessor WasowFormalNormalization
open WasowFormalSplit WasowReductionTermination WasowScalarPhase

/-- The spectral child dimensions exhaust the input dimension, as proved by
the true spectral basis and each child's two-sided coordinate inverses. -/
theorem family_dimension {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Series ι} {rank : ℕ} (F : Family A rank) :
    ∑ a : Spectrum A, dim (F.child a).shape = Fintype.card ι := by
  calc
    _ = ∑ a : Spectrum A, (WasowLeadingBlocks.blockSize
        (Matrix.toLin' (PowerSeries.constantCoeff A)) a + 1) := by
      apply Finset.sum_congr rfl
      intro a _
      exact (data_dimension (F.normalization a)).trans (Fintype.card_fin _)
    _ = Fintype.card (WasowArbitraryFormalBlocks.BlockIndex A) := by
      simp [WasowArbitraryFormalBlocks.BlockIndex, WasowLeadingBlocks.MatrixIndex,
        WasowMultiShiftReduction.Index, Fintype.card_sigma]
    _ = Fintype.card ι :=
      (WasowPencilCoordinates.card_eq_of_two_sided_inverse
        (WasowLeadingBlocks.changeMatrix (PowerSeries.constantCoeff A))
        (WasowLeadingBlocks.inverseChangeMatrix (PowerSeries.constantCoeff A))
        (WasowLeadingBlocks.change_mul_inverse _)
        (WasowLeadingBlocks.inverse_mul_change _)).symm

/-- Forget only the coordinate gauges, retaining precisely the scalar phase
extraction and ramification operations from the real recursive reduction. -/
def toPhaseTree {old : FormalState} : WasowRecursiveTree.Tree old → WasowPhaseTree.Tree
  | .regular old d _ =>
      .ramify d.slope.den d.slope.den_pos (.regular (dim old.shape))
  | .single _ next i _ child =>
      .ramify i.slope.den i.slope.den_pos
        (.scalar (rankPhase next.shape.rank i.eigenvalue)
          (rankPhase_coeff_zero _ _) (toPhaseTree child))
  | .split old d _ rank _ _ _ _ _ children =>
      .ramify d.slope.den d.slope.den_pos
        (.split (Fintype.card (Spectrum (rawSeries old d.slope))) (fun j =>
          let a := (Fintype.equivFin (Spectrum (rawSeries old d.slope))).symm j
          .scalar (rankPhase rank a.val) (rankPhase_coeff_zero _ _) (toPhaseTree (children a))))

theorem toPhaseTree_dimension {old : FormalState} (t : WasowRecursiveTree.Tree old) :
    WasowPhaseTree.dimension (toPhaseTree t) = dim old.shape := by
  induction t with
  | regular old d h => rfl
  | single old next i data child ih =>
      change WasowPhaseTree.dimension (toPhaseTree child) = dim old.shape
      rw [ih]
      exact dim_eq_of_step (singleData_step data)
  | split old d hc rank he family a b hab children ih =>
      change (∑ j : Fin (Fintype.card (Spectrum (rawSeries old d.slope))),
        WasowPhaseTree.dimension (toPhaseTree (children
          ((Fintype.equivFin (Spectrum (rawSeries old d.slope))).symm j)))) = dim old.shape
      simp_rw [ih]
      exact ((Fintype.equivFin (Spectrum (rawSeries old d.slope))).symm.sum_comp
        (fun c => dim (family.child c).shape)).trans (family_dimension family)

/-- The initial spectral split and its actual scalar eigenvalues are retained
as well; this extraction is available for arbitrary full matrix series. -/
def reductionPhaseTree {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Series ι} {rank : ℕ} (R : WasowRecursiveTree.Reduction A rank) : WasowPhaseTree.Tree :=
  .split (Fintype.card (Spectrum A)) (fun j =>
    let a := (Fintype.equivFin (Spectrum A)).symm j
    .scalar (rankPhase rank a.val) (rankPhase_coeff_zero _ _) (toPhaseTree (R.trees a)))

theorem reductionPhaseTree_dimension {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Series ι} {rank : ℕ} (R : WasowRecursiveTree.Reduction A rank) :
    WasowPhaseTree.dimension (reductionPhaseTree R) = Fintype.card ι := by
  change (∑ j : Fin (Fintype.card (Spectrum A)),
    WasowPhaseTree.dimension (toPhaseTree (R.trees ((Fintype.equivFin (Spectrum A)).symm j)))) = _
  simp_rw [toPhaseTree_dimension]
  exact ((Fintype.equivFin (Spectrum A)).symm.sum_comp
    (fun c => dim (R.initial.child c).shape)).trans (family_dimension R.initial)

def phaseFamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Series ι} {rank : ℕ} (R : WasowRecursiveTree.Reduction A rank) :
    Fin (Fintype.card ι) → Polynomial ℂ :=
  fun j => WasowPhaseTree.family (reductionPhaseTree R)
    (Fin.cast (reductionPhaseTree_dimension R).symm j)

/-- Evaluation follows the recorded scalar/ramification/splitting operations
of the supplied genuine formal reduction. The cast merely numbers its columns. -/
def phaseValue {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Series ι} {rank : ℕ} (R : WasowRecursiveTree.Reduction A rank)
    (θ r : ℝ) (j : Fin (Fintype.card ι)) : ℂ :=
  WasowPhaseTree.phaseValue (reductionPhaseTree R) θ r
    (Fin.cast (reductionPhaseTree_dimension R).symm j)

theorem phaseFamily_coeff_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Series ι} {rank : ℕ} (R : WasowRecursiveTree.Reduction A rank)
    (j : Fin (Fintype.card ι)) : (phaseFamily R j).coeff 0 = 0 :=
  WasowPhaseTree.family_coeff_zero _ _

theorem phaseValue_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Series ι} {rank : ℕ} (R : WasowRecursiveTree.Reduction A rank)
    (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) (j : Fin (Fintype.card ι)) :
    phaseValue R θ r j = phaseOnRay (WasowPhaseTree.denominator (reductionPhaseTree R))
      (phaseFamily R j) θ ⟨0,WasowPhaseTree.denominator_pos _⟩ r :=
  WasowPhaseTree.phaseValue_eq _ θ hr _

/-- An arbitrary complete matrix series has a genuine finite formal reduction
and a single normalized phase family, all selected before the ray direction.
This is a formal phase-family existence theorem, not yet a ray-gauge theorem. -/
theorem exists_reduction_fixed_phases {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Series ι) (rank : ℕ) :
    ∃ R : WasowRecursiveTree.Reduction A rank,
      ∃ (p : ℕ) (hp : 0 < p) (F : Fin (Fintype.card ι) → Polynomial ℂ),
        (∀ j, (F j).coeff 0 = 0) ∧ ∀ θ r, 0 ≤ r → ∀ j,
          phaseValue R θ r j = phaseOnRay p (F j) θ ⟨0,hp⟩ r := by
  obtain ⟨R⟩ := WasowRecursiveTree.exists_reduction A rank
  exact ⟨R, WasowPhaseTree.denominator (reductionPhaseTree R), WasowPhaseTree.denominator_pos _,
    phaseFamily R, phaseFamily_coeff_zero R, fun θ r hr j => phaseValue_eq R θ hr j⟩

end WasowRecursivePhases
#print axioms WasowRecursivePhases.family_dimension
#print axioms WasowRecursivePhases.toPhaseTree_dimension
#print axioms WasowRecursivePhases.reductionPhaseTree_dimension
#print axioms WasowRecursivePhases.phaseFamily_coeff_zero
#print axioms WasowRecursivePhases.phaseValue_eq
#print axioms WasowRecursivePhases.exists_reduction_fixed_phases
