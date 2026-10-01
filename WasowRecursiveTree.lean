import WasowFormalSplit
import WasowFormalSpectrum

/-! Finite trees of actual full-series reductions. Every internal edge records
its full differential gauge relation; regular leaves retain their entire
formal series. This does not assert convergence of those leaf series or a
single global near-identity gauge for the original coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace WasowRecursiveTree
open WasowFormalSuccessor WasowFormalNormalization WasowMultiShiftReduction
open WasowOrderedShearing WasowShearingLeading WasowFormalShearing

/-- The slope is selected from actual coefficient support. Its stopping
alternative and its continuing feedback are both part of the proved output. -/
structure SlopeData (old : FormalState) where
  slope : ℚ
  positive : 0 < slope
  bounded : slope ≤ (old.shape.rank : ℚ)+1
  weights : ∀ k i j, flatCoefficients old.shape.sizes (coefficients old) k i j ≠ 0 →
    0 ≤ weightedDegree slope k i j
  feedback : slope = (old.shape.rank : ℚ)+1 ∨
    ∃ i j, j ≤ i ∧ leadingMatrix (flatCoefficients old.shape.sizes (coefficients old)) slope i j ≠ 0

theorem exists_slopeData (old : FormalState) : Nonempty (SlopeData old) := by
  obtain ⟨σ, hp, hb, hw, hf⟩ := exists_slope_with_leading_feedback
    (flatCoefficients old.shape.sizes (coefficients old)) old.shape.rank
    (flat_initial_shape old.shape.sizes (coefficients old)
      (by simpa only [coefficients, PowerSeries.coeff_zero_eq_constantCoeff_apply] using old.leading))
  refine ⟨⟨σ, hp, ?_, hw, ?_⟩⟩
  · exact_mod_cast hb
  · simpa only [Nat.cast_add, Nat.cast_one] using hf

theorem slope_supported {old : FormalState} (d : SlopeData old) :
    Supported (flattenSeries old) d.slope.den d.slope.num.toNat := by
  apply supported_of_weightedDegree _ _ d.slope.den_ne_zero
  intro k a b hab
  rw [slope_num_div_den d.slope d.positive.le]
  exact d.weights k a b hab

theorem numerator_le {old : FormalState} (d : SlopeData old) :
    d.slope.num.toNat ≤ d.slope.den*(old.shape.rank+1) := by
  have hp : (0 : ℚ) < d.slope.den := by exact_mod_cast d.slope.den_pos
  have hb : ((d.slope.num.toNat : ℕ) : ℚ)/d.slope.den ≤ (old.shape.rank : ℚ)+1 := by
    rw [slope_num_div_den d.slope d.positive.le]
    exact d.bounded
  have hh := (div_le_iff₀ hp).mp hb
  have hh' : ((d.slope.num.toNat : ℕ) : ℚ) ≤ (d.slope.den : ℚ)*((old.shape.rank : ℚ)+1) := by
    simpa only [mul_comm] using hh
  exact_mod_cast hh'

/-- The exact full-series edge relation applies also in the stopping branch;
the derivative correction is retained even when its order becomes zero. -/
theorem full_shearing_identity {old : FormalState} (d : SlopeData old)
    (a b : Fin (∑ j, (old.shape.sizes j+1))) :
    PowerSeries.X^(d.slope.num.toNat*(a.val+1)) *
      WasowPowerSeries.entry (rawSeries old d.slope)
        ((flatten old.shape.sizes).symm a) ((flatten old.shape.sizes).symm b) =
      PowerSeries.C (d.slope.den : ℂ) * PowerSeries.X^(d.slope.num.toNat*b.val) *
        PowerSeries.expand d.slope.den d.slope.den_ne_zero
          (WasowPowerSeries.entry (flattenSeries old) a b) +
      (if a=b then PowerSeries.X^(d.slope.den*(old.shape.rank+1)+1) *
        PowerSeries.derivative ℂ (PowerSeries.X^(d.slope.num.toNat*a.val)) else 0) := by
  have he : WasowPowerSeries.entry (rawSeries old d.slope)
      ((flatten old.shape.sizes).symm a) ((flatten old.shape.sizes).symm b) =
      WasowPowerSeries.entry (ramifiedSeries (flattenSeries old) d.slope.den d.slope.den_ne_zero
        d.slope.num.toNat old.shape.rank) a b := by
    apply PowerSeries.ext
    intro k
    simp [rawSeries, WasowPowerSeries.coeff_entry, Matrix.reindex_apply]
  rw [he]
  exact ramifiedSeries_clear_powers _ _ _ _ _ (slope_supported d) (numerator_le d) a b

/-- The stopping leaf has the genuine regular-singular exponent `-1`.
Its coefficient is the full `rawSeries`, not just its constant coefficient. -/
theorem stopping_rank {old : FormalState} (d : SlopeData old)
    (hstop : d.slope = (old.shape.rank : ℚ)+1) :
    (d.slope.den : ℚ)*((old.shape.rank : ℚ)+1-d.slope)-1 = -1 := by
  rw [hstop]
  ring

/-- The complete finite operation tree. Branches retain both global block
splitting data and all actual component normalization equations. -/
inductive Tree : FormalState → Type
  | regular (old : FormalState) (d : SlopeData old)
      (stopping : d.slope = (old.shape.rank : ℚ)+1) : Tree old
  | single (old next : FormalState) (i : ContinuingInput old)
      (data : SingleData old next i) (child : Tree next) : Tree old
  | split (old : FormalState) (d : SlopeData old)
      (continuing : d.slope < (old.shape.rank : ℚ)+1)
      (rank : ℕ) (rank_update : (rank : ℚ) =
        (d.slope.den : ℚ)*((old.shape.rank : ℚ)+1-d.slope)-1)
      (family : WasowFormalSplit.Family (rawSeries old d.slope) rank)
      (a b : WasowFormalSplit.Spectrum (rawSeries old d.slope)) (distinct : a ≠ b)
      (children : ∀ c, Tree (family.child c)) : Tree old

/-- All recursive children decrease the established dimension/mass/rank measure. -/
def Smaller (next old : FormalState) : Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
    (WasowReductionTermination.measure next.shape) (WasowReductionTermination.measure old.shape)

theorem smaller_wellFounded : WellFounded Smaller :=
  InvImage.wf FormalState.shape WasowReductionTermination.measure_wellFounded

/-- Actual full-series reductions exist recursively from every normalized
input, with finitely many branches and regular-singular full-series leaves. -/
theorem exists_tree (old : FormalState) : Nonempty (Tree old) := by
  classical
  apply smaller_wellFounded.induction old
  intro current ih
  obtain ⟨d⟩ := exists_slopeData current
  by_cases hstop : d.slope = (current.shape.rank : ℚ)+1
  · exact ⟨Tree.regular current d hstop⟩
  have hcont : d.slope < (current.shape.rank : ℚ)+1 := lt_of_le_of_ne d.bounded hstop
  have hfeedback := d.feedback.resolve_left hstop
  rcases WasowFormalSpectrum.single_eigen_or_split
      (PowerSeries.constantCoeff (rawSeries current d.slope)) with ⟨α, hN⟩ | ⟨a,b,hab⟩
  · have hn : IsNilpotent ((d.slope.den : ℂ) •
        shearedLeading current.shape.sizes (coefficients current) d.slope - α • 1) := by
      rw [rawSeries_leading current d.slope d.positive hcont] at hN
      exact hN
    let i : ContinuingInput current := ⟨d.slope,d.positive,hcont,d.weights,hfeedback,α,hn⟩
    obtain ⟨next, ⟨data⟩⟩ := exists_single_successor current i
    have hlt : Smaller next current := WasowReductionTermination.measure_decreases
      (Or.inl (singleData_step data))
    exact ⟨Tree.single current next i data (Classical.choice (ih next hlt))⟩
  · obtain ⟨q', hq'⟩ := WasowRankSelection.exists_ramified_rank current.shape.rank d.slope hcont
    obtain ⟨family⟩ := WasowFormalSplit.exists_family (rawSeries current d.slope) q'
    have hlt (c) : Smaller (family.child c) current :=
      Prod.Lex.left _ _ (WasowFormalSplit.all_children_dimension_lt family a b hab c)
    exact ⟨Tree.split current d hcont q' hq' family a b hab
      (fun c => Classical.choice (ih (family.child c) (hlt c)))⟩

/-- The tree has a natural height because every branching spectrum is finite. -/
def height {old : FormalState} : Tree old → ℕ
  | .regular _ _ _ => 0
  | .single _ _ _ _ child => height child + 1
  | .split _ _ _ _ _ _ _ _ _ children => (Finset.univ.sup (fun c => height (children c))) + 1

/-- An arbitrary full matrix series first receives its genuine spectral block
split and scalar removals, then every normalized component has a finite tree. -/
structure Reduction {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Series ι) (rank : ℕ) where
  initial : WasowFormalSplit.Family A rank
  trees : ∀ a, Tree (initial.child a)

/-- Finite recursive formal reduction from an arbitrary complete matrix series.
No initial spectral coordinates, Jordan form, or terminal canonical data are assumed. -/
theorem exists_reduction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Series ι) (rank : ℕ) : Nonempty (Reduction A rank) := by
  classical
  obtain ⟨initial⟩ := WasowFormalSplit.exists_family A rank
  exact ⟨⟨initial, fun a => Classical.choice (exists_tree (initial.child a))⟩⟩

#print axioms exists_reduction
#print axioms exists_slopeData
#print axioms slope_supported
#print axioms numerator_le
#print axioms full_shearing_identity
#print axioms stopping_rank
#print axioms smaller_wellFounded
#print axioms exists_tree
end WasowRecursiveTree
