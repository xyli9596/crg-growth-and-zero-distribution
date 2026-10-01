import WasowFormalNormalization
import WasowReductionTermination

/-! Actual all-order multi-eigenvalue splitting of a full matrix series,
followed by genuine sorted Jordan normalization of every selected component.
The global block gauge and every child's exact differential equation are data. -/
set_option autoImplicit false
noncomputable section
namespace WasowFormalSplit
open Module WasowLeadingBlocks WasowArbitraryFormalBlocks
open WasowFormalSuccessor WasowFormalNormalization WasowMultiShiftReduction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Spectrum (A : Series ι) := Eigenvalues (Matrix.toLin' (PowerSeries.constantCoeff A))

/-- The actual full block-diagonal series and its invertible differential gauge. -/
structure BlockData (A : Series ι) (rank : ℕ) where
  gauge : Series (BlockIndex A)
  series : Series (BlockIndex A)
  inverse : Series (BlockIndex A)
  gauge_constant : PowerSeries.constantCoeff gauge = 1
  gauge_unit : IsUnit gauge
  leading : PowerSeries.constantCoeff series = PowerSeries.constantCoeff (coordinateSeries A)
  offDiagonal : ∀ k a b, a ≠ b → ∀ i j,
    PowerSeries.coeff k series ⟨a,i⟩ ⟨b,j⟩ = 0
  inverse_left : inverse*gauge=1
  inverse_right : gauge*inverse=1
  equation : coordinateSeries A*gauge - gauge*series =
    -(PowerSeries.X^(rank+2) * WasowPowerSeries.derivative gauge)

theorem exists_blockData (A : Series ι) (rank : ℕ) : Nonempty (BlockData A rank) := by
  obtain ⟨P, B, S, hP0, hPu, hB0, _, hB, hSP, hPS, heq⟩ :=
    exists_arbitrary_formal_block_reduction A (Nat.succ_pos rank)
  exact ⟨⟨P, B, S, hP0, hPu, hB0, hB, hSP, hPS, heq⟩⟩

/-- Every component is extracted from the actual globally split series. -/
def component {A : Series ι} {rank : ℕ} (d : BlockData A rank) (a : Spectrum A) :
    Series (Fin (blockSize (Matrix.toLin' (PowerSeries.constantCoeff A)) a + 1)) :=
  PowerSeries.mk (fun k => block (PowerSeries.coeff k d.series) a a)

theorem component_coeff {A : Series ι} {rank : ℕ} (d : BlockData A rank)
    (a : Spectrum A) (k : ℕ) :
    PowerSeries.coeff k (component d a) = block (PowerSeries.coeff k d.series) a a :=
  PowerSeries.coeff_mk _ _

theorem component_leading {A : Series ι} {rank : ℕ} (d : BlockData A rank)
    (a : Spectrum A) :
    PowerSeries.constantCoeff (component d a) =
      a.val • 1 + nilpotentBlock (Matrix.toLin' (PowerSeries.constantCoeff A)) a := by
  calc
    PowerSeries.constantCoeff (component d a) = PowerSeries.coeff 0 (component d a) :=
      (PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm
    _ = block (PowerSeries.coeff 0 d.series) a a := component_coeff d a 0
    _ = block (PowerSeries.constantCoeff d.series) a a := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply d.series]
    _ = _ := by
      rw [d.leading, coordinateSeries_leading]
      apply Matrix.ext
      intro i j
      simp [block, WasowMultiBlockReduction.leading]

/-- Scalar eigenvalue removal is kept as an explicit formal operation. -/
def translatedComponent {A : Series ι} {rank : ℕ} (d : BlockData A rank) (a : Spectrum A) :=
  component d a - PowerSeries.C (a.val • 1)

theorem translatedComponent_leading {A : Series ι} {rank : ℕ} (d : BlockData A rank)
    (a : Spectrum A) :
    PowerSeries.constantCoeff (translatedComponent d a) =
      nilpotentBlock (Matrix.toLin' (PowerSeries.constantCoeff A)) a := by
  simp [translatedComponent, component_leading]

/-- A whole finite family of normalized children, with all connecting data. -/
structure Family (A : Series ι) (rank : ℕ) where
  blocks : BlockData A rank
  child : Spectrum A → FormalState
  normalization : ∀ a, Data (translatedComponent blocks a) rank (child a)

theorem exists_family (A : Series ι) (rank : ℕ) : Nonempty (Family A rank) := by
  classical
  obtain ⟨d⟩ := exists_blockData A rank
  have hn (a : Spectrum A) : IsNilpotent (PowerSeries.constantCoeff (translatedComponent d a)) := by
    rw [translatedComponent_leading]
    exact nilpotentBlock_isNilpotent _ a
  choose next hd using fun a : Spectrum A => exists_normalization (translatedComponent d a) rank (hn a)
  exact ⟨⟨d, next, fun a => Classical.choice (hd a)⟩⟩

/-- A second eigenvalue proves a child's dimension decrease from actual bases;
it is not a premise about the numerical reduction invariant. -/
theorem child_dimension_lt {A : Series ι} {rank : ℕ} (F : Family A rank)
    (a b : Spectrum A) (hab : a ≠ b) :
    WasowReductionTermination.dim (F.child a).shape < Fintype.card ι := by
  have hd := data_dimension (F.normalization a)
  have hl := WasowReductionTermination.block_finrank_lt
    (Matrix.toLin' (PowerSeries.constantCoeff A)) a b hab
  rw [block_finrank, Module.finrank_pi] at hl
  change Fintype.card (Index (F.child a).shape.sizes) < _
  rw [hd, Fintype.card_fin]
  exact hl

theorem all_children_dimension_lt {A : Series ι} {rank : ℕ} (F : Family A rank)
    (a b : Spectrum A) (hab : a ≠ b) :
    ∀ c, WasowReductionTermination.dim (F.child c).shape < Fintype.card ι := by
  intro c
  by_cases hc : c = a
  · subst c
    exact child_dimension_lt F a b hab
  · exact child_dimension_lt F c a hc

#print axioms exists_blockData
#print axioms component_coeff
#print axioms component_leading
#print axioms translatedComponent_leading
#print axioms exists_family
#print axioms child_dimension_lt
#print axioms all_children_dimension_lt
end WasowFormalSplit
