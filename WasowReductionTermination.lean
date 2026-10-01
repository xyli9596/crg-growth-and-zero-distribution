import WasowShearingTermination

/-! Well-foundedness of actual matrix/rank reductions, combining genuine
single-eigenvalue shearing steps with passage to a proper generalized
eigenspace. Dimension decrease is proved from distinct eigenvalues and an
actual basis of the selected block. No decrease is an input to the relation.
This is not the construction of the full successor formal series or the
complete Wasow normal form. -/
set_option autoImplicit false
noncomputable section
namespace WasowReductionTermination
open Module
open WasowLeadingBlocks WasowMultiShiftReduction WasowShearingTermination

/-- A second distinct eigenvalue forces the chosen generalized eigenspace
to be proper: the other nonzero block is disjoint from it. -/
theorem blockSpace_ne_top {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V)
    (a b : Eigenvalues f) (hab : a ≠ b) : blockSpace f a ≠ ⊤ := by
  have hv : a.val ≠ b.val := fun hh => hab (Subtype.ext hh)
  have hd : Disjoint (blockSpace f a) (blockSpace f b) :=
    f.disjoint_genEigenspace hv ⊤ ⊤
  intro ht
  rw [ht, top_disjoint] at hd
  exact blockSpace_ne_bot f b hd

/-- The actual block dimension is strictly smaller than the ambient dimension. -/
theorem block_finrank_lt {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V)
    (a b : Eigenvalues f) (hab : a ≠ b) :
    Module.finrank ℂ (blockSpace f a) < Module.finrank ℂ V :=
  Submodule.finrank_lt (blockSpace_ne_top f a b hab)

/-- The dimension of a reduction state is its actual Jordan coordinate cardinality. -/
def dim (x : State) : ℕ := Fintype.card (Index x.sizes)

/-- A genuine single-eigenvalue coordinate transition preserves dimension. -/
theorem dim_eq_of_step {next old : State} (hs : Step next old) : dim next = dim old := by
  obtain ⟨d⟩ := hs
  exact (WasowPencilCoordinates.card_eq_of_two_sided_inverse d.P d.Q d.PQ d.QP).symm

/-- Concrete multi-eigenvalue splitting data. The selected component has a
true sorted Jordan basis for its translated restricted operator. The next
rank is unrestricted: dimension decrease also covers splitting after a
ramified shear whose resulting rank differs from the old rank. -/
structure SplitData (next old : State) where
  C : Matrix (Index old.sizes) (Index old.sizes) ℂ
  a : Eigenvalues (Matrix.toLin' C)
  b : Eigenvalues (Matrix.toLin' C)
  distinct : a ≠ b
  basis : Basis (Index next.sizes) ℂ (blockSpace (Matrix.toLin' C) a)
  jordan : LinearMap.toMatrix basis basis
    (restriction (Matrix.toLin' C) a -
      algebraMap ℂ (Module.End ℂ (blockSpace (Matrix.toLin' C) a)) a.val) =
        jordanShift next.sizes

/-- The split relation asks for an actual coordinate realization, not a
numeric dimension-decrease certificate. -/
def Split (next old : State) : Prop := Nonempty (SplitData next old)

theorem dim_lt_of_split {next old : State} (hs : Split next old) : dim next < dim old := by
  obtain ⟨d⟩ := hs
  have hh := block_finrank_lt (Matrix.toLin' d.C) d.a d.b d.distinct
  rw [Module.finrank_eq_card_basis d.basis, Module.finrank_pi] at hh
  exact hh

/-- Actual distinct eigenvalues automatically produce a sorted Jordan
successor of the selected component, with no assumed coordinate basis. -/
theorem exists_split_successor (old : State)
    (C : Matrix (Index old.sizes) (Index old.sizes) ℂ)
    (a b : Eigenvalues (Matrix.toLin' C)) (hab : a ≠ b) (q' : ℕ) :
    ∃ next : State, next.rank = q' ∧ Split next old := by
  obtain ⟨s, h, hh, basis, hj⟩ := WasowSortedJordan.exists_sorted_jordan_basis
    (restriction (Matrix.toLin' C) a -
      algebraMap ℂ (Module.End ℂ (blockSpace (Matrix.toLin' C) a)) a.val)
    (restriction_sub_nilpotent (Matrix.toLin' C) a)
  let next : State := ⟨s, h, hh, q'⟩
  exact ⟨next, rfl, ⟨⟨C, a, b, hab, basis, hj⟩⟩⟩

/-- Both genuine operation types are included in one reduction relation. -/
def CombinedStep (next old : State) : Prop := Step next old ∨ Split next old

def measure (x : State) : ℕ × (ℕ × ℕ) :=
  (dim x, WasowShearingTermination.measure x)

/-- The lexicographic triple decreases for either actual operation. -/
theorem measure_decreases {next old : State} (hs : CombinedStep next old) :
    Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) (measure next) (measure old) := by
  rcases hs with hs | hs
  · unfold measure
    rw [dim_eq_of_step hs]
    exact Prod.Lex.right _ (WasowShearingTermination.measure_decreases hs)
  · exact Prod.Lex.left _ _ (dim_lt_of_split hs)

/-- The stated dimension/mass/rank lexicographic order is well-founded. -/
theorem measure_wellFounded :
    WellFounded (InvImage (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) measure) := by
  exact InvImage.wf measure
    (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

/-- Genuine shear and generalized-eigenspace split steps cannot continue forever. -/
theorem combinedStep_wellFounded : WellFounded CombinedStep :=
  measure_wellFounded.mono (fun _ _ hs => measure_decreases hs)

theorem no_infinite_combined_steps (x : ℕ → State) :
    ¬ ∀ n, CombinedStep (x (n+1)) (x n) := by
  intro hx
  exact (wellFounded_iff_isEmpty_descending_chain.mp combinedStep_wellFounded).false ⟨x, hx⟩

#print axioms blockSpace_ne_top
#print axioms block_finrank_lt
#print axioms dim_eq_of_step
#print axioms dim_lt_of_split
#print axioms exists_split_successor
#print axioms measure_decreases
#print axioms measure_wellFounded
#print axioms combinedStep_wellFounded
#print axioms no_infinite_combined_steps
end WasowReductionTermination
