import WasowOrderedShearing
import WasowPencilCoordinates
import WasowPencilScaling
import WasowSortedJordan
import Mathlib.Order.WellFounded

/-! Well-foundedness of actual continuing single-eigenvalue shearing steps.
The relation records normalized coefficient data, the selected zero-weight
leading matrix, the exact minimal-denominator rank update, and genuine Jordan
coordinate inverses. It does not assume any invariant decrease. This terminates
these matrix/rank steps; constructing the complete successor formal series and
assembling the splitting and stopping branches is a separate task. -/
set_option autoImplicit false
noncomputable section
namespace WasowShearingTermination
open WasowMultiShiftReduction WasowOrderedShearing WasowShearingLeading
open WasowPencilReduction

structure State where
  blocks : ℕ
  sizes : Fin blocks → ℕ
  sorted : Monotone sizes
  rank : ℕ

def mass (x : State) : ℕ :=
  WasowPencilDescent.degreeMass (pencil (jordanShift x.sizes))

def measure (x : State) : ℕ × ℕ := (mass x, x.rank)

/-- Concrete data of a continuing single-eigenvalue step. The rank here is
Wasow's exponent in `x^(-q)y'=A(x)y`, not the inverse-variable formal index. -/
structure StepData (next old : State) where
  A : ℕ → Matrix (Index old.sizes) (Index old.sizes) ℂ
  initial : A 0 = jordanShift old.sizes
  rows : ∀ k, 0 < k → ∀ a (i : Fin (old.sizes a+1)) j,
    i.val < old.sizes a → A k ⟨a,i⟩ j = 0
  slope : ℚ
  slope_pos : 0 < slope
  nonstopping : slope < (old.rank : ℚ) + 1
  weights : ∀ k i j, flatCoefficients old.sizes A k i j ≠ 0 →
    0 ≤ weightedDegree slope k i j
  feedback : ∃ i j, j ≤ i ∧ leadingMatrix (flatCoefficients old.sizes A) slope i j ≠ 0
  scale : ℂ
  scale_ne_zero : scale ≠ 0
  eigenvalue : ℂ
  nilpotent : IsNilpotent (scale • shearedLeading old.sizes A slope - eigenvalue • 1)
  P : Matrix (Index old.sizes) (Index next.sizes) ℂ
  Q : Matrix (Index next.sizes) (Index old.sizes) ℂ
  PQ : P * Q = 1
  QP : Q * P = 1
  next_jordan : Q * (scale • shearedLeading old.sizes A slope - eigenvalue • 1) * P =
    jordanShift next.sizes
  rank_update : (next.rank : ℚ) = (slope.den : ℚ) * ((old.rank : ℚ) + 1 - slope) - 1

def Step (next old : State) : Prop := Nonempty (StepData next old)

/-- Actual coordinate changes and scalar subtraction preserve the next mass. -/
theorem next_mass {next old : State} (d : StepData next old) :
    mass next = WasowPencilDescent.degreeMass
      (pencil (shearedLeading old.sizes d.A d.slope)) := by
  unfold mass
  rw [← d.next_jordan,
    WasowPencilCoordinates.degreeMass_coordinates _ d.P d.Q d.PQ d.QP,
    WasowPencilSimilarity.degreeMass_sub_scalar,
    WasowPencilScaling.degreeMass_smul _ d.scale d.scale_ne_zero]

/-- The first measure never increases in a genuine single-eigenvalue step. -/
theorem mass_le {next old : State} (d : StepData next old) : mass next ≤ mass old := by
  rw [next_mass d]
  exact shearedLeading_single_eigen_mass_le old.sizes d.A d.initial d.rows
    d.slope_pos (d.eigenvalue / d.scale)
    (WasowPencilScaling.isNilpotent_unscale _ _ _ d.scale_ne_zero d.nilpotent)

/-- A fractional slope strictly decreases the actual determinantal invariant. -/
theorem mass_lt_of_fractional {next old : State} (d : StepData next old)
    (hfrac : ∀ k : ℕ, d.slope ≠ k) : mass next < mass old := by
  rw [next_mass d]
  exact fractional_single_eigen_strict_drop old.sizes old.sorted d.A d.initial d.rows
    d.slope_pos hfrac d.feedback (d.eigenvalue / d.scale)
    (WasowPencilScaling.isNilpotent_unscale _ _ _ d.scale_ne_zero d.nilpotent)

/-- For an integral slope the minimal ramification denominator is one, so
its exact rank update strictly decreases the nonnegative rank. -/
theorem rank_lt_of_integral {next old : State} (d : StepData next old)
    (hint : ∃ k : ℕ, d.slope = k) : next.rank < old.rank := by
  obtain ⟨k,hk⟩ := hint
  have hden : d.slope.den = 1 := by rw [hk]; simp
  have hr := d.rank_update
  rw [hden] at hr
  norm_num only [Nat.cast_one, one_mul] at hr
  have hs := d.slope_pos
  exact_mod_cast (show (next.rank : ℚ) < old.rank by linarith)

/-- The lexicographic decrease is a conclusion of the actual step equations. -/
theorem measure_decreases {next old : State} (h : Step next old) :
    Prod.Lex Nat.lt Nat.lt (measure next) (measure old) := by
  classical
  obtain ⟨d⟩ := h
  by_cases hint : ∃ k : ℕ, d.slope = k
  · exact Prod.Lex.right' Nat.lt (mass_le d) (rank_lt_of_integral d hint)
  · exact Prod.Lex.left _ _ (mass_lt_of_fractional d (by simpa only [not_exists] using hint))

/-- No indefinite sequence of these genuine single-eigenvalue shear steps exists,
even though an individual fractional step can increase the integer rank. -/
theorem step_wellFounded : WellFounded Step := by
  have hw : WellFounded (Prod.Lex Nat.lt Nat.lt) := (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
  exact (InvImage.wf measure hw).mono (fun _ _ h => measure_decreases h)

/-- Every infinite candidate sequence has an index at which a genuine step
fails; this is the chain formulation of the proved well-foundedness. -/
theorem no_infinite_steps (x : ℕ → State) : ¬ ∀ n, Step (x (n+1)) (x n) := by
  intro hx
  exact (wellFounded_iff_isEmpty_descending_chain.mp step_wellFounded).false ⟨x, hx⟩

/-- Continuing single-eigenvalue data actually produce a successor: the
next sorted Jordan coordinates are supplied by the general Jordan theorem.
The nonzero scale includes the true ramification prefactor. -/
theorem exists_successor (old : State)
    (A : ℕ → Matrix (Index old.sizes) (Index old.sizes) ℂ)
    (hA : A 0 = jordanShift old.sizes)
    (hrows : ∀ k, 0 < k → ∀ a (i : Fin (old.sizes a+1)) j,
      i.val < old.sizes a → A k ⟨a,i⟩ j = 0)
    (σ : ℚ) (hσ : 0 < σ) (hcap : σ < (old.rank : ℚ)+1)
    (hweights : ∀ k i j, flatCoefficients old.sizes A k i j ≠ 0 →
      0 ≤ weightedDegree σ k i j)
    (hfeedback : ∃ i j, j ≤ i ∧ leadingMatrix (flatCoefficients old.sizes A) σ i j ≠ 0)
    (c α : ℂ) (hc : c ≠ 0)
    (hN : IsNilpotent (c • shearedLeading old.sizes A σ - α • 1))
    (q' : ℕ) (hq' : (q' : ℚ) = (σ.den : ℚ) * ((old.rank : ℚ)+1-σ)-1) :
    ∃ next : State, next.rank = q' ∧ Step next old := by
  obtain ⟨s, h, hh, P, Q, hPQ, hQP, hJ⟩ :=
    WasowSortedJordan.exists_sorted_jordan_matrix_coordinates _ hN
  let next : State := ⟨s, h, hh, q'⟩
  refine ⟨next, rfl, ⟨{
    A := A
    initial := hA
    rows := hrows
    slope := σ
    slope_pos := hσ
    nonstopping := hcap
    weights := hweights
    feedback := hfeedback
    scale := c
    scale_ne_zero := hc
    eigenvalue := α
    nilpotent := hN
    P := P
    Q := Q
    PQ := hPQ
    QP := hQP
    next_jordan := hJ
    rank_update := hq'
  }⟩⟩

#print axioms next_mass
#print axioms mass_le
#print axioms mass_lt_of_fractional
#print axioms rank_lt_of_integral
#print axioms measure_decreases
#print axioms step_wellFounded
#print axioms no_infinite_steps
#print axioms exists_successor
end WasowShearingTermination
