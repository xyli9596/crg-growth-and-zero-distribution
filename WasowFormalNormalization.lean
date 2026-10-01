import WasowFormalSuccessor

/-! Actual normalization of a full series with nilpotent leading matrix.
The sorted Jordan coordinates and invertible all-order row gauge are outputs. -/
set_option autoImplicit false
noncomputable section
namespace WasowFormalNormalization
open WasowFormalSuccessor WasowMultiShiftReduction WasowShearingTermination

abbrev Series (ι : Type*) := PowerSeries (Matrix ι ι ℂ)

/-- Full coordinate and differential data for a normalized successor series. -/
structure Data {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Series ι) (rank : ℕ) (next : FormalState) where
  P : Matrix ι (Index next.shape.sizes) ℂ
  Q : Matrix (Index next.shape.sizes) ι ℂ
  PQ : P*Q=1
  QP : Q*P=1
  jordan : Q * PowerSeries.constantCoeff A * P = jordanShift next.shape.sizes
  rank_eq : next.shape.rank = rank
  gauge : Series (Index next.shape.sizes)
  inverse : Series (Index next.shape.sizes)
  gauge_constant : PowerSeries.constantCoeff gauge = 1
  gauge_unit : IsUnit gauge
  inverse_left : inverse*gauge=1
  inverse_right : gauge*inverse=1
  equation : PowerSeries.map (coordinateEquiv P Q PQ QP).toRingHom A * gauge -
    gauge * next.series = -(PowerSeries.X^(rank+2) * WasowPowerSeries.derivative gauge)

theorem exists_normalization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Series ι) (rank : ℕ) (hN : IsNilpotent (PowerSeries.constantCoeff A)) :
    ∃ next : FormalState, Nonempty (Data A rank next) := by
  obtain ⟨s, h, hh, P, Q, hPQ, hQP, hJ⟩ :=
    WasowSortedJordan.exists_sorted_jordan_matrix_coordinates _ hN
  let st : State := ⟨s, h, hh, rank⟩
  let D := PowerSeries.map (coordinateEquiv P Q hPQ hQP).toRingHom A
  have hD : PowerSeries.constantCoeff D = jordanShift h := hJ
  obtain ⟨U, B, V, hU0, hUunit, hB0, _, hBrows, hVU, hUV, heq⟩ :=
    WasowFormalSeries.exists_multishift_powerSeries h D hD (Nat.succ_pos rank)
  have hrows : ∀ k, 0 < k → ∀ a (u : Fin (h a+1)) j,
      u.val < h a → PowerSeries.coeff k B ⟨a,u⟩ j = 0 := by
    intro k hk a u j hu
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rcases j with ⟨b,v⟩
    exact hBrows l a b u v hu
  let next : FormalState := ⟨st, B, hB0.trans hD, hrows⟩
  exact ⟨next, ⟨⟨P, Q, hPQ, hQP, hJ, rfl, U, V, hU0, hUunit, hVU, hUV, heq⟩⟩⟩

/-- Dimension equality follows from the actual rectangular coordinate inverses. -/
theorem data_dimension {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Series ι} {rank : ℕ} {next : FormalState} (d : Data A rank next) :
    Fintype.card (Index next.shape.sizes) = Fintype.card ι :=
  (WasowPencilCoordinates.card_eq_of_two_sided_inverse d.P d.Q d.PQ d.QP).symm

#print axioms exists_normalization
#print axioms data_dimension
end WasowFormalNormalization
