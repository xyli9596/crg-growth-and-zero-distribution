import WasowFormalShearing
import WasowRankSelection
import WasowArbitraryFormalBlocks

/-! A continuing shearing step on the complete formal coefficient series.
All power substitution, derivative correction, scalar subtraction, constant
Jordan coordinates, and renewed all-order row normalization are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace WasowFormalSuccessor
open WasowMultiShiftReduction WasowOrderedShearing WasowShearingLeading
open WasowShearingTermination WasowFormalShearing

/-- A numerical reduction state together with its actual normalized full series. -/
structure FormalState where
  shape : State
  series : PowerSeries (Matrix (Index shape.sizes) (Index shape.sizes) ℂ)
  leading : PowerSeries.constantCoeff series = jordanShift shape.sizes
  rows : ∀ k, 0 < k → ∀ a (i : Fin (shape.sizes a+1)) j,
    i.val < shape.sizes a → PowerSeries.coeff k series ⟨a,i⟩ j = 0

def coefficients (old : FormalState) := fun k => PowerSeries.coeff k old.series

def flattenSeries (old : FormalState) := PowerSeries.map
  (Matrix.reindexAlgEquiv ℂ ℂ (flatten old.shape.sizes)).toRingHom old.series

theorem flattenSeries_coeff (old : FormalState) (k : ℕ) :
    PowerSeries.coeff k (flattenSeries old) = flatCoefficients old.shape.sizes (coefficients old) k := rfl

/-- The exact unscaled power-substitution coefficient, including its denominator
chain factor, returned to the original block index type. -/
def rawSeries (old : FormalState) (σ : ℚ) := PowerSeries.map
  (Matrix.reindexAlgEquiv ℂ ℂ (flatten old.shape.sizes).symm).toRingHom
  (ramifiedSeries (flattenSeries old) σ.den σ.den_ne_zero σ.num.toNat old.shape.rank)

theorem slope_num_div_den (σ : ℚ) (hσ : 0 ≤ σ) :
    ((σ.num.toNat : ℕ) : ℚ) / σ.den = σ := by
  have hn : 0 ≤ σ.num := Rat.num_nonneg.mpr hσ
  rw [show ((σ.num.toNat : ℕ) : ℚ) = (σ.num : ℚ) by exact_mod_cast Int.toNat_of_nonneg hn]
  exact σ.num_div_den

/-- The constructed entire ramified series has exactly the scaled leading
matrix used by the established matrix/rank transition. -/
theorem rawSeries_leading (old : FormalState) (σ : ℚ) (hσ : 0 < σ)
    (hcap : σ < (old.shape.rank : ℚ) + 1) :
    PowerSeries.constantCoeff (rawSeries old σ) =
      (σ.den : ℂ) • shearedLeading old.shape.sizes (coefficients old) σ := by
  have hs := slope_num_div_den σ hσ.le
  have hcap' : ((σ.num.toNat : ℕ) : ℚ) / σ.den < ((old.shape.rank+1 : ℕ) : ℚ) := by
    rw [hs]; exact_mod_cast hcap
  change (Matrix.reindexAlgEquiv ℂ ℂ (flatten old.shape.sizes).symm)
    (PowerSeries.constantCoeff (ramifiedSeries (flattenSeries old) σ.den σ.den_ne_zero
      σ.num.toNat old.shape.rank)) = _
  rw [constantCoeff_ramifiedSeries _ _ _ _ _ hcap', hs]
  rfl

/-- The continuing branch conditions concern the actual input coefficients
and leading matrix, without any assumed successor normal form or decrease. -/
structure ContinuingInput (old : FormalState) where
  slope : ℚ
  slope_pos : 0 < slope
  nonstopping : slope < (old.shape.rank : ℚ) + 1
  weights : ∀ k i j, flatCoefficients old.shape.sizes (coefficients old) k i j ≠ 0 →
    0 ≤ weightedDegree slope k i j
  feedback : ∃ i j, j ≤ i ∧ leadingMatrix
    (flatCoefficients old.shape.sizes (coefficients old)) slope i j ≠ 0
  eigenvalue : ℂ
  nilpotent : IsNilpotent ((slope.den : ℂ) •
    shearedLeading old.shape.sizes (coefficients old) slope - eigenvalue • 1)

/-- Every coefficient satisfies the no-negative-power condition after actual
minimal-denominator expansion; no coefficient is silently truncated away. -/
theorem supported_flattenSeries {old : FormalState} (i : ContinuingInput old) :
    Supported (flattenSeries old) i.slope.den i.slope.num.toNat := by
  apply supported_of_weightedDegree _ _ i.slope.den_ne_zero
  intro k a b hab
  rw [slope_num_div_den i.slope i.slope_pos.le]
  exact i.weights k a b hab

/-- The full cleared entry identity, including the true derivative of the
actual diagonal shearing gauge and the ramification prefactor. -/
theorem rawSeries_clear_powers {old : FormalState} (i : ContinuingInput old)
    (a b : Fin (∑ j, (old.shape.sizes j+1))) :
    PowerSeries.X^(i.slope.num.toNat*(a.val+1)) *
      WasowPowerSeries.entry (rawSeries old i.slope)
        ((flatten old.shape.sizes).symm a) ((flatten old.shape.sizes).symm b) =
      PowerSeries.C (i.slope.den : ℂ) * PowerSeries.X^(i.slope.num.toNat*b.val) *
        PowerSeries.expand i.slope.den i.slope.den_ne_zero
          (WasowPowerSeries.entry (flattenSeries old) a b) +
      (if a=b then PowerSeries.X^(i.slope.den*(old.shape.rank+1)+1) *
        PowerSeries.derivative ℂ (PowerSeries.X^(i.slope.num.toNat*a.val)) else 0) := by
  have ha : i.slope.num.toNat ≤ i.slope.den*(old.shape.rank+1) := by
    have hc := correction_exponent_pos i.slope.den i.slope.den_ne_zero
      i.slope.num.toNat old.shape.rank (by
        rw [slope_num_div_den i.slope i.slope_pos.le]
        exact_mod_cast i.nonstopping)
    omega
  have he : WasowPowerSeries.entry (rawSeries old i.slope)
      ((flatten old.shape.sizes).symm a) ((flatten old.shape.sizes).symm b) =
      WasowPowerSeries.entry (ramifiedSeries (flattenSeries old) i.slope.den i.slope.den_ne_zero
        i.slope.num.toNat old.shape.rank) a b := by
    apply PowerSeries.ext
    intro k
    simp [rawSeries, WasowPowerSeries.coeff_entry, Matrix.reindex_apply]
  rw [he]
  exact ramifiedSeries_clear_powers _ _ _ _ _ (supported_flattenSeries i) ha a b

/-- A genuine rectangular pair of coordinate inverses yields an algebra
equivalence of the full matrix coefficient rings. -/
def coordinateEquiv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix ι κ ℂ) (Q : Matrix κ ι ℂ) (hPQ : P*Q=1) (hQP : Q*P=1) :
    Matrix ι ι ℂ ≃ₐ[ℂ] Matrix κ κ ℂ where
  toFun M := Q*M*P
  invFun M := P*M*Q
  left_inv M := by
    calc
      P*(Q*M*P)*Q = (P*Q)*M*(P*Q) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hPQ, Matrix.one_mul, Matrix.mul_one]
  right_inv M := by
    calc
      Q*(P*M*Q)*P = (Q*P)*M*(Q*P) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
  map_mul' M N := by
    symm
    calc
      (Q*M*P)*(Q*N*P) = Q*M*(P*Q)*N*P := by simp only [Matrix.mul_assoc]
      _ = Q*(M*N)*P := by simp only [hPQ, Matrix.mul_one, Matrix.mul_assoc]
  map_add' M N := by simp only [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hQP]

/-- Complete algebraic data linking two normalized full formal states. -/
structure SingleData (old next : FormalState) (i : ContinuingInput old) where
  P : Matrix (Index old.shape.sizes) (Index next.shape.sizes) ℂ
  Q : Matrix (Index next.shape.sizes) (Index old.shape.sizes) ℂ
  PQ : P*Q=1
  QP : Q*P=1
  jordan : Q * ((i.slope.den : ℂ) •
    shearedLeading old.shape.sizes (coefficients old) i.slope - i.eigenvalue • 1) * P =
      jordanShift next.shape.sizes
  rank_update : (next.shape.rank : ℚ) =
    (i.slope.den : ℚ) * ((old.shape.rank : ℚ)+1-i.slope)-1
  gauge : PowerSeries (Matrix (Index next.shape.sizes) (Index next.shape.sizes) ℂ)
  inverse : PowerSeries (Matrix (Index next.shape.sizes) (Index next.shape.sizes) ℂ)
  gauge_constant : PowerSeries.constantCoeff gauge = 1
  gauge_unit : IsUnit gauge
  inverse_left : inverse*gauge=1
  inverse_right : gauge*inverse=1
  gauge_rows : ∀ k a b j, PowerSeries.coeff (k+1) gauge ⟨a,0⟩ ⟨b,j⟩=0
  equation : PowerSeries.map (coordinateEquiv P Q PQ QP).toRingHom
      (rawSeries old i.slope - PowerSeries.C (i.eigenvalue • 1)) * gauge -
    gauge * next.series =
      -(PowerSeries.X^(next.shape.rank+2) * WasowPowerSeries.derivative gauge)

/-- The complete series successor really gives the previously verified
matrix/rank transition, with its actual ramification prefactor. -/
theorem singleData_step {old next : FormalState} {i : ContinuingInput old}
    (d : SingleData old next i) : Step next.shape old.shape := by
  refine ⟨⟨coefficients old, (by simpa only [coefficients, PowerSeries.coeff_zero_eq_constantCoeff_apply] using old.leading), old.rows,
    i.slope, i.slope_pos, i.nonstopping, i.weights, i.feedback,
    (i.slope.den : ℂ), ?_, i.eigenvalue, i.nilpotent,
    d.P, d.Q, d.PQ, d.QP, d.jordan, d.rank_update⟩⟩
  exact_mod_cast i.slope.den_ne_zero

/-- Every verified continuing single-eigenvalue branch produces a complete
normalized successor series and exact invertible formal gauge data. -/
theorem exists_single_successor (old : FormalState) (i : ContinuingInput old) :
    ∃ next : FormalState, Nonempty (SingleData old next i) := by
  obtain ⟨q', hq'⟩ := WasowRankSelection.exists_ramified_rank old.shape.rank i.slope i.nonstopping
  obtain ⟨s, h, hh, P, Q, hPQ, hQP, hJ⟩ :=
    WasowSortedJordan.exists_sorted_jordan_matrix_coordinates _ i.nilpotent
  let st : State := ⟨s, h, hh, q'⟩
  let e := coordinateEquiv P Q hPQ hQP
  let D := PowerSeries.map e.toRingHom
    (rawSeries old i.slope - PowerSeries.C (i.eigenvalue • 1))
  have hD : PowerSeries.constantCoeff D = jordanShift h := by
    change Q * (PowerSeries.constantCoeff (rawSeries old i.slope) - i.eigenvalue • 1) * P = _
    rw [rawSeries_leading old i.slope i.slope_pos i.nonstopping]
    exact hJ
  obtain ⟨U, B, V, hU0, hUunit, hB0, hUrows, hBrows, hVU, hUV, heq⟩ :=
    WasowFormalSeries.exists_multishift_powerSeries h D hD (Nat.succ_pos q')
  have hrows : ∀ k, 0 < k → ∀ a (u : Fin (h a+1)) j,
      u.val < h a → PowerSeries.coeff k B ⟨a,u⟩ j = 0 := by
    intro k hk a u j hu
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rcases j with ⟨b,v⟩
    exact hBrows l a b u v hu
  let next : FormalState := ⟨st, B, hB0.trans hD, hrows⟩
  exact ⟨next, ⟨⟨P, Q, hPQ, hQP, hJ, hq', U, V, hU0, hUunit, hVU, hUV, hUrows, heq⟩⟩⟩

/-- The relation records the actual series and all transformation identities. -/
def FormalStep (next old : FormalState) : Prop :=
  ∃ i : ContinuingInput old, Nonempty (SingleData old next i)

theorem formalStep_wellFounded : WellFounded FormalStep := by
  apply (InvImage.wf FormalState.shape WasowShearingTermination.step_wellFounded).mono
  intro next old hs
  obtain ⟨i, ⟨d⟩⟩ := hs
  exact singleData_step d

#print axioms singleData_step
#print axioms exists_single_successor
#print axioms formalStep_wellFounded
#print axioms flattenSeries_coeff
#print axioms slope_num_div_den
#print axioms rawSeries_leading
#print axioms supported_flattenSeries
#print axioms rawSeries_clear_powers
end WasowFormalSuccessor
