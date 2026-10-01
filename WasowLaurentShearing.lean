import WasowLaurentRamification
import WasowRecursiveTree

/-! Actual Laurent diagonal shearing of full formal coefficients. The new rank
is an integer, so the regular-singular stopping rank `-1` is included. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace WasowLaurentShearing
open WasowLaurentGauge WasowLaurentRamification WasowFormalSuccessor
open WasowMultiShiftReduction WasowOrderedShearing WasowRecursiveTree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Differential coefficient in the inverse variable, for arbitrary integer rank. -/
def differentialCoefficientZ (q : ℤ) (A : PowerSeries (Matrix ι ι ℂ)) : Matrix ι ι L :=
  fun i j => HahnSeries.single (-q-2) (-1) * toLaurent A i j

@[simp] theorem differentialCoefficientZ_nat (q : ℕ)
    (A : PowerSeries (Matrix ι ι ℂ)) :
    differentialCoefficientZ (q : ℤ) A = differentialCoefficient q A := rfl

/-- Diagonal Laurent monomials with unrestricted integral exponents. -/
def diagonalGauge (w : ι → ℤ) : Matrix ι ι L :=
  Matrix.diagonal (fun i => HahnSeries.single (w i) 1)

theorem diagonalGauge_inverses (w : ι → ℤ) :
    diagonalGauge w * diagonalGauge (fun i => -w i) = 1 ∧
    diagonalGauge (fun i => -w i) * diagonalGauge w = 1 := by
  constructor <;> simp [diagonalGauge, Matrix.diagonal_mul_diagonal]

omit [Fintype ι] in
theorem diagonalGauge_derivative (w : ι → ℤ) (i j : ι) :
    matrixDerivative (diagonalGauge w) i j =
      if i=j then D (HahnSeries.single (w i) 1) else 0 := by
  by_cases h : i=j <;> simp [matrixDerivative, diagonalGauge, h]

/-- Clearing nonnegative powers is sufficient to establish the genuine
Laurent differential equation. This lemma retains the derivative correction. -/
theorem gaugeEquation_of_clear_powers (q p a : ℕ) (hp : 0 < p) (w : ι → ℕ)
    (A B : PowerSeries (Matrix ι ι ℂ))
    (he : ∀ i j,
      (HahnSeries.single ((a*(w i+1) : ℕ) : ℤ) 1 : L) * toLaurent B i j =
      HahnSeries.C (p : ℂ) * HahnSeries.single ((a*w j : ℕ) : ℤ) 1 *
        ramify p hp (toLaurent A i j) +
      if i=j then HahnSeries.single ((p*(q+1)+1 : ℕ) : ℤ) 1 *
        D (HahnSeries.single ((a*w i : ℕ) : ℤ) 1) else 0) :
    GaugeEquation (pullback p hp (differentialCoefficientZ (q : ℤ) A))
      (diagonalGauge (fun i => ((a*w i : ℕ) : ℤ)))
      (differentialCoefficientZ ((p : ℤ)*(q+1)-a-1) B) := by
  unfold GaugeEquation
  apply Matrix.ext
  intro i j
  rw [Matrix.sub_apply, diagonalGauge_derivative]
  simp only [diagonalGauge, Matrix.mul_diagonal, Matrix.diagonal_mul,
    pullback, differentialCoefficientZ, map_mul, ramify_single]
  let t : L := HahnSeries.single ((p*(q+1)+1 : ℕ) : ℤ) 1
  have ht : t ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  apply mul_left_cancel₀ ht
  have hc1 : t * (jacobian p * HahnSeries.single ((p : ℤ)*(-(q : ℤ)-2)) (-1)) =
      -(HahnSeries.C (p : ℂ) : L) := by
    dsimp [t, jacobian]
    rw [← mul_assoc, HahnSeries.single_mul_single, HahnSeries.single_mul_single]
    have hex : ((p*(q+1)+1 : ℕ) : ℤ) + ((p : ℤ)-1) + (p : ℤ)*(-(q : ℤ)-2) = 0 := by
      push_cast
      ring
    push_cast at hex
    rw [hex]
    simp
    exact map_natCast (HahnSeries.C : ℂ →+* L) p
  have hc2 : t * (HahnSeries.single ((a*w i : ℕ) : ℤ) 1 *
      HahnSeries.single (-((p : ℤ)*(q+1)-a-1)-2) (-1)) =
      -(HahnSeries.single ((a*(w i+1) : ℕ) : ℤ) 1 : L) := by
    dsimp [t]
    rw [← mul_assoc, HahnSeries.single_mul_single, HahnSeries.single_mul_single]
    have hex : ((p*(q+1)+1 : ℕ) : ℤ) + ((a*w i : ℕ) : ℤ) +
        (-((p : ℤ)*(q+1)-a-1)-2) = ((a*(w i+1) : ℕ) : ℤ) := by
      push_cast
      ring
    push_cast at hex
    rw [hex]
    simp
  calc
    _ = (t * (jacobian p * HahnSeries.single ((p : ℤ)*(-(q : ℤ)-2)) (-1))) *
        HahnSeries.single ((a*w j : ℕ) : ℤ) 1 * ramify p hp (toLaurent A i j) -
        (t * (HahnSeries.single ((a*w i : ℕ) : ℤ) 1 *
          HahnSeries.single (-((p : ℤ)*(q+1)-a-1)-2) (-1))) * toLaurent B i j := by ring
    _ = -(HahnSeries.C (p : ℂ) * HahnSeries.single ((a*w j : ℕ) : ℤ) 1 *
        ramify p hp (toLaurent A i j)) +
        HahnSeries.single ((a*(w i+1) : ℕ) : ℤ) 1 * toLaurent B i j := by
      rw [hc1, hc2]
      ring
    _ = if i=j then t * D (HahnSeries.single ((a*w i : ℕ) : ℤ) 1) else 0 := by
      rw [he]
      dsimp [t]
      abel
    _ = _ := by split_ifs <;> simp

def shearingRank {old : FormalState} (d : SlopeData old) : ℤ :=
  (d.slope.den : ℤ)*(old.shape.rank+1)-d.slope.num.toNat-1

def shearingGauge {old : FormalState} (d : SlopeData old) :
    Matrix (Index old.shape.sizes) (Index old.shape.sizes) L :=
  diagonalGauge (fun i => ((d.slope.num.toNat * (flatten old.shape.sizes i).val : ℕ) : ℤ))

def shearingInverse {old : FormalState} (d : SlopeData old) :
    Matrix (Index old.shape.sizes) (Index old.shape.sizes) L :=
  diagonalGauge (fun i => -((d.slope.num.toNat * (flatten old.shape.sizes i).val : ℕ) : ℤ))

theorem shearing_inverses {old : FormalState} (d : SlopeData old) :
    shearingGauge d * shearingInverse d = 1 ∧ shearingInverse d * shearingGauge d = 1 :=
  diagonalGauge_inverses _

theorem entry_flattenSeries (old : FormalState) (i j : Index old.shape.sizes) :
    WasowPowerSeries.entry (flattenSeries old)
      (flatten old.shape.sizes i) (flatten old.shape.sizes j) =
      WasowPowerSeries.entry old.series i j := by
  apply PowerSeries.ext
  intro n
  simp [flattenSeries, WasowPowerSeries.coeff_entry, Matrix.reindex_apply]

theorem shearing_clear_laurent {old : FormalState} (d : SlopeData old)
    (i j : Index old.shape.sizes) :
    (HahnSeries.single
      ((d.slope.num.toNat*((flatten old.shape.sizes i).val+1) : ℕ) : ℤ) 1 : L) *
        toLaurent (rawSeries old d.slope) i j =
      HahnSeries.C (d.slope.den : ℂ) *
        HahnSeries.single ((d.slope.num.toNat*(flatten old.shape.sizes j).val : ℕ) : ℤ) 1 *
        ramify d.slope.den d.slope.den_pos (toLaurent old.series i j) +
      if i=j then
        HahnSeries.single ((d.slope.den*(old.shape.rank+1)+1 : ℕ) : ℤ) 1 *
        D (HahnSeries.single
          ((d.slope.num.toNat*(flatten old.shape.sizes i).val : ℕ) : ℤ) 1) else 0 := by
  have he := full_shearing_identity d (flatten old.shape.sizes i) (flatten old.shape.sizes j)
  simp only [Equiv.symm_apply_apply, entry_flattenSeries, Equiv.apply_eq_iff_eq] at he
  have hl := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) he
  simp only [map_mul, map_add, HahnSeries.ofPowerSeries_X_pow,
    HahnSeries.ofPowerSeries_C, apply_ite, map_zero] at hl
  rw [← ramify_powerSeries d.slope.den d.slope.den_pos,
    ← derivative_powerSeries] at hl
  by_cases hij : i=j <;>
    simpa only [hij, if_true, if_false, toLaurent_apply, HahnSeries.ofPowerSeries_X_pow] using hl

/-- Every automatically selected slope has an actual invertible Laurent
shearing gauge. This includes the stopping branch without a positive-rank premise. -/
theorem gaugeEquation_shearing {old : FormalState} (d : SlopeData old) :
    GaugeEquation (pullback d.slope.den d.slope.den_pos
      (differentialCoefficient old.shape.rank old.series)) (shearingGauge d)
      (differentialCoefficientZ (shearingRank d) (rawSeries old d.slope)) := by
  exact gaugeEquation_of_clear_powers old.shape.rank d.slope.den d.slope.num.toNat
    d.slope.den_pos (fun i => (flatten old.shape.sizes i).val) old.series
    (rawSeries old d.slope) (shearing_clear_laurent d)

/-- The integer rank agrees with the exact rational ramification formula. -/
theorem shearingRank_cast {old : FormalState} (d : SlopeData old) :
    (shearingRank d : ℚ) =
      (d.slope.den : ℚ)*((old.shape.rank : ℚ)+1-d.slope)-1 := by
  have he := slope_num_div_den d.slope d.positive.le
  have hden : (d.slope.den : ℚ) ≠ 0 := by exact_mod_cast d.slope.den_ne_zero
  have hn : (d.slope.num.toNat : ℚ) = (d.slope.den : ℚ)*d.slope := by
    apply (div_eq_iff hden).mp at he
    simpa [mul_comm] using he
  dsimp [shearingRank]
  push_cast
  rw [hn]
  ring

theorem shearingRank_stopping {old : FormalState} (d : SlopeData old)
    (hstop : d.slope = (old.shape.rank : ℚ)+1) : shearingRank d = -1 := by
  have h := shearingRank_cast d
  rw [hstop] at h
  norm_num at h
  exact_mod_cast h

#print axioms entry_flattenSeries
#print axioms shearing_clear_laurent
#print axioms gaugeEquation_shearing
#print axioms shearingRank_cast
#print axioms shearingRank_stopping

#print axioms differentialCoefficientZ_nat
#print axioms diagonalGauge_inverses
#print axioms diagonalGauge_derivative
#print axioms gaugeEquation_of_clear_powers
#print axioms shearing_inverses
end WasowLaurentShearing
