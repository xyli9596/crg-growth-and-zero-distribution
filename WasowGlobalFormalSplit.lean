import WasowGlobalFormalEdges
import WasowLaurentShearing

/-! Concrete Laurent changes for the actual full-series splitting and shearing
edges. No global gauge, convergence, or canonical form is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace WasowGlobalFormalSplit
open WasowLaurentGauge WasowGlobalFormalEdges WasowLaurentRamification
open WasowFormalSuccessor WasowFormalNormalization WasowFormalSplit
open WasowArbitraryFormalBlocks WasowLeadingBlocks WasowLaurentShearing
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Pull back a concrete invertible gauge, including its full chain rule. -/
def ramifyChange {A : Matrix ι ι L} {B : Matrix κ κ L}
    (f : Change A B) (p : ℕ) (hp : 0<p) : Change (pullback p hp A) (pullback p hp B) where
  G := ramifyMatrix p hp f.G
  H := ramifyMatrix p hp f.H
  GH := (ramifyMatrix_inverses p hp f.G f.H f.GH f.HG).1
  HG := (ramifyMatrix_inverses p hp f.G f.H f.GH f.HG).2
  equation := gaugeEquation_ramify p hp A f.G B f.equation

/-- The extracted scalar is the derivative coefficient in the inverse variable. -/
def scalarCoefficient (q : ℕ) (α : ℂ) : L := HahnSeries.single (-(q:ℤ)-2) (-α)

theorem differentialCoefficient_scalar (q : ℕ) (α : ℂ) :
    differentialCoefficient q (PowerSeries.C (α • (1 : Matrix ι ι ℂ))) =
      scalarCoefficient q α • (1 : Matrix ι ι L) := by
  rw [differentialCoefficient, toLaurent_C]
  apply Matrix.ext
  intro i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, scalarCoefficient, HahnSeries.C_apply]
    rw [HahnSeries.single_mul_single]
    simp
  · simp [Matrix.smul_apply, Matrix.map_apply, scalarCoefficient, hij]

theorem differentialCoefficient_restore (q : ℕ) (A : Series ι) (α : ℂ) :
    differentialCoefficient q (A-PowerSeries.C (α•1)) + scalarCoefficient q α•1 =
      differentialCoefficient q A := by
  have hs := differentialCoefficient_scalar (ι:=ι) q α
  unfold differentialCoefficient at *
  rw [map_sub]
  apply Matrix.ext
  intro i j
  have hh := congrArg (fun M : Matrix ι ι L => M i j) hs
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul] at hh ⊢
  rw [← hh]
  ring

/-- The actual spectral basis transforms every coefficient of the series. -/
theorem coordinateSeries_eq (A : Series ι) :
    coordinateSeries A = PowerSeries.map
      (coordinateEquiv (changeMatrix (PowerSeries.constantCoeff A))
        (inverseChangeMatrix (PowerSeries.constantCoeff A))
        (change_mul_inverse _) (inverse_mul_change _)).toRingHom A := by
  apply PowerSeries.ext
  intro n
  rw [coordinateSeries_coeff, PowerSeries.coeff_map]
  rfl

/-- The full split series, not just its leading matrix, is a block matrix. -/
theorem toLaurent_split {A : Series ι} {q : ℕ} (d : BlockData A q) :
    toLaurent d.series = Matrix.blockDiagonal' (fun a => toLaurent (component d a)) := by
  apply Matrix.ext
  rintro ⟨a,i⟩ ⟨b,j⟩
  by_cases hab : a=b
  · subst b
    rw [Matrix.blockDiagonal'_apply_eq]
    apply HahnSeries.ext
    funext n
    simp only [toLaurent_apply, PowerSeries.coeff_coe, WasowPowerSeries.coeff_entry]
    split_ifs
    · rfl
    · rw [component_coeff]
      rfl
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab]
    apply HahnSeries.ext
    funext n
    simp only [toLaurent_apply, PowerSeries.coeff_coe, WasowPowerSeries.coeff_entry,
      HahnSeries.coeff_zero]
    split_ifs
    · rfl
    · exact d.offDiagonal n.natAbs a b hab i j

theorem differentialCoefficient_split {A : Series ι} {q : ℕ} (d : BlockData A q) :
    differentialCoefficient q d.series =
      Matrix.blockDiagonal' (fun a => differentialCoefficient q (component d a)) := by
  rw [differentialCoefficient, toLaurent_split]
  apply Matrix.ext
  rintro ⟨a,i⟩ ⟨b,j⟩
  by_cases hab : a=b
  · subst b
    simp [differentialCoefficient, Matrix.smul_apply]
  · simp [differentialCoefficient, Matrix.smul_apply,
      Matrix.blockDiagonal'_apply_ne _ _ _ hab]

/-- One concrete Laurent gauge realizes the entire actual spectral split. -/
def splitChange {A : Series ι} {q : ℕ} (d : BlockData A q) :
    Change (differentialCoefficient q A)
      (Matrix.blockDiagonal' (fun a => differentialCoefficient q (component d a))) := by
  have hc := constantChange (differentialCoefficient q A)
    (changeMatrix (PowerSeries.constantCoeff A)) (inverseChangeMatrix (PowerSeries.constantCoeff A))
    (change_mul_inverse _) (inverse_mul_change _)
  rw [← differentialCoefficient_coordinate q A _ _
    (change_mul_inverse _) (inverse_mul_change _), ← coordinateSeries_eq] at hc
  have hg := powerSeriesChange q (coordinateSeries A) d.gauge d.series d.inverse
    d.inverse_right d.inverse_left d.equation
  rw [differentialCoefficient_split d] at hg
  exact hc.comp hg

/-- Normalization after removing the scalar is restored by the same actual gauge. -/
def componentChange {A : Series ι} {q : ℕ} (F : Family A q) (a : Spectrum A) :
    Change (differentialCoefficient q (component F.blocks a))
      (differentialCoefficient q (F.child a).series + scalarCoefficient q a.val•1) := by
  have hc := (normalizationChange (F.normalization a)).addScalar (scalarCoefficient q a.val)
  dsimp [translatedComponent] at hc
  rw [differentialCoefficient_restore] at hc
  exact hc

/-- All full-series child normalizations are combined through the actual
spectral gauge and true inverse matrices. -/
def familyChange {A : Series ι} {q : ℕ} (F : Family A q) :
    Change (differentialCoefficient q A)
      (Matrix.blockDiagonal' (fun a =>
        differentialCoefficient q (F.child a).series + scalarCoefficient q a.val•1)) :=
  (splitChange F.blocks).comp (blockChange _ _ (componentChange F))

/-- The actual shearing matrix and its monomial inverse, including the regular stop. -/
def shearChange {old : FormalState} (d : WasowRecursiveTree.SlopeData old) :
    Change (pullback d.slope.den d.slope.den_pos (differentialCoefficient old.shape.rank old.series))
      (differentialCoefficientZ (shearingRank d) (rawSeries old d.slope)) where
  G := shearingGauge d
  H := shearingInverse d
  GH := (shearing_inverses d).1
  HG := (shearing_inverses d).2
  equation := gaugeEquation_shearing d

/-- A continuing single-eigenvalue edge has the same supported slope data. -/
def continuingSlope {old : FormalState} (i : ContinuingInput old) :
    WasowRecursiveTree.SlopeData old where
  slope := i.slope
  positive := i.slope_pos
  bounded := i.nonstopping.le
  weights := i.weights
  feedback := Or.inr i.feedback

theorem shearingRank_eq {old : FormalState} (d : WasowRecursiveTree.SlopeData old)
    (q : ℕ) (hq : (q:ℚ) = (d.slope.den:ℚ)*((old.shape.rank:ℚ)+1-d.slope)-1) :
    shearingRank d = (q:ℤ) := by
  have hh := shearingRank_cast d
  rw [← hq] at hh
  exact_mod_cast hh

/-- Genuine single-eigenvalue successor: actual shearing, constant coordinates,
complete power-series normalization, and the scalar coefficient restored. -/
def singleChange {old next : FormalState} {i : ContinuingInput old}
    (d : SingleData old next i) :
    Change (pullback i.slope.den i.slope.den_pos
      (differentialCoefficient old.shape.rank old.series))
      (differentialCoefficient next.shape.rank next.series +
        scalarCoefficient next.shape.rank i.eigenvalue•1) := by
  have hc := constantChange
    (differentialCoefficient next.shape.rank (rawSeries old i.slope -
      PowerSeries.C (i.eigenvalue•1))) d.P d.Q d.PQ d.QP
  rw [← differentialCoefficient_coordinate _ _ _ _ d.PQ d.QP] at hc
  have hn := hc.comp (powerSeriesChange next.shape.rank _ d.gauge next.series d.inverse
    d.inverse_right d.inverse_left d.equation)
  have ha := hn.addScalar (scalarCoefficient next.shape.rank i.eigenvalue)
  rw [differentialCoefficient_restore] at ha
  have hs := shearChange (continuingSlope i)
  rw [shearingRank_eq (continuingSlope i) next.shape.rank d.rank_update,
    differentialCoefficientZ_nat] at hs
  exact hs.comp ha

#print axioms continuingSlope
#print axioms shearingRank_eq
#print axioms singleChange

#print axioms ramifyChange
#print axioms differentialCoefficient_scalar
#print axioms differentialCoefficient_restore
#print axioms coordinateSeries_eq
#print axioms toLaurent_split
#print axioms differentialCoefficient_split
#print axioms splitChange
#print axioms componentChange
#print axioms familyChange
#print axioms shearChange
end WasowGlobalFormalSplit
