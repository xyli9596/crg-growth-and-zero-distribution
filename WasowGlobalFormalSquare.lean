import WasowGlobalFormalTree

/-! Final column reindexing of the genuine global Laurent gauge to the original
matrix index. The dimension equality follows from its actual two-sided inverse. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace WasowGlobalFormalSquare
open WasowLaurentGauge WasowLaurentRamification WasowGlobalFormalEdges
open WasowGlobalFormalRegular WasowGlobalFormalCanonical WasowGlobalFormalAssembly
open WasowGlobalFormalTree WasowFormalNormalization
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem change_card {A : Matrix ι ι L} {B : Matrix κ κ L} (f : Change A B) :
    Fintype.card ι = Fintype.card κ := by
  have ht := Matrix.trace_mul_comm f.G f.H
  rw [f.GH, f.HG, Matrix.trace_one, Matrix.trace_one] at ht
  have ht' : (HahnSeries.C (Fintype.card ι : ℂ) : L) = HahnSeries.C (Fintype.card κ : ℂ) := by
    simpa only [map_natCast] using ht
  have hc := congrArg (fun f : L => f.coeff 0) ht'
  simp only [HahnSeries.C_apply, HahnSeries.coeff_single_same] at hc
  exact_mod_cast hc

/-- Column permutation preserves the full canonical coefficient and its phase fibers. -/
def reindexData (N : NormalData κ) (e : ι ≃ κ) : NormalData ι where
  phase := fun i => N.phase (e i)
  phase_zero := fun i => N.phase_zero (e i)
  regular := PowerSeries.map (Matrix.reindexAlgEquiv ℂ ℂ e.symm).toRingHom N.regular
  separated := by
    intro n i j hij
    rw [PowerSeries.coeff_map]
    exact N.separated n (e i) (e j) hij

theorem coefficient_reindexData (N : NormalData κ) (e : ι ≃ κ) :
    coefficient (reindexData N e) = (coefficient N).submatrix e e := by
  apply Matrix.ext
  intro i j
  have hr : toLaurent (PowerSeries.map (Matrix.reindexAlgEquiv ℂ ℂ e.symm).toRingHom
      N.regular) i j = toLaurent N.regular (e i) (e j) := by
    ext n
    simp [toLaurent_apply, PowerSeries.coeff_coe, WasowPowerSeries.coeff_entry]
  simp only [coefficient, reindexData, Matrix.add_apply, Matrix.submatrix_apply,
    regularCoefficient]
  rw [hr]
  simp only [Matrix.diagonal_apply, e.injective.eq_iff]

/-- Only the output columns are reordered; the original input coordinates stay fixed. -/
def squareChange {A : Matrix ι ι L} {B : Matrix κ κ L}
    (f : Change A B) (e : ι ≃ κ) : Change A (B.submatrix e e) where
  G := f.G.submatrix id e
  H := f.H.submatrix e id
  GH := by
    rw [Matrix.submatrix_mul_equiv, f.GH]
    rfl
  HG := by
    change f.H.submatrix e (Equiv.refl ι) * f.G.submatrix (Equiv.refl ι) e=1
    rw [Matrix.submatrix_mul_equiv, f.HG, Matrix.submatrix_one_equiv]
  equation := by
    unfold GaugeEquation
    change A.submatrix id (Equiv.refl ι) * f.G.submatrix (Equiv.refl ι) e -
      f.G.submatrix id e * B.submatrix e e = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    change (A*f.G-f.G*B).submatrix id e = _
    rw [f.equation]
    rfl

/-- Square global data directly usable by finite Laurent truncation. -/
structure SquareRealization (A : Matrix ι ι L) where
  denominator : ℕ
  positive : 0 < denominator
  normal : NormalData ι
  change : Change (pullback denominator positive A) (coefficient normal)

def toSquare {A : Matrix ι ι L} (R : Realization A) : SquareRealization A := by
  let e : ι ≃ R.index := Fintype.equivOfCardEq (change_card R.change)
  refine ⟨R.denominator, R.positive, reindexData R.normal e, ?_⟩
  rw [coefficient_reindexData]
  exact squareChange R.change e

/-- An arbitrary full matrix series admits a single square Laurent normalizing
gauge, its actual inverse, and a fixed finite polynomial phase family. -/
theorem exists_square_global_realization (A : Series ι) (q : ℕ) :
    Nonempty (SquareRealization (differentialCoefficient q A)) := by
  obtain ⟨R⟩ := exists_global_realization A q
  exact ⟨toSquare R⟩

/-- Expanded form of the genuine formal normal-form result. All parameters
are chosen from the full coefficient series, before any ray is introduced. -/
theorem exists_global_formal_normal_form (A : Series ι) (q : ℕ) :
    ∃ p : ℕ, ∃ hp : 0<p, ∃ F : ι → Polynomial ℂ, ∃ R : Series ι,
      ∃ G H : Matrix ι ι L,
      (∀i, (F i).coeff 0=0) ∧
      (∀n i j, F i ≠ F j → PowerSeries.coeff n R i j=0) ∧
      G*H=1 ∧ H*G=1 ∧
      GaugeEquation (pullback p hp (differentialCoefficient q A)) G
        (Matrix.diagonal (fun i => D (WasowLaurentPhase.phaseLaurent (F i))) +
          regularCoefficient R) := by
  obtain ⟨W⟩ := exists_square_global_realization A q
  exact ⟨W.denominator, W.positive, W.normal.phase, W.normal.regular,
    W.change.G, W.change.H, W.normal.phase_zero, W.normal.separated,
    W.change.GH, W.change.HG, W.change.equation⟩

#print axioms exists_global_formal_normal_form

#print axioms change_card
#print axioms reindexData
#print axioms coefficient_reindexData
#print axioms squareChange
#print axioms toSquare
#print axioms exists_square_global_realization
end WasowGlobalFormalSquare
