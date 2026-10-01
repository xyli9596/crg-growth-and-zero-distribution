import WasowGlobalFormalSplit

/-! Actual complete regular-singular series under ramification and finite
block assembly. Matrix coefficients remain noncommutative throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace WasowGlobalFormalRegular
open WasowLaurentGauge WasowLaurentRamification
open WasowFormalNormalization
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise substitution by `t^p`, defined without assuming commutativity
of the coefficient matrix ring. -/
def expandSeries (p : ℕ) (R : Series ι) : Series ι :=
  PowerSeries.mk (fun n => if p ∣ n then PowerSeries.coeff (n/p) R else 0)

theorem entry_expandSeries (p : ℕ) (hp : 0<p) (R : Series ι) (i j : ι) :
    WasowPowerSeries.entry (expandSeries p R) i j =
      PowerSeries.expand p hp.ne' (WasowPowerSeries.entry R i j) := by
  apply PowerSeries.ext
  intro n
  simp only [WasowPowerSeries.coeff_entry, expandSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_expand]
  split_ifs <;> rfl

theorem toLaurent_expandSeries (p : ℕ) (hp : 0<p) (R : Series ι) :
    toLaurent (expandSeries p R) = ramifyMatrix p hp (toLaurent R) := by
  apply Matrix.ext
  intro i j
  simp only [toLaurent_apply, entry_expandSeries p hp R, ramifyMatrix, ramify_powerSeries]

theorem toLaurent_smul_entry (c : ℂ) (R : Series ι) (i j : ι) :
    toLaurent (c•R) i j = HahnSeries.C c * toLaurent R i j := by
  ext n
  simp only [toLaurent_apply, PowerSeries.coeff_coe, WasowPowerSeries.coeff_entry,
    HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  split_ifs <;> simp_all

/-- A regular-singular differential coefficient, with a complete formal series. -/
def regularCoefficient (R : Series ι) : Matrix ι ι L :=
  fun i j => HahnSeries.single (-1) 1 * toLaurent R i j

/-- The Jacobian multiplies the regular series by `p`; no higher pole is created. -/
theorem pullback_regularCoefficient (p : ℕ) (hp : 0<p) (R : Series ι) :
    pullback p hp (regularCoefficient R) =
      regularCoefficient ((p:ℂ) • expandSeries p R) := by
  apply Matrix.ext
  intro i j
  simp only [pullback, regularCoefficient, map_mul, ramify_single,
    toLaurent_smul_entry, toLaurent_expandSeries p hp R, ramifyMatrix]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  simp only [jacobian, HahnSeries.C_apply, HahnSeries.single_mul_single]
  norm_num
  congr 2
  ring

theorem regularCoefficient_neg (R : Series ι) :
    regularCoefficient (-R) = WasowLaurentShearing.differentialCoefficientZ (-1) R := by
  apply Matrix.ext
  intro i j
  change HahnSeries.single (-1) 1 * toLaurent (-R) i j =
    HahnSeries.single (-(-1:ℤ)-2) (-1) * toLaurent R i j
  rw [map_neg]
  simp
  ring

section Blocks
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {I : σ → Type*} [∀a, Fintype (I a)] [∀a, DecidableEq (I a)]

/-- A complete block series, defined coefficientwise. -/
def blockSeries (R : ∀a, Series (I a)) : Series (Σa,I a) :=
  PowerSeries.mk (fun n => Matrix.blockDiagonal' (fun a => PowerSeries.coeff n (R a)))

theorem toLaurent_blockSeries (R : ∀a, Series (I a)) :
    toLaurent (blockSeries R) = Matrix.blockDiagonal' (fun a => toLaurent (R a)) := by
  apply Matrix.ext
  rintro ⟨a,i⟩ ⟨b,j⟩
  by_cases hab : a=b
  · subst b
    rw [Matrix.blockDiagonal'_apply_eq]
    ext n
    simp [toLaurent_apply, PowerSeries.coeff_coe, WasowPowerSeries.coeff_entry, blockSeries]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab]
    ext n
    simp [toLaurent_apply, PowerSeries.coeff_coe, WasowPowerSeries.coeff_entry,
      blockSeries, Matrix.blockDiagonal'_apply_ne _ _ _ hab]

theorem regularCoefficient_blocks (R : ∀a, Series (I a)) :
    regularCoefficient (blockSeries R) =
      Matrix.blockDiagonal' (fun a => regularCoefficient (R a)) := by
  apply Matrix.ext
  rintro ⟨a,i⟩ ⟨b,j⟩
  simp only [regularCoefficient, toLaurent_blockSeries]
  by_cases hab : a=b
  · subst b
    simp [regularCoefficient]
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hab]

end Blocks

#print axioms entry_expandSeries
#print axioms toLaurent_expandSeries
#print axioms toLaurent_smul_entry
#print axioms pullback_regularCoefficient
#print axioms regularCoefficient_neg
#print axioms toLaurent_blockSeries
#print axioms regularCoefficient_blocks
end WasowGlobalFormalRegular
