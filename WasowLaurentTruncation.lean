import WasowLaurentGauge
import WasowTruncation
import WasowActualTruncation

/-! Uniform clearing of genuine Laurent matrix poles, followed by finite
polynomial product approximation. Neither cleared constant term is assumed
invertible. Pole orders are fixed before the truncation order is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace WasowLaurentTruncation
open WasowLaurentGauge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def poleOrder (G : Matrix ι ι L) : ℕ := ∑ i, ∑ j, (-(G i j).order).toNat

omit [DecidableEq ι] in
theorem poleOrder_add_order_nonneg (G : Matrix ι ι L) (i j : ι) :
    0 ≤ (poleOrder G : ℤ) + (G i j).order := by
  have h1 : (-(G i j).order).toNat ≤ ∑ j, (-(G i j).order).toNat :=
    Finset.single_le_sum (f := fun j => (-(G i j).order).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h2 : (∑ j, (-(G i j).order).toNat) ≤ poleOrder G :=
    Finset.single_le_sum (f := fun i => ∑ j, (-(G i j).order).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3 : (-(G i j).order).toNat ≤ poleOrder G := h1.trans h2
  omega

def clearedEntry (G : Matrix ι ι L) (i j : ι) : PowerSeries ℂ :=
  PowerSeries.X ^ ((poleOrder G : ℤ) + (G i j).order).toNat * (G i j).powerSeriesPart

def cleared (G : Matrix ι ι L) : PowerSeries (Matrix ι ι ℂ) :=
  PowerSeries.mk (fun n i j => PowerSeries.coeff n (clearedEntry G i j))

@[simp] theorem entry_cleared (G : Matrix ι ι L) (i j : ι) :
    WasowPowerSeries.entry (cleared G) i j = clearedEntry G i j := by
  ext n
  simp [cleared, PowerSeries.coeff_mk]

/-- Actual multiplication by a single common nonnegative power clears every
entry, including zero entries and poles of different orders. -/
theorem toLaurent_cleared (G : Matrix ι ι L) :
    toLaurent (cleared G) = (HahnSeries.single (poleOrder G : ℤ) 1 : L) • G := by
  apply Matrix.ext
  intro i j
  rw [toLaurent_apply, entry_cleared]
  simp only [clearedEntry, PowerSeries.coe_mul, HahnSeries.ofPowerSeries_X_pow,
    Matrix.smul_apply, smul_eq_mul]
  have hn := Int.toNat_of_nonneg (poleOrder_add_order_nonneg G i j)
  rw [hn]
  rw [show (HahnSeries.single ((poleOrder G : ℤ) + (G i j).order) 1 : L) =
    HahnSeries.single (poleOrder G : ℤ) 1 * HahnSeries.single (G i j).order 1 by simp]
  rw [mul_assoc, LaurentSeries.single_order_mul_powerSeriesPart]

/-- The original Laurent matrix is recovered, without any convergence claim. -/
theorem recover_cleared (G : Matrix ι ι L) :
    (HahnSeries.single (-(poleOrder G : ℤ)) 1 : L) • toLaurent (cleared G) = G := by
  rw [toLaurent_cleared, smul_smul]
  simp

/-- The coefficientwise Laurent embedding is genuinely injective. -/
theorem toLaurent_injective : Function.Injective (toLaurent (ι := ι)) := by
  intro F H he
  apply PowerSeries.ext
  intro n
  ext i j
  have hij := congrFun (congrFun he i) j
  have hentry : WasowPowerSeries.entry F i j = WasowPowerSeries.entry H i j :=
    HahnSeries.ofPowerSeries_injective hij
  simpa using congrArg (PowerSeries.coeff n) hentry

/-- Clearing both members of a true Laurent inverse pair preserves its exact
product, with the expected scalar power in place of the identity. -/
theorem cleared_mul (G Q : Matrix ι ι L) (hGQ : G * Q = 1) :
    cleared G * cleared Q = PowerSeries.X ^ (poleOrder G + poleOrder Q) := by
  apply toLaurent_injective
  rw [map_mul, toLaurent_cleared, toLaurent_cleared, toLaurent_X_pow]
  apply Matrix.ext
  intro i j
  have hij := congrFun (congrFun hGQ i) j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at hij ⊢
  rw [← hij, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (HahnSeries.single ((poleOrder G + poleOrder Q : ℕ) : ℤ) 1 : L) =
    HahnSeries.single (poleOrder G : ℤ) 1 * HahnSeries.single (poleOrder Q : ℤ) 1 by simp]
  ring

/-- Both exact identities are available even when both cleared leading
matrices are singular. -/
theorem cleared_inverse_pair (G Q : Matrix ι ι L) (hGQ : G * Q = 1) (hQG : Q * G = 1) :
    cleared G * cleared Q = PowerSeries.X ^ (poleOrder G + poleOrder Q) ∧
    cleared Q * cleared G = PowerSeries.X ^ (poleOrder G + poleOrder Q) := by
  exact ⟨cleared_mul G Q hGQ, by simpa only [Nat.add_comm] using cleared_mul Q G hQG⟩

/-- The finite product differs from its exact scalar monomial only above the
chosen truncation degree. -/
theorem trunc_product_divisible (P Q : PowerSeries (Matrix ι ι ℂ)) (k N : ℕ)
    (hPQ : P * Q = PowerSeries.X ^ k) :
    Polynomial.X ^ N ∣ PowerSeries.trunc N P * PowerSeries.trunc N Q - Polynomial.X ^ k := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro n hn
  have hh := WasowTruncation.coeff_mul_congr_below hn
    (fun j hj => WasowTruncation.coeff_truncation P hj)
    (fun j hj => WasowTruncation.coeff_truncation Q hj)
  rw [hPQ] at hh
  rw [← Polynomial.coeff_coe]
  rw [WasowActualTruncation.coe_sub_noncomm, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X,
    map_sub, hh, sub_self]

#print axioms poleOrder_add_order_nonneg
#print axioms entry_cleared
#print axioms toLaurent_cleared
#print axioms recover_cleared
#print axioms toLaurent_injective
#print axioms cleared_mul
#print axioms cleared_inverse_pair
#print axioms trunc_product_divisible
end WasowLaurentTruncation
