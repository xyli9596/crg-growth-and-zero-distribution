import WasowLeadingBlocks
import Mathlib.Algebra.GCDMonoid.Finset

/-! Determinants of rectangular products expanded over all row selections.
Repeated selections vanish automatically; embeddings are not required. This
is the multilinear form needed for determinantal-divisor invariance. -/
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace WasowMinorExpansion

/-- Exact multilinear expansion of a rectangular matrix product determinant. -/
theorem det_rectangular_mul {R ι κ : Type*} [CommRing R]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix κ ι R) (B : Matrix ι κ R) :
    (A * B).det = ∑ f : κ → ι, (∏ i, A i (f i)) * (B.submatrix f id).det := by
  classical
  let d := (Matrix.detRowAlternating : (κ → R) [⋀^κ]→ₗ[R] R).toMultilinearMap
  have he : A * B = fun i => ∑ j, A i j • B j := by
    ext i k
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  change d (fun i => ∑ j, A i j • B j) = _
  rw [d.map_sum]
  apply Finset.sum_congr rfl
  intro f _
  exact d.map_smul_univ (fun i => A i (f i)) (fun i => B (f i))

/-- Any common divisor of all selected minors of the right factor divides
every minor of the product, without invertibility assumptions. -/
theorem dvd_minor_mul {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι R) (k : ℕ) (d : R)
    (hd : ∀ r c : Fin k → ι, d ∣ (B.submatrix r c).det)
    (r c : Fin k → ι) : d ∣ ((A*B).submatrix r c).det := by
  rw [Matrix.submatrix_mul A B r id c Function.bijective_id, det_rectangular_mul]
  apply Finset.dvd_sum
  intro f _
  apply dvd_mul_of_dvd_right
  simpa only [Matrix.submatrix_submatrix, Function.id_comp, Function.comp_id] using hd f c

/-- The corresponding statement for common divisors of the left factor. -/
theorem dvd_minor_mul_left {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι R) (k : ℕ) (d : R)
    (hd : ∀ r c : Fin k → ι, d ∣ (A.submatrix r c).det)
    (r c : Fin k → ι) : d ∣ ((A*B).submatrix r c).det := by
  have htrans : ∀ r c : Fin k → ι, d ∣ (A.transpose.submatrix r c).det := by
    intro r c
    change d ∣ (A.submatrix c r).transpose.det
    rw [Matrix.det_transpose]
    exact hd c r
  have hh := dvd_minor_mul B.transpose A.transpose k d htrans c r
  rw [← Matrix.transpose_mul] at hh
  change d ∣ ((A*B).submatrix r c).transpose.det at hh
  simpa only [Matrix.det_transpose] using hh

end WasowMinorExpansion
#print axioms WasowMinorExpansion.det_rectangular_mul
#print axioms WasowMinorExpansion.dvd_minor_mul
#print axioms WasowMinorExpansion.dvd_minor_mul_left
