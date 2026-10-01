import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
Determinantal divisors for the polynomial matrices in Wasow's reduction.
All row and column selectors are included; repetitions contribute zero minors.
The strict descent below is proved from the entries of the reduced triangular
polynomial matrix, rather than supplied as a hypothesis about an invariant.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
open Polynomial
namespace WasowReductionDescent

variable {ι : Type*} [Fintype ι]

/-- The normalized gcd of the minors of order `k`. -/
def minorGCD (T : Matrix ι ι (Polynomial ℂ)) (k : ℕ) : Polynomial ℂ :=
  Finset.univ.gcd (fun s : (Fin k → ι) × (Fin k → ι) =>
    (T.submatrix s.1 s.2).det)

theorem minorGCD_dvd_minor (T : Matrix ι ι (Polynomial ℂ)) (k : ℕ)
    (r c : Fin k → ι) : minorGCD T k ∣ (T.submatrix r c).det := by
  exact Finset.gcd_dvd (f := fun s : (Fin k → ι) × (Fin k → ι) =>
    (T.submatrix s.1 s.2).det) (Finset.mem_univ (r,c))

theorem dvd_minorGCD_iff (T : Matrix ι ι (Polynomial ℂ)) (k : ℕ)
    (p : Polynomial ℂ) : p ∣ minorGCD T k ↔
      ∀ r c : Fin k → ι, p ∣ (T.submatrix r c).det := by
  simp only [minorGCD, Finset.dvd_gcd_iff, Finset.mem_univ, forall_true_left,
    Prod.forall]

omit [Fintype ι] in
theorem det_submatrix_eq_zero_of_not_injective
    (T : Matrix ι ι (Polynomial ℂ)) (k : ℕ) (r c : Fin k → ι)
    (hr : ¬ Function.Injective r) : (T.submatrix r c).det = 0 := by
  classical
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hr
  exact Matrix.det_zero_of_row_eq hne (by ext l; simp [Matrix.submatrix, hij])

omit [Fintype ι] in
/-- Every principal minor of a triangular matrix is the product of its
selected diagonal entries, even if the selector does not preserve order. -/
theorem det_principal_submatrix [LinearOrder ι]
    (T : Matrix ι ι (Polynomial ℂ)) (hT : T.IsLowerTriangular)
    (k : ℕ) (r : Fin k → ι) (hr : Function.Injective r) :
    (T.submatrix r r).det = ∏ i, T (r i) (r i) := by
  let : LinearOrder (Fin k) := LinearOrder.lift' r hr
  apply Matrix.det_of_isLowerTriangular
  intro i j hij
  exact hT hij

/-- A triangular matrix has determinantal divisors dividing those of its
diagonal matrix. This proves the weak part of the actual invariant decrease. -/
theorem minorGCD_dvd_diagonal [LinearOrder ι]
    (T : Matrix ι ι (Polynomial ℂ)) (hT : T.IsLowerTriangular) (k : ℕ) :
    minorGCD T k ∣ minorGCD (Matrix.diagonal (fun i => T i i)) k := by
  classical
  rw [dvd_minorGCD_iff]
  intro r c
  by_cases hr : Function.Injective r
  · have hdiv := minorGCD_dvd_minor T k r r
    rw [det_principal_submatrix T hT k r hr] at hdiv
    have heq : (Matrix.diagonal (fun i => T i i)).submatrix r c =
        Matrix.of (fun i j => T (r i) (r i) *
          (if r i = c j then (1 : Polynomial ℂ) else 0)) := by
      ext i j
      by_cases he : r i = c j <;> simp [Matrix.submatrix, Matrix.diagonal, he]
    rw [heq, Matrix.det_mul_column (fun i => T (r i) (r i))
      (fun i j => if r i = c j then (1 : Polynomial ℂ) else 0)]
    exact dvd_mul_of_dvd_left hdiv _
  · rw [det_submatrix_eq_zero_of_not_injective _ k r c hr]
    exact dvd_zero _

/-- Increasing finite selections cannot move an index to the left. -/
theorem le_val_of_strictMono {k n : ℕ} (r : Fin k → Fin n)
    (hr : StrictMono r) (i : Fin k) : i.val ≤ (r i).val := by
  have h : ∀ a, ∀ ha : a < k, a ≤ (r ⟨a,ha⟩).val := by
    intro a
    induction a with
    | zero => intro ha; exact Nat.zero_le _
    | succ a ih =>
      intro ha
      have hap : a < k := by omega
      have hp := ih hap
      have hlt := hr (show (⟨a,hap⟩ : Fin k) < ⟨a+1,ha⟩ from by simp)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt hp hlt)
  exact h i.val i.isLt

/-- Among selections of `k` distinct indices, the initial `k` indices have
smallest total weight when the weights are increasing. -/
theorem initial_sum_le_selection {k n : ℕ} (hkn : k ≤ n)
    (m : Fin n → ℕ) (hm : Monotone m) (r : Fin k → Fin n)
    (hr : Function.Injective r) :
    (∑ i : Fin k, m (Fin.castLE hkn i)) ≤ ∑ i : Fin k, m (r i) := by
  classical
  let s : Finset (Fin n) := Finset.univ.image r
  have hs : s.card = k := by
    simp [s, Finset.card_image_of_injective _ hr]
  let e := s.orderEmbOfFin hs
  have he : Function.Injective e := e.injective
  have him : Finset.univ.image e = s := s.image_orderEmbOfFin_univ hs
  calc
    _ ≤ ∑ i : Fin k, m (e i) := Finset.sum_le_sum fun i _ =>
      hm (le_val_of_strictMono e e.strictMono i)
    _ = ∑ j ∈ s, m j := by rw [← him, Finset.sum_image (by exact he.injOn)]
    _ = _ := by exact Finset.sum_image (by exact hr.injOn)

omit [Fintype ι] in
/-- Every diagonal minor factors by the product of its selected row entries. -/
theorem det_diagonal_submatrix [DecidableEq ι] (d : ι → Polynomial ℂ) (k : ℕ)
    (r c : Fin k → ι) :
    ((Matrix.diagonal d).submatrix r c).det =
      (∏ i, d (r i)) * (Matrix.of (fun i j =>
        if r i = c j then (1 : Polynomial ℂ) else 0)).det := by
  classical
  have heq : (Matrix.diagonal d).submatrix r c =
      Matrix.of (fun i j => d (r i) *
        (if r i = c j then (1 : Polynomial ℂ) else 0)) := by
    ext i j
    by_cases he : r i = c j <;> simp [Matrix.submatrix, Matrix.diagonal, he]
  rw [heq, Matrix.det_mul_column (fun i => d (r i))
    (fun i j => if r i = c j then (1 : Polynomial ℂ) else 0)]
  rfl

/-- The initial principal minor of a diagonal matrix of powers of `X`. -/
theorem diagonal_initial_minor {n k : ℕ} (hkn : k ≤ n) (m : Fin n → ℕ) :
    ((Matrix.diagonal (fun i => (X : Polynomial ℂ)^m i)).submatrix
      (Fin.castLE hkn) (Fin.castLE hkn)).det =
      X ^ (∑ i : Fin k, m (Fin.castLE hkn i)) := by
  have he : ((Matrix.diagonal (fun i => (X : Polynomial ℂ)^m i)).submatrix
      (Fin.castLE hkn) (Fin.castLE hkn)) =
      Matrix.diagonal (fun i => (X : Polynomial ℂ)^m (Fin.castLE hkn i)) := by
    ext i j
    simp [Matrix.submatrix, Matrix.diagonal, Fin.castLE_inj]
  rw [he, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]

/-- The determinantal divisor of an ordered diagonal matrix has exactly the
sum of its smallest `k` exponents as degree. -/
theorem natDegree_minorGCD_diagonal {n k : ℕ} (hkn : k ≤ n)
    (m : Fin n → ℕ) (hm : Monotone m) :
    (minorGCD (Matrix.diagonal (fun i => (X : Polynomial ℂ)^m i)) k).natDegree =
      ∑ i : Fin k, m (Fin.castLE hkn i) := by
  let D : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
    Matrix.diagonal (fun i => X^m i)
  let d := ∑ i : Fin k, m (Fin.castLE hkn i)
  have hgd : minorGCD D k ∣ X^d := by
    simpa only [D, d, diagonal_initial_minor hkn m] using
      minorGCD_dvd_minor D k (Fin.castLE hkn) (Fin.castLE hkn)
  have hne : (X : Polynomial ℂ)^d ≠ 0 := pow_ne_zero _ X_ne_zero
  have hg : minorGCD D k ≠ 0 := ne_zero_of_dvd_ne_zero hne hgd
  have hdg : (X : Polynomial ℂ)^d ∣ minorGCD D k := by
    rw [dvd_minorGCD_iff]
    intro r c
    by_cases hr : Function.Injective r
    · change (X : Polynomial ℂ)^d ∣ ((Matrix.diagonal (fun i =>
        (X : Polynomial ℂ)^m i)).submatrix r c).det
      rw [det_diagonal_submatrix, Finset.prod_pow_eq_pow_sum]
      apply dvd_mul_of_dvd_left
      exact pow_dvd_pow _ (initial_sum_le_selection hkn m hm r hr)
    · rw [det_submatrix_eq_zero_of_not_injective _ k r c hr]
      exact dvd_zero _
  have h₁ := Polynomial.natDegree_le_of_dvd hgd hne
  have h₂ := Polynomial.natDegree_le_of_dvd hdg hg
  simp only [Polynomial.natDegree_X_pow] at h₁ h₂
  exact le_antisymm h₁ h₂

/-- Replace the last row of an initial principal minor. Triangularity gives
an explicit minor exposing an arbitrary entry below the diagonal. -/
theorem det_replaced_last_row_minor {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (Polynomial ℂ)) (hT : T.IsLowerTriangular)
    (ℓ a : Fin n) :
    (T.submatrix
      (fun i : Fin (ℓ.val+1) => if hi : i.val < ℓ.val then
        (⟨i.val, lt_trans hi ℓ.isLt⟩ : Fin n) else a)
      (Fin.castLE (Nat.succ_le_of_lt ℓ.isLt))).det =
    (∏ i : Fin ℓ.val, T (Fin.castLE (Nat.le_of_lt ℓ.isLt) i)
      (Fin.castLE (Nat.le_of_lt ℓ.isLt) i)) * T a ℓ := by
  let r : Fin (ℓ.val+1) → Fin n := fun i =>
    if hi : i.val < ℓ.val then ⟨i.val, lt_trans hi ℓ.isLt⟩ else a
  let c : Fin (ℓ.val+1) → Fin n := Fin.castLE (Nat.succ_le_of_lt ℓ.isLt)
  have ht : (T.submatrix r c).IsLowerTriangular := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have hi : i.val < ℓ.val := by omega
    change T (r i) (c j) = 0
    simp only [r, dif_pos hi]
    exact hT hij'
  change (T.submatrix r c).det = _
  rw [Matrix.det_of_isLowerTriangular _ ht, Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [Matrix.submatrix, r, c, i.isLt]
    rfl
  · simp [Matrix.submatrix, r, c]
    rfl

/-- An actual nonzero reduced entry forces a strict decrease of one
 determinantal-divisor degree. -/
theorem strict_minor_degree_drop {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (Polynomial ℂ))
    (hT : T.IsLowerTriangular) (m : Fin n → ℕ) (hm : Monotone m)
    (hdiag : ∀ i, T i i = X^m i) (ℓ a : Fin n)
    (hentry : T a ℓ ≠ 0) (hdegree : (T a ℓ).natDegree < m ℓ) :
    (minorGCD T (ℓ.val+1)).natDegree <
      (minorGCD (Matrix.diagonal (fun i => (X : Polynomial ℂ)^m i))
        (ℓ.val+1)).natDegree := by
  let r : Fin (ℓ.val+1) → Fin n := fun i =>
    if hi : i.val < ℓ.val then ⟨i.val, lt_trans hi ℓ.isLt⟩ else a
  let c : Fin (ℓ.val+1) → Fin n := Fin.castLE (Nat.succ_le_of_lt ℓ.isLt)
  have he : (T.submatrix r c).det =
      X^(∑ i : Fin ℓ.val, m (Fin.castLE (Nat.le_of_lt ℓ.isLt) i)) * T a ℓ := by
    rw [det_replaced_last_row_minor T hT ℓ a]
    simp only [hdiag, Finset.prod_pow_eq_pow_sum]
  have hne : (T.submatrix r c).det ≠ 0 := by
    rw [he]
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) hentry
  have hle := Polynomial.natDegree_le_of_dvd
    (minorGCD_dvd_minor T (ℓ.val+1) r c) hne
  rw [he, Polynomial.natDegree_X_pow_mul _ hentry] at hle
  rw [natDegree_minorGCD_diagonal (Nat.succ_le_of_lt ℓ.isLt) m hm,
    Fin.sum_univ_castSucc]
  have hlast : Fin.castLE (Nat.succ_le_of_lt ℓ.isLt) (Fin.last ℓ.val) = ℓ := by
    ext; rfl
  rw [hlast]
  have hsum : (∑ i : Fin ℓ.val,
      m (Fin.castLE (Nat.succ_le_of_lt ℓ.isLt) i.castSucc)) =
      ∑ i : Fin ℓ.val, m (Fin.castLE (Nat.le_of_lt ℓ.isLt) i) := by
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [hsum]
  omega

/-- The old diagonal divisors are nonzero for all orders through the size. -/
theorem minorGCD_diagonal_ne_zero {n k : ℕ} (hkn : k ≤ n) (m : Fin n → ℕ) :
    minorGCD (Matrix.diagonal (fun i => (X : Polynomial ℂ)^m i)) k ≠ 0 := by
  apply ne_zero_of_dvd_ne_zero (pow_ne_zero _ X_ne_zero)
  simpa only [diagonal_initial_minor hkn m] using
    minorGCD_dvd_minor (Matrix.diagonal (fun i => (X : Polynomial ℂ)^m i))
      k (Fin.castLE hkn) (Fin.castLE hkn)

/-- All other determinantal-divisor degrees weakly decrease. -/
theorem minor_degree_le_diagonal {n k : ℕ} (hkn : k ≤ n)
    (T : Matrix (Fin n) (Fin n) (Polynomial ℂ)) (hT : T.IsLowerTriangular)
    (m : Fin n → ℕ) (hdiag : ∀ i, T i i = X^m i) :
    (minorGCD T k).natDegree ≤
      (minorGCD (Matrix.diagonal (fun i => (X : Polynomial ℂ)^m i)) k).natDegree := by
  apply Polynomial.natDegree_le_of_dvd _ (minorGCD_diagonal_ne_zero hkn m)
  have hh : (fun i => T i i) = (fun i => (X : Polynomial ℂ)^m i) := funext hdiag
  simpa only [hh] using minorGCD_dvd_diagonal T hT k

/-- A natural-valued descent invariant for fixed-size polynomial matrices. -/
def degreeMass {n : ℕ} (T : Matrix (Fin n) (Fin n) (Polynomial ℂ)) : ℕ :=
  ∑ k : Fin (n+1), (minorGCD T k.val).natDegree

/-- Genuine strict descent, deduced from a nonzero reduced matrix entry.
This is the polynomial-matrix core of the exceptional step in Lemma 19.4. -/
theorem degreeMass_strict_drop {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (Polynomial ℂ))
    (hT : T.IsLowerTriangular) (m : Fin n → ℕ) (hm : Monotone m)
    (hdiag : ∀ i, T i i = X^m i)
    (hentry : ∃ ℓ a, T a ℓ ≠ 0 ∧ (T a ℓ).natDegree < m ℓ) :
    degreeMass T < degreeMass (Matrix.diagonal (fun i => (X : Polynomial ℂ)^m i)) := by
  obtain ⟨ℓ,a,hne,hdeg⟩ := hentry
  apply Finset.sum_lt_sum
  · intro k _
    exact minor_degree_le_diagonal (by omega) T hT m hdiag
  · refine ⟨⟨ℓ.val+1,by omega⟩, Finset.mem_univ _, ?_⟩
    exact strict_minor_degree_drop T hT m hm hdiag ℓ a hne hdeg

#print axioms det_replaced_last_row_minor
#print axioms strict_minor_degree_drop
#print axioms minorGCD_diagonal_ne_zero
#print axioms minor_degree_le_diagonal
#print axioms degreeMass_strict_drop
#print axioms le_val_of_strictMono
#print axioms initial_sum_le_selection
#print axioms det_diagonal_submatrix
#print axioms diagonal_initial_minor
#print axioms natDegree_minorGCD_diagonal
#print axioms minorGCD_dvd_minor
#print axioms dvd_minorGCD_iff
#print axioms det_submatrix_eq_zero_of_not_injective
#print axioms det_principal_submatrix
#print axioms minorGCD_dvd_diagonal
end WasowReductionDescent
