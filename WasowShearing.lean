import WasowDiagonal
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Exact integer shearing and the finite rational slope selection

These are individual operations in Wasow §19. They do not assert that one
shearing makes an arbitrary nilpotent leading matrix nonnilpotent, or that the
general reduction terminates. The repeated nilpotent case still requires the
strict decrease of the determinantal-divisor invariants from §19.4.
-/
noncomputable section
open Matrix Set Filter
open scoped Topology BigOperators
namespace WasowShearing

variable {m : ℕ}

def shear {𝕂 : Type*} [Field 𝕂] (k : Fin m → ℤ) (x : 𝕂) : Matrix (Fin m) (Fin m) 𝕂 :=
  Matrix.diagonal (fun i => x ^ k i)

def inverseShear {𝕂 : Type*} [Field 𝕂] (k : Fin m → ℤ) (x : 𝕂) : Matrix (Fin m) (Fin m) 𝕂 :=
  shear (fun i => -k i) x

def derivativeShear {𝕂 : Type*} [Field 𝕂] (k : Fin m → ℤ) (x : 𝕂) : Matrix (Fin m) (Fin m) 𝕂 :=
  Matrix.diagonal (fun i => (k i : 𝕂) * x ^ (k i - 1))

theorem inverseShear_mul_shear {𝕂 : Type*} [Field 𝕂] (k : Fin m → ℤ) {x : 𝕂} (hx : x ≠ 0) :
    inverseShear k x * shear k x = 1 := by
  rw [inverseShear, shear, shear, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← zpow_add₀ hx]
  simp

theorem shear_mul_inverseShear {𝕂 : Type*} [Field 𝕂] (k : Fin m → ℤ) {x : 𝕂} (hx : x ≠ 0) :
    shear k x * inverseShear k x = 1 := by
  rw [inverseShear, shear, shear, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← zpow_add₀ hx]
  simp

theorem shear_hasDerivAt (k : Fin m → ℤ) {r : ℝ} (hr : 0 < r) (i j : Fin m) :
    HasDerivAt (fun t : ℝ => shear k (t : ℂ) i j) (derivativeShear k (r : ℂ) i j) r := by
  by_cases hij : i = j
  · subst j
    have hz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simpa only [shear, derivativeShear, Matrix.diagonal_apply_eq] using
      (hasDerivAt_zpow (k i) (r : ℂ) (Or.inl hz)).comp_ofReal
  · simpa [shear, derivativeShear, Matrix.diagonal_apply, hij] using
      hasDerivAt_const r (0 : ℂ)

/-- Conjugation shifts each entry by its exact integer weight difference. -/
theorem conjugate_shear_apply {𝕂 : Type*} [Field 𝕂] (k : Fin m → ℤ) (A : Matrix (Fin m) (Fin m) 𝕂)
    {x : 𝕂} (hx : x ≠ 0) (i j : Fin m) :
    (inverseShear k x * A * shear k x) i j = x ^ (k j-k i) * A i j := by
  simp only [inverseShear, shear, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [sub_eq_add_neg, zpow_add₀ hx]
  ring

/-- The derivative correction in the exact gauge transform is `diag(kᵢ/x)`. -/
theorem inverseShear_mul_derivative {𝕂 : Type*} [Field 𝕂] (k : Fin m → ℤ) {x : 𝕂} (hx : x ≠ 0) :
    inverseShear k x * derivativeShear k x = Matrix.diagonal (fun i => (k i : 𝕂) / x) := by
  rw [inverseShear, shear, derivativeShear, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  calc
    x ^ (-k i) * ((k i : 𝕂) * x ^ (k i - 1)) =
        (k i : 𝕂) * (x ^ (-k i) * x ^ (k i - 1)) := by ring
    _ = (k i : 𝕂) * x ^ (-1 : ℤ) := by rw [← zpow_add₀ hx]; congr 2; omega
    _ = _ := by simp [div_eq_mul_inv]

/-- The actual transformed coefficient, including the derivative term. -/
theorem exact_transformed_coefficient {𝕂 : Type*} [Field 𝕂] (k : Fin m → ℤ)
    (A : Matrix (Fin m) (Fin m) 𝕂) {x : 𝕂} (hx : x ≠ 0) :
    inverseShear k x * A * shear k x - inverseShear k x * derivativeShear k x =
      (show Matrix (Fin m) (Fin m) 𝕂 from fun i j => x ^ (k j-k i) * A i j) - Matrix.diagonal (fun i => (k i : 𝕂) / x) := by
  rw [inverseShear_mul_derivative k hx]
  congr 1
  ext i j
  exact conjugate_shear_apply k A hx i j

/-- Every integer shearing and its actual inverse have a common polynomial
bound on positive real rays. Negative powers are included. -/
theorem exists_polynomial_mulVec_bounds (k : Fin m → ℤ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r → ∀ v : Fin m → ℂ,
      ‖(shear k (r : ℂ)).mulVec v‖ ≤ r ^ K * ‖v‖ ∧
      ‖(inverseShear k (r : ℂ)).mulVec v‖ ≤ r ^ K * ‖v‖ := by
  let K : ℝ := ∑ i, |(k i : ℝ)|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hki (i : Fin m) : |(k i : ℝ)| ≤ K := by
    dsimp [K]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (k j : ℝ)) (Finset.mem_univ i)
  refine ⟨K, hK, fun r hr v => ?_⟩
  have hbound (w : Fin m → ℤ) (hw : ∀ i, (w i : ℝ) ≤ K) :
      ‖(shear w (r : ℂ)).mulVec v‖ ≤ r ^ K * ‖v‖ := by
    apply WasowDiagonal.diagonal_mulVec_norm_le _ v (Real.rpow_nonneg (by linarith) _)
    intro i
    rw [norm_zpow, Complex.norm_real, Real.norm_of_nonneg (by linarith), ← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le hr (hw i)
  exact ⟨hbound k (fun i => (le_abs_self _).trans (hki i)),
    hbound (fun i => -k i) (fun i => by simpa using (neg_le_abs (k i : ℝ)).trans (hki i))⟩

/-- The lower envelope meets `β=σ` at a positive rational slope. This is the
finite numerical core of the §19.3 choice; it does not assert nonnilpotence. -/
theorem exists_rational_slope {ι : Type*} [Fintype ι] [Nonempty ι]
    (α : ι → ℚ) (d : ι → ℕ) (hα : ∀ i, 0 < α i) :
    ∃ σ : ℚ, 0 < σ ∧ (∀ i, σ ≤ α i - (d i : ℚ) * σ) ∧
      ∃ i, σ = α i - (d i : ℚ) * σ := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i => α i / ((d i : ℚ)+1)) Finset.univ_nonempty
  let σ : ℚ := α i / ((d i : ℚ)+1)
  have hσ : 0 < σ := div_pos (hα i) (by positivity)
  have hle (j : ι) : σ * ((d j : ℚ)+1) ≤ α j := by
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < (d j : ℚ)+1)).mp
    exact hi j (Finset.mem_univ j)
  have heq : σ * ((d i : ℚ)+1) = α i := by dsimp [σ]; field_simp
  refine ⟨σ, hσ, fun j => ?_, i, ?_⟩
  · nlinarith [hle j]
  · nlinarith


/-- The same coefficient identity holds inside the actual rational-function
field; the shearing need not be replaced by an abstract invertibility premise. -/
theorem rational_transformed_coefficient (k : Fin m → ℤ)
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) :
    inverseShear k RatFunc.X * A * shear k RatFunc.X -
        inverseShear k RatFunc.X * derivativeShear k RatFunc.X =
      (show Matrix (Fin m) (Fin m) (RatFunc ℂ) from
        fun i j => RatFunc.X ^ (k j-k i) * A i j) -
      Matrix.diagonal (fun i => (k i : RatFunc ℂ) / RatFunc.X) :=
  exact_transformed_coefficient k A RatFunc.X_ne_zero

/-- A nonzero feedback entry closes a single two-dimensional nilpotent chain
and forces the new leading matrix to be nonnilpotent. This is a genuine
special case, not the multiblock termination assertion of §19.4. -/
theorem feedback_two_not_nilpotent {c : ℂ} (hc : c ≠ 0) :
    ¬ IsNilpotent (!![0, 1; c, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply IsUnit.not_isNilpotent
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_fin_two]
  simp [hc]

end WasowShearing

#print axioms WasowShearing.inverseShear_mul_shear
#print axioms WasowShearing.shear_mul_inverseShear
#print axioms WasowShearing.shear_hasDerivAt
#print axioms WasowShearing.conjugate_shear_apply
#print axioms WasowShearing.inverseShear_mul_derivative
#print axioms WasowShearing.exact_transformed_coefficient
#print axioms WasowShearing.exists_polynomial_mulVec_bounds
#print axioms WasowShearing.exists_rational_slope

#print axioms WasowShearing.rational_transformed_coefficient
#print axioms WasowShearing.feedback_two_not_nilpotent
