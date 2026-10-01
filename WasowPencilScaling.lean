import WasowPencilCoordinates

/-! Nonzero scalar factors produced by actual ramification preserve the full
characteristic-pencil degree invariant. The eigenvalue and nilpotence scaling
are handled explicitly, so the ramification factor is never silently removed. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace WasowPencilScaling
open WasowPencilReduction WasowReductionDescent WasowPencilDescent

/-- Invertible substitution of the polynomial variable by `X/c`. -/
def scaleEquiv (c : ℂ) (hc : c ≠ 0) : ℂ[X] ≃ₐ[ℂ] ℂ[X] :=
  Polynomial.algEquivOfCompEqX (Polynomial.C c⁻¹ * X) (Polynomial.C c * X)
    (by simp [← mul_assoc, ← Polynomial.C_mul, hc])
    (by simp [← mul_assoc, ← Polynomial.C_mul, hc])

theorem scaleEquiv_apply (c : ℂ) (hc : c ≠ 0) (p : ℂ[X]) :
    scaleEquiv c hc p = p.comp (Polynomial.C c⁻¹ * X) := by
  simp [scaleEquiv, ← Polynomial.comp_eq_aeval]

theorem natDegree_scaleEquiv (c : ℂ) (hc : c ≠ 0) (p : ℂ[X]) :
    (scaleEquiv c hc p).natDegree = p.natDegree := by
  rw [scaleEquiv_apply, Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul_X _ (inv_ne_zero hc), mul_one]

variable {ι : Type*} [Fintype ι]

theorem degreeMass_scaleEquiv (T : Matrix ι ι ℂ[X]) (c : ℂ) (hc : c ≠ 0) :
    WasowPencilDescent.degreeMass (T.map (scaleEquiv c hc)) =
      WasowPencilDescent.degreeMass T := by
  unfold WasowPencilDescent.degreeMass
  apply Finset.sum_congr rfl
  intro k _
  have hh := Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_eq_degree_of_associated
      (WasowPencilSimilarity.minorGCD_map_associated T (scaleEquiv c hc).toRingEquiv k))
  exact hh.symm.trans (natDegree_scaleEquiv c hc _)

/-- Multiplication by a nonzero constant polynomial is an actual invertible
row transformation, hence leaves every normalized determinantal divisor fixed. -/
theorem minorGCD_smul_C [DecidableEq ι] (T : Matrix ι ι ℂ[X])
    (c : ℂ) (hc : c ≠ 0) (k : ℕ) :
    minorGCD (Polynomial.C c • T) k = minorGCD T k := by
  have hi : (Polynomial.C c⁻¹ • (1 : Matrix ι ι ℂ[X])) * (Polynomial.C c • 1) = 1 := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_smul]
  simpa only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one] using
    WasowMinorEquivalence.minorGCD_equivalent
      (Polynomial.C c • (1 : Matrix ι ι ℂ[X])) (Polynomial.C c⁻¹ • 1)
      T 1 1 hi (Matrix.one_mul 1) k

theorem degreeMass_smul_C [DecidableEq ι] (T : Matrix ι ι ℂ[X])
    (c : ℂ) (hc : c ≠ 0) :
    WasowPencilDescent.degreeMass (Polynomial.C c • T) = WasowPencilDescent.degreeMass T := by
  unfold WasowPencilDescent.degreeMass
  simp_rw [minorGCD_smul_C T c hc]

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {h : σ → ℕ}

omit [Fintype σ] in
/-- Exact polynomial identity for the characteristic pencil of the scaled matrix. -/
theorem pencil_smul (C : Matrix (OldIndex h) (OldIndex h) ℂ) (c : ℂ) (hc : c ≠ 0) :
    pencil (c • C) = Polynomial.C c • ((pencil C).map (scaleEquiv c hc)) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    have hi : Polynomial.C c * Polynomial.C c⁻¹ = (1 : ℂ[X]) := by
      rw [← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1]
    simp [pencil, scaleEquiv_apply, smul_eq_mul, mul_sub, ← mul_assoc, hi]
  · simp [pencil, scaleEquiv_apply, hij, smul_eq_mul, Polynomial.C_mul]

/-- The actual nonzero ramification multiplier does not affect degree mass. -/
theorem degreeMass_smul (C : Matrix (OldIndex h) (OldIndex h) ℂ) (c : ℂ) (hc : c ≠ 0) :
    WasowPencilDescent.degreeMass (pencil (c • C)) = WasowPencilDescent.degreeMass (pencil C) := by
  rw [pencil_smul C c hc, degreeMass_smul_C _ c hc, degreeMass_scaleEquiv _ c hc]

/-- The translated eigenvalue scales by `1/c`; nilpotence is proved using
the actual scalar multiplication of the translated matrix. -/
theorem isNilpotent_unscale [DecidableEq ι] (C : Matrix ι ι ℂ)
    (c α : ℂ) (hc : c ≠ 0) (hN : IsNilpotent (c • C - α • 1)) :
    IsNilpotent (C - (α / c) • 1) := by
  have he : c⁻¹ • (c • C - α • 1) = C - (α / c) • 1 := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul, smul_smul]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  rw [← he]
  exact hN.smul c⁻¹

#print axioms scaleEquiv_apply
#print axioms natDegree_scaleEquiv
#print axioms degreeMass_scaleEquiv
#print axioms minorGCD_smul_C
#print axioms degreeMass_smul_C
#print axioms pencil_smul
#print axioms degreeMass_smul
#print axioms isNilpotent_unscale
end WasowPencilScaling
