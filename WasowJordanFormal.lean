import WasowJordanBasis

/-! Resonant all-order normalization without a preassigned Jordan basis.
A scalar leading eigenvalue is removed and restored explicitly; the constant
coordinate change is constructed from the actual nilpotent part. -/
set_option autoImplicit false
noncomputable section
open Module
namespace WasowJordanFormal
open WasowPowerSeries
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constant scalar matrix commutes with every matrix power series. -/
theorem scalarSeries_commute (μ : ℂ) (P : PowerSeries (Matrix ι ι ℂ)) :
    PowerSeries.C (μ • (1 : Matrix ι ι ℂ)) * P =
      P * PowerSeries.C (μ • (1 : Matrix ι ι ℂ)) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C]
  simp

/-- Scalar shifts do not alter the coefficient commutator, so the normalized
multishift recurrence applies with an arbitrary scalar leading eigenvalue. -/
theorem exists_scalar_multishift_powerSeries {σ : Type} [Fintype σ] [DecidableEq σ]
    (h : σ → ℕ) (μ : ℂ)
    (A : PowerSeries (Matrix (WasowMultiShiftReduction.Index h) (WasowMultiShiftReduction.Index h) ℂ))
    (hA : PowerSeries.constantCoeff A = μ • 1 + WasowMultiShiftReduction.jordanShift h)
    {q : ℕ} (hq : 0 < q) :
    ∃ P B S : PowerSeries (Matrix (WasowMultiShiftReduction.Index h) (WasowMultiShiftReduction.Index h) ℂ),
      PowerSeries.constantCoeff P = 1 ∧ IsUnit P ∧
      PowerSeries.constantCoeff B = PowerSeries.constantCoeff A ∧
      (∀ k a b j, (PowerSeries.coeff (k+1) P) ⟨a,0⟩ ⟨b,j⟩ = 0) ∧
      (∀ k a b i j, i.val < h a → (PowerSeries.coeff (k+1) B) ⟨a,i⟩ ⟨b,j⟩ = 0) ∧
      S * P = 1 ∧ P * S = 1 ∧
      A * P - P * B = -(PowerSeries.X ^ (q+1) * derivative P) := by
  let C : PowerSeries (Matrix (WasowMultiShiftReduction.Index h) (WasowMultiShiftReduction.Index h) ℂ) :=
    PowerSeries.C (μ • 1)
  have hD : PowerSeries.constantCoeff (A - C) = WasowMultiShiftReduction.jordanShift h := by
    simp [C, hA]
  obtain ⟨P, B, S, hP0, hPu, hB0, hP, hB, hSP, hPS, heq⟩ :=
    WasowFormalSeries.exists_multishift_powerSeries h (A - C) hD hq
  refine ⟨P, B + C, S, hP0, hPu, ?_, hP, ?_, hSP, hPS, ?_⟩
  · rw [map_add, hB0]
    simp [C]
  · intro k a b i j hi
    simpa [C] using hB k a b i j hi
  · have hc : C * P = P * C := scalarSeries_commute μ P
    calc
      A * P - P * (B + C) = (A - C) * P - P * B := by
        rw [mul_add, sub_mul, hc]
        abel
      _ = _ := heq

/-- For any formal system whose leading matrix has one eigenvalue, construct
its Jordan coordinates and the normalized formal gauge of all orders. -/
theorem exists_single_eigenvalue_normalization (A : PowerSeries (Matrix ι ι ℂ)) (μ : ℂ)
    (hN : IsNilpotent (PowerSeries.constantCoeff A - μ • 1)) {q : ℕ} (hq : 0 < q) :
    ∃ (σ : Type) (_ : Fintype σ) (_ : DecidableEq σ) (h : σ → ℕ)
      (e : Matrix ι ι ℂ ≃ₐ[ℂ] Matrix (WasowMultiShiftReduction.Index h) (WasowMultiShiftReduction.Index h) ℂ)
      (P B S : PowerSeries (Matrix (WasowMultiShiftReduction.Index h) (WasowMultiShiftReduction.Index h) ℂ)),
      e (PowerSeries.constantCoeff A) = μ • 1 + WasowMultiShiftReduction.jordanShift h ∧
      PowerSeries.constantCoeff P = 1 ∧ IsUnit P ∧
      PowerSeries.constantCoeff B = e (PowerSeries.constantCoeff A) ∧
      (∀ k a b j, (PowerSeries.coeff (k+1) P) ⟨a,0⟩ ⟨b,j⟩ = 0) ∧
      (∀ k a b i j, i.val < h a → (PowerSeries.coeff (k+1) B) ⟨a,i⟩ ⟨b,j⟩ = 0) ∧
      S * P = 1 ∧ P * S = 1 ∧
      PowerSeries.map e.toRingHom A * P - P * B =
        -(PowerSeries.X ^ (q+1) * derivative P) := by
  let N := PowerSeries.constantCoeff A - μ • 1
  have hn : IsNilpotent (Matrix.toLin' N) :=
    hN.map (Matrix.toLinAlgEquiv (Pi.basisFun ℂ ι))
  obtain ⟨σ, fσ, dσ, h, b, hb⟩ := WasowJordanBasis.exists_jordan_basis (Matrix.toLin' N) hn
  let := fσ
  let := dσ
  let e : Matrix ι ι ℂ ≃ₐ[ℂ] Matrix (WasowMultiShiftReduction.Index h) (WasowMultiShiftReduction.Index h) ℂ :=
    (Matrix.toLinAlgEquiv (Pi.basisFun ℂ ι)).trans (LinearMap.toMatrixAlgEquiv b)
  have heN : e N = WasowMultiShiftReduction.jordanShift h := by
    change LinearMap.toMatrix b b (Matrix.toLin' N) = _
    exact hb
  have heA : e (PowerSeries.constantCoeff A) = μ • 1 + WasowMultiShiftReduction.jordanShift h := by
    have hh : e (PowerSeries.constantCoeff A) - μ • 1 = WasowMultiShiftReduction.jordanShift h := by
      simpa only [N, map_sub, map_smul, map_one] using heN
    rw [sub_eq_iff_eq_add] at hh
    simpa only [add_comm] using hh
  have hlead : PowerSeries.constantCoeff (PowerSeries.map e.toRingHom A) =
      μ • 1 + WasowMultiShiftReduction.jordanShift h := heA
  obtain ⟨P, B, S, hP0, hPu, hB0, hP, hB, hSP, hPS, heq⟩ :=
    exists_scalar_multishift_powerSeries h μ (PowerSeries.map e.toRingHom A) hlead hq
  exact ⟨σ, fσ, dσ, h, e, P, B, S, heA, hP0, hPu, hB0, hP, hB, hSP, hPS, heq⟩

#print axioms scalarSeries_commute
#print axioms exists_scalar_multishift_powerSeries
#print axioms exists_single_eigenvalue_normalization
end WasowJordanFormal
