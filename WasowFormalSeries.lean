import WasowPowerSeries
import WasowFormalRecurrence
import WasowMultiBlockReduction

/-! Genuine invertible formal power-series gauges obtained from the all-order
coefficient constructions. All products live in the noncommutative matrix
coefficient ring; this is a formal result, not a convergence assertion. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowFormalSeries
open WasowPowerSeries WasowFormalRecurrence
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The all-order block recursion yields an actual formal unit and a block
normal form satisfying the exact formal differential gauge equation. -/
theorem exists_block_powerSeries {α β : ℂ} (hαβ : α ≠ β)
    {N : Matrix m m ℂ} {M : Matrix n n ℂ}
    (hN : IsNilpotent N) (hM : IsNilpotent M)
    (A : PowerSeries (Matrix (m ⊕ n) (m ⊕ n) ℂ))
    (hA : PowerSeries.constantCoeff A = Matrix.fromBlocks (α • 1 + N) 0 0 (β • 1 + M))
    {q : ℕ} (hq : 0 < q) :
    ∃ P B S : PowerSeries (Matrix (m ⊕ n) (m ⊕ n) ℂ),
      PowerSeries.constantCoeff P = 1 ∧ IsUnit P ∧
      PowerSeries.constantCoeff B = PowerSeries.constantCoeff A ∧
      (∀ k, (PowerSeries.coeff (k+1) P).toBlocks₁₁ = 0 ∧
        (PowerSeries.coeff (k+1) P).toBlocks₂₂ = 0) ∧
      (∀ k, (PowerSeries.coeff k B).toBlocks₁₂ = 0 ∧
        (PowerSeries.coeff k B).toBlocks₂₁ = 0) ∧
      S * P = 1 ∧ P * S = 1 ∧
      A * P - P * B = -(PowerSeries.X ^ (q+1) * derivative P) := by
  have hAc : (fun k => PowerSeries.coeff k A) 0 =
      Matrix.fromBlocks (α • 1 + N) 0 0 (β • 1 + M) := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hA
  obtain ⟨P, B, hP0, hB0, hP, hB, heq⟩ :=
    exists_formal_block_reduction hαβ hN hM (fun k => PowerSeries.coeff k A) hAc hq
  obtain ⟨S, hSP, hPS⟩ := exists_inverse_of_constant_one P hP0
  have hmk : PowerSeries.mk (fun k => PowerSeries.coeff k A) = A := by
    apply PowerSeries.ext
    intro k
    exact PowerSeries.coeff_mk _ _
  refine ⟨PowerSeries.mk P, PowerSeries.mk B, S, ?_,
    isUnit_of_constant_one P hP0, ?_, ?_, ?_, hSP, hPS, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hP0]
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hB0,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simpa only [PowerSeries.coeff_mk] using hP
  · simpa only [PowerSeries.coeff_mk] using hB
  · have hh := equation_of_coefficients (fun k => PowerSeries.coeff k A) P B q
      (by simpa only [derivativeCoeff] using heq)
    simpa only [hmk] using hh

/-- The formal power-series equation for an arbitrary finite family of
single-eigenvalue blocks, with arbitrary nilpotent parts inside the blocks. -/
theorem exists_multiblock_powerSeries {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h : σ → ℕ) (eigenvalue : σ → ℂ)
    (N : ∀ a, Matrix (Fin (h a+1)) (Fin (h a+1)) ℂ)
    (heigenvalue : Function.Injective eigenvalue) (hN : ∀ a, IsNilpotent (N a))
    (A : PowerSeries (Matrix (WasowMultiShiftReduction.Index h) (WasowMultiShiftReduction.Index h) ℂ))
    (hA : PowerSeries.constantCoeff A = WasowMultiBlockReduction.leading h eigenvalue N)
    {q : ℕ} (hq : 0 < q) :
    ∃ P B S : PowerSeries (Matrix (WasowMultiShiftReduction.Index h) (WasowMultiShiftReduction.Index h) ℂ),
      PowerSeries.constantCoeff P = 1 ∧ IsUnit P ∧
      PowerSeries.constantCoeff B = PowerSeries.constantCoeff A ∧
      (∀ k a i j, (PowerSeries.coeff (k+1) P) ⟨a,i⟩ ⟨a,j⟩ = 0) ∧
      (∀ k a b, a ≠ b → ∀ i j, (PowerSeries.coeff k B) ⟨a,i⟩ ⟨b,j⟩ = 0) ∧
      S * P = 1 ∧ P * S = 1 ∧
      A * P - P * B = -(PowerSeries.X ^ (q+1) * derivative P) := by
  have hAc : (fun k => PowerSeries.coeff k A) 0 =
      WasowMultiBlockReduction.leading h eigenvalue N := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hA
  obtain ⟨P, B, hP0, hB0, hP, hB, heq⟩ :=
    WasowMultiBlockReduction.exists_formal_multiblock_reduction h eigenvalue N heigenvalue hN
      (fun k => PowerSeries.coeff k A) hAc hq
  obtain ⟨S, hSP, hPS⟩ := exists_inverse_of_constant_one P hP0
  have hmk : PowerSeries.mk (fun k => PowerSeries.coeff k A) = A := by
    apply PowerSeries.ext
    intro k
    exact PowerSeries.coeff_mk _ _
  refine ⟨PowerSeries.mk P, PowerSeries.mk B, S, ?_,
    isUnit_of_constant_one P hP0, ?_, ?_, ?_, hSP, hPS, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hP0]
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hB0,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simpa only [PowerSeries.coeff_mk] using hP
  · simpa only [PowerSeries.coeff_mk] using hB
  · have hh := equation_of_coefficients (fun k => PowerSeries.coeff k A) P B q
      (by simpa only [derivativeCoeff] using heq)
    simpa only [hmk] using hh

/-- The actual invertible formal series for row normalization of an arbitrary
finite family of nilpotent Jordan shift blocks. -/
theorem exists_multishift_powerSeries {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h : σ → ℕ)
    (A : PowerSeries (Matrix (WasowMultiShiftReduction.Index h) (WasowMultiShiftReduction.Index h) ℂ))
    (hA : PowerSeries.constantCoeff A = WasowMultiShiftReduction.jordanShift h)
    {q : ℕ} (hq : 0 < q) :
    ∃ P B S : PowerSeries (Matrix (WasowMultiShiftReduction.Index h) (WasowMultiShiftReduction.Index h) ℂ),
      PowerSeries.constantCoeff P = 1 ∧ IsUnit P ∧
      PowerSeries.constantCoeff B = PowerSeries.constantCoeff A ∧
      (∀ k a b j, (PowerSeries.coeff (k+1) P) ⟨a,0⟩ ⟨b,j⟩ = 0) ∧
      (∀ k a b i j, i.val < h a → (PowerSeries.coeff (k+1) B) ⟨a,i⟩ ⟨b,j⟩ = 0) ∧
      S * P = 1 ∧ P * S = 1 ∧
      A * P - P * B = -(PowerSeries.X ^ (q+1) * derivative P) := by
  have hAc : (fun k => PowerSeries.coeff k A) 0 = WasowMultiShiftReduction.jordanShift h := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hA
  obtain ⟨P, B, hP0, hB0, hP, hB, heq⟩ :=
    WasowMultiShiftReduction.exists_formal_multishift_reduction h
      (fun k => PowerSeries.coeff k A) hAc hq
  obtain ⟨S, hSP, hPS⟩ := exists_inverse_of_constant_one P hP0
  have hmk : PowerSeries.mk (fun k => PowerSeries.coeff k A) = A := by
    apply PowerSeries.ext
    intro k
    exact PowerSeries.coeff_mk _ _
  refine ⟨PowerSeries.mk P, PowerSeries.mk B, S, ?_,
    isUnit_of_constant_one P hP0, ?_, ?_, ?_, hSP, hPS, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hP0]
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hB0,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simpa only [PowerSeries.coeff_mk] using hP
  · simpa only [PowerSeries.coeff_mk] using hB
  · have hh := equation_of_coefficients (fun k => PowerSeries.coeff k A) P B q
      (by simpa only [derivativeCoeff] using heq)
    simpa only [hmk] using hh

#print axioms exists_block_powerSeries
#print axioms exists_multiblock_powerSeries
#print axioms exists_multishift_powerSeries
end WasowFormalSeries
