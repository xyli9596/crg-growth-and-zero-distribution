import WasowLeadingBlocks

/-! Full formal eigenvalue-block splitting with the block coordinates actually
constructed from the arbitrary leading matrix. The coordinate map is the
proved constant similarity, not a further hypothesis on the input series. -/
set_option autoImplicit false
noncomputable section
namespace WasowArbitraryFormalBlocks
open WasowLeadingBlocks WasowPowerSeries
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Algebraic coordinate transport commutes with the actual coefficientwise
formal derivative, including its complex scalar factors. -/
theorem map_derivative (e : Matrix ι ι ℂ →ₐ[ℂ] Matrix κ κ ℂ)
    (P : PowerSeries (Matrix ι ι ℂ)) :
    PowerSeries.map e.toRingHom (derivative P) =
      derivative (PowerSeries.map e.toRingHom P) := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, coeff_derivative]
  exact map_smul e ((n+1 : ℕ) : ℂ) (PowerSeries.coeff (n+1) P)

abbrev BlockIndex (A : PowerSeries (Matrix ι ι ℂ)) :=
  MatrixIndex (PowerSeries.constantCoeff A)

def coordinateSeries (A : PowerSeries (Matrix ι ι ℂ)) :
    PowerSeries (Matrix (BlockIndex A) (BlockIndex A) ℂ) :=
  PowerSeries.map (matrixCoordinates (PowerSeries.constantCoeff A)).toRingHom A

/-- Every coefficient is transported by the same actual constant similarity. -/
theorem coordinateSeries_coeff (A : PowerSeries (Matrix ι ι ℂ)) (n : ℕ) :
    PowerSeries.coeff n (coordinateSeries A) =
      inverseChangeMatrix (PowerSeries.constantCoeff A) * PowerSeries.coeff n A *
        changeMatrix (PowerSeries.constantCoeff A) := by
  change matrixCoordinates (PowerSeries.constantCoeff A) (PowerSeries.coeff n A) = _
  exact matrixCoordinates_apply _ _

/-- The input series itself supplies the complete block decomposition of its
constant term; no external basis or splitting is assumed. -/
theorem coordinateSeries_leading (A : PowerSeries (Matrix ι ι ℂ)) :
    PowerSeries.constantCoeff (coordinateSeries A) =
      WasowMultiBlockReduction.leading (blockSize (Matrix.toLin' (PowerSeries.constantCoeff A)))
        (fun a => a.val) (nilpotentBlock (Matrix.toLin' (PowerSeries.constantCoeff A))) := by
  change matrixCoordinates (PowerSeries.constantCoeff A) (PowerSeries.constantCoeff A) = _
  exact matrixCoordinates_leading _

/-- All-order splitting for an arbitrary input matrix series. Its constant
coordinate change has already been constructed with two-sided inverses. -/
theorem exists_arbitrary_formal_block_reduction (A : PowerSeries (Matrix ι ι ℂ))
    {q : ℕ} (hq : 0 < q) :
    ∃ P B S : PowerSeries (Matrix (BlockIndex A) (BlockIndex A) ℂ),
      PowerSeries.constantCoeff P = 1 ∧ IsUnit P ∧
      PowerSeries.constantCoeff B = PowerSeries.constantCoeff (coordinateSeries A) ∧
      (∀ k a i j, (PowerSeries.coeff (k+1) P) ⟨a,i⟩ ⟨a,j⟩ = 0) ∧
      (∀ k a b, a ≠ b → ∀ i j, (PowerSeries.coeff k B) ⟨a,i⟩ ⟨b,j⟩ = 0) ∧
      S * P = 1 ∧ P * S = 1 ∧
      coordinateSeries A * P - P * B = -(PowerSeries.X ^ (q+1) * derivative P) := by
  exact WasowFormalSeries.exists_multiblock_powerSeries
    (blockSize (Matrix.toLin' (PowerSeries.constantCoeff A))) (fun a => a.val)
    (nilpotentBlock (Matrix.toLin' (PowerSeries.constantCoeff A)))
    (eigenvalues_injective _) (nilpotentBlock_isNilpotent _)
    (coordinateSeries A) (coordinateSeries_leading A) hq

#print axioms map_derivative
#print axioms coordinateSeries_coeff
#print axioms coordinateSeries_leading
#print axioms exists_arbitrary_formal_block_reduction
end WasowArbitraryFormalBlocks
