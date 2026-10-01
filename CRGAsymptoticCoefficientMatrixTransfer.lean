import CRGAsymptoticCoefficientQuotient
import WasowGlobalRayData

/-! Scalar entry expansions imply the operator-norm matrix expansion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology BigOperators Matrix.Norms.Operator
open Filter Asymptotics
namespace CRGAsymptoticCoefficientMatrixTransfer
open WasowMatrixPolynomial
variable {m : ℕ}

/-- Finite matrix polynomial evaluation commutes with extracting an entry. -/
theorem eval_trunc_entry (A : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (N : ℕ) (z : ℂ)
    (i j : Fin m) :
    eval (PowerSeries.trunc N A) z i j = (PowerSeries.trunc N (WasowPowerSeries.entry A i j)).eval z := by
  rw [WasowGlobalRayData.eval_trunc_sum]
  change (∑n∈Finset.range N,z^n • PowerSeries.coeff n A) i j = _
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  change _ = Polynomial.eval₂ (RingHom.id ℂ) z (PowerSeries.trunc N (WasowPowerSeries.entry A i j))
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  simp only [RingHom.id_apply,WasowPowerSeries.coeff_entry,mul_comm]

/-- Finite-dimensional assembly of all scalar estimates in the genuine
matrix infinity operator norm. -/
theorem isBigO_matrix_of_entries {l : Filter ℂ}
    {f : ℂ → Matrix (Fin m) (Fin m) ℂ} {g : ℂ → ℝ}
    (hf : ∀i j,(fun z => f z i j) =O[l] g) : f =O[l] g := by
  classical
  let E : Fin m → Fin m → Matrix (Fin m) (Fin m) ℂ :=
    fun i j => Matrix.single i j 1
  have hh : ∀i∈(Finset.univ : Finset (Fin m)),
      (fun z => ∑j:Fin m,f z i j • E i j) =O[l] g := by
    intro i _hi
    have hj : ∀j∈(Finset.univ : Finset (Fin m)),(fun z => f z i j • E i j) =O[l] g := by
      intro j _hj
      have hconst : (fun _ : ℂ => E i j) =O[l] (fun _ : ℂ => (1:ℝ)) :=
        isBigO_const_of_tendsto tendsto_const_nhds (by norm_num)
      simpa only [smul_eq_mul,mul_one] using (hf i j).smul hconst
    exact (IsBigO.sum hj).congr_left (fun z => by simp only [Finset.sum_apply])
  apply (IsBigO.sum hh).congr_left
  intro z
  simp only [Finset.sum_apply]
  ext i j
  simp [E,Matrix.sum_apply,Matrix.single_apply,ite_and]

/-- No matrix-norm estimate is an extra coefficient assumption: it follows
from exactly the finitely many scalar complete expansions. -/
theorem completeExpansion_of_entries
    {l : Filter ℂ} {c : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {A : PowerSeries (Matrix (Fin m) (Fin m) ℂ)}
    (hc : ∀i j,CRGAsymptoticCoefficientQuotient.CompleteExpansion l
      (fun z => c z i j) (WasowPowerSeries.entry A i j)) :
    CRGAsymptoticCoefficientCompleteExpansion.CompleteExpansion l c A := by
  intro N
  apply isBigO_matrix_of_entries
  intro i j
  simpa only [Matrix.sub_apply,eval_trunc_entry] using hc i j N

/-- A finite polynomial has its exact formal power-series expansion. -/
theorem polynomial_completeExpansion {l : Filter ℂ} (hl : l ≤ 𝓝 (0:ℂ)) (P : Polynomial ℂ) :
    CRGAsymptoticCoefficientQuotient.CompleteExpansion l (fun z => P.eval z) P := by
  intro N
  have hf := CRGAsymptoticCoefficientQuotient.isBigO_polynomial_of_X_pow_dvd
    (P-PowerSeries.trunc N (P:PowerSeries ℂ)) N (by
      apply Polynomial.X_pow_dvd_iff.mpr
      intro k hk
      rw [Polynomial.coeff_sub,PowerSeries.coeff_trunc,if_pos hk,Polynomial.coeff_coe,sub_self])
  simpa only [Polynomial.eval_sub] using hf.mono hl

/-- Scalar sign changes preserve the exact full formal coefficients. -/
theorem completeExpansion_neg {l : Filter ℂ} {f : ℂ → ℂ} {A : PowerSeries ℂ}
    (hf : CRGAsymptoticCoefficientQuotient.CompleteExpansion l f A) :
    CRGAsymptoticCoefficientQuotient.CompleteExpansion l (fun z => -f z) (-A) := by
  intro N
  exact ((hf N).neg_left).congr_left (fun z => by
    rw [map_neg,Polynomial.eval_neg]
    ring)

#print axioms eval_trunc_entry
#print axioms isBigO_matrix_of_entries
#print axioms completeExpansion_of_entries
#print axioms polynomial_completeExpansion
#print axioms completeExpansion_neg
end CRGAsymptoticCoefficientMatrixTransfer
