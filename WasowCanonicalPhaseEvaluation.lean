import WasowCanonicalTruncation
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! Evaluation of the fixed canonical phase is the actual complex derivative
of F(1/t). The argument uses only finite Laurent sums; no divergent formal
series is assigned an analytic value. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace WasowCanonicalPhaseEvaluation
open WasowLaurentGauge WasowLaurentPhase WasowCanonicalTruncation
open WasowGlobalFormalCanonical WasowLaurentTruncation WasowLaurentClearing

def evalOn (S : Finset ℤ) (z : ℂ) (f : L) : ℂ := ∑ n ∈ S, f.coeff n * z^n

theorem evalOn_sum_single (S : Finset ℤ) (z : ℂ) (s : Finset ℕ)
    (e : ℕ → ℤ) (c : ℕ → ℂ) (he : ∀i∈s, e i ∈ S) :
    evalOn S z (∑ i ∈ s, HahnSeries.single (e i) (c i)) =
      ∑ i ∈ s, c i*z^(e i) := by
  unfold evalOn
  simp only [HahnSeries.coeff_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [HahnSeries.coeff_single, ite_mul, he i hi]

/-- Equality of finite Laurent sums implies equality of their actual integer-power values. -/
theorem finite_laurent_eval_eq (s t : Finset ℕ) (e f : ℕ → ℤ) (c d : ℕ → ℂ)
    (he : (∑ i∈s, HahnSeries.single (e i) (c i) : L) =
      ∑ j∈t, HahnSeries.single (f j) (d j)) (z : ℂ) :
    (∑ i∈s, c i*z^(e i)) = ∑ j∈t, d j*z^(f j) := by
  let S := s.image e ∪ t.image f
  have hc : ∀i∈s, e i ∈ S := by intro i hi; exact Finset.mem_union_left _ (Finset.mem_image_of_mem e hi)
  have hd : ∀j∈t, f j ∈ S := by intro j hj; exact Finset.mem_union_right _ (Finset.mem_image_of_mem f hj)
  have h := congrArg (evalOn S z) he
  rwa [evalOn_sum_single S z s e c hc, evalOn_sum_single S z t f d hd] at h

theorem phaseDerivative_sum (F : Polynomial ℂ) :
    D (phaseLaurent F) =
      ∑ n∈F.support, HahnSeries.single (-(n : ℤ)-1) (-(n : ℂ)*F.coeff n) := by
  rw [phaseLaurent_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp [D, LaurentSeries.derivative, LaurentSeries.hasseDeriv_single, zsmul_eq_mul]

/-- The same finite sum is the genuine complex derivative of the fixed phase. -/
theorem phase_hasDerivAt (F : Polynomial ℂ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun t : ℂ => F.eval t⁻¹)
      (∑ n∈F.support, (-(n : ℂ)*F.coeff n)*z^(-(n : ℤ)-1)) z := by
  have he : (fun t : ℂ => F.eval t⁻¹) =
      (fun t : ℂ => ∑ n∈F.support, F.coeff n*t^(-(n : ℤ))) := by
    funext t
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp [zpow_neg, zpow_natCast, inv_pow, mul_comm]
  rw [he]
  apply HasDerivAt.fun_sum
  intro n _
  simpa only [Int.cast_neg, Int.cast_natCast, mul_assoc, mul_left_comm] using
    (hasDerivAt_zpow (-(n : ℤ)) z (Or.inl hz)).const_mul (F.coeff n)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem toLaurent_polynomial_entry (P : Polynomial (Matrix ι ι ℂ)) (i j : ι) :
    toLaurent (P : PowerSeries (Matrix ι ι ℂ)) i j =
      ∑ n∈P.support, HahnSeries.single (n : ℤ) (P.coeff n i j) := by
  ext k
  rw [toLaurent_apply, PowerSeries.coeff_coe, HahnSeries.coeff_sum]
  by_cases hk : 0 ≤ k
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simp only [Int.natAbs_natCast,
      WasowPowerSeries.coeff_entry, Polynomial.coeff_coe, HahnSeries.coeff_single,
      Int.natCast_inj]
    by_cases hn : n ∈ P.support
    · simp [hn]
    · simp [hn, Polynomial.notMem_support_iff.mp hn]
  · rw [if_pos (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro n _
    exact HahnSeries.coeff_single_of_ne (by omega)

theorem eval_pole_polynomial_entry (h : ℕ) (P : Polynomial (Matrix ι ι ℂ))
    {z : ℂ} (hz : z ≠ 0) (i j : ι) :
    (z^(-(h : ℤ)) • WasowMatrixPolynomial.eval P z) i j =
      ∑ n∈P.support, P.coeff n i j * z^(-(h : ℤ)+(n : ℤ)) := by
  rw [WasowMatrixPolynomial.eval_eq_sum]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [zpow_add₀ hz, zpow_natCast]
  ring

/-- The phase retained by finite canonical truncation is exactly the actual
complex derivative of the originally fixed polynomial F_i(1/t). -/
theorem phasePolynomial_eval (h : ℕ) (hh : 0 < h) (N : NormalData ι)
    (hp : poleOrder (coefficient N) ≤ h) {z : ℂ} (hz : z ≠ 0) :
    z^(-(h : ℤ)) • WasowMatrixPolynomial.eval (phasePolynomial h N) z =
      Matrix.diagonal (fun i => deriv (fun t : ℂ => (N.phase i).eval t⁻¹) z) := by
  apply Matrix.ext
  intro i j
  have he := congrArg (fun M : Matrix ι ι L => M i j) (recover_phasePolynomial h hh N hp)
  simp only [Matrix.smul_apply, smul_eq_mul, toLaurent_polynomial_entry,
    Finset.mul_sum, HahnSeries.single_mul_single, one_mul] at he
  rw [eval_pole_polynomial_entry h _ hz i j]
  by_cases hij : i=j
  · subst j
    rw [Matrix.diagonal_apply_eq, phaseDerivative_sum] at he
    have hv := finite_laurent_eval_eq (phasePolynomial h N).support (N.phase i).support
      (fun n => -(h : ℤ)+(n : ℤ)) (fun n => -(n : ℤ)-1)
      (fun n => (phasePolynomial h N).coeff n i i)
      (fun n => -(n : ℂ)*(N.phase i).coeff n) he z
    rw [Matrix.diagonal_apply_eq, (phase_hasDerivAt (N.phase i) hz).deriv]
    exact hv
  · rw [Matrix.diagonal_apply_ne _ hij] at he ⊢
    have hv := finite_laurent_eval_eq (phasePolynomial h N).support ∅
      (fun n => -(h : ℤ)+(n : ℤ)) (fun _ => (0 : ℤ))
      (fun n => (phasePolynomial h N).coeff n i j) (fun _ => (0 : ℂ))
      (by simpa only [Finset.sum_empty] using he) z
    simpa only [Finset.sum_empty] using hv

/-- The complete actual finite canonical target has the original analytic
phase derivative and only a finite truncation of the regular coefficient. -/
theorem eval_trunc_canonical_derivative (h n : ℕ) (hh : 0 < h) (hn : h ≤ n)
    (N : NormalData ι) (hp : poleOrder (coefficient N) ≤ h)
    {z : ℂ} (hz : z ≠ 0) :
    z^(-(h : ℤ)) • WasowMatrixPolynomial.eval (PowerSeries.trunc n
      (clearAt h (coefficient N))) z =
      Matrix.diagonal (fun i => deriv (fun t : ℂ => (N.phase i).eval t⁻¹) z) +
      z⁻¹ • WasowMatrixPolynomial.eval (PowerSeries.trunc (n-h+1) N.regular) z := by
  rw [eval_trunc_canonical h n hh hn N hp hz, phasePolynomial_eval h hh N hp hz]

#print axioms eval_pole_polynomial_entry
#print axioms phasePolynomial_eval
#print axioms eval_trunc_canonical_derivative

#print axioms evalOn_sum_single
#print axioms finite_laurent_eval_eq
#print axioms phaseDerivative_sum
#print axioms phase_hasDerivAt
#print axioms toLaurent_polynomial_entry
end WasowCanonicalPhaseEvaluation
