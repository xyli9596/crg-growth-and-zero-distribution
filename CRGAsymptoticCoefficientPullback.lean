import CRGAsymptoticCoefficientCompleteExpansion
import WasowGlobalFormalRegular
import WasowRamifiedCoefficient

/-! Pullbacks and pole clearing preserve complete asymptotic expansions,
including divergent expansions on closed subsectors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology BigOperators Matrix.Norms.Operator
open Filter Asymptotics
namespace CRGAsymptoticCoefficientPullback
open CRGAsymptoticCoefficientCompleteExpansion WasowMatrixPolynomial
open WasowLaurentFiniteRealization WasowGlobalFormalRegular
variable {m : ℕ}

/-- Concrete sparse finite polynomial; this is available also over the
noncommutative matrix coefficient ring. -/
def expandedTruncation (p N : ℕ) (A : PowerSeries (Mat (m := m))) : Polynomial (Mat (m := m)) :=
  ∑ n ∈ Finset.range N, Polynomial.monomial (p*n) (PowerSeries.coeff n A)

theorem coeff_expandedTruncation (p N : ℕ) (hp : 0<p)
    (A : PowerSeries (Mat (m := m))) (k : ℕ) :
    (expandedTruncation p N A).coeff k =
      if p ∣ k ∧ k/p<N then PowerSeries.coeff (k/p) A else 0 := by
  classical
  simp only [expandedTruncation, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hd : p ∣ k
  · by_cases hn : k/p<N
    · rw [if_pos ⟨hd,hn⟩, Finset.sum_eq_single (k/p)]
      · rw [Nat.mul_div_cancel' hd, if_pos rfl]
      · intro n _hN hne
        rw [if_neg]
        intro he
        apply hne
        rw [← he, Nat.mul_div_cancel_left _ hp]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hn)).elim
    · rw [if_neg (by simp [hn])]
      apply Finset.sum_eq_zero
      intro n hN
      rw [if_neg]
      intro he
      have hdiv : k/p=n := by rw [← he, Nat.mul_div_cancel_left _ hp]
      exact hn (hdiv ▸ Finset.mem_range.mp hN)
  · rw [if_neg (by simp [hd])]
    apply Finset.sum_eq_zero
    intro n _hN
    rw [if_neg]
    intro he
    exact hd ⟨n,he.symm⟩

theorem eval_expandedTruncation (p N : ℕ) (A : PowerSeries (Mat (m := m))) (z : ℂ) :
    eval (expandedTruncation p N A) z = eval (PowerSeries.trunc N A) (z^p) := by
  change evaluation z (expandedTruncation p N A) = _
  unfold expandedTruncation
  rw [map_sum]
  change _ = Polynomial.eval₂ (RingHom.id _) (algebraMap ℂ (Mat (m := m)) (z^p))
    (PowerSeries.trunc N A)
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _hn
  change Polynomial.eval₂ (RingHom.id _) (algebraMap ℂ (Mat (m := m)) z)
      (Polynomial.monomial (p*n) (PowerSeries.coeff n A)) = _
  rw [Polynomial.eval₂_monomial]
  simp only [RingHom.id_apply, ← map_pow, ← pow_mul]

/-- Higher integer powers are bounded by lower powers near zero. -/
theorem isBigO_norm_pow_of_le {l : Filter ℂ} (hl : l ≤ 𝓝 (0 : ℂ))
    {N M : ℕ} (hNM : N≤M) :
    (fun z : ℂ => ‖z‖ ^ M) =O[l] (fun z : ℂ => ‖z‖ ^ N) := by
  apply IsBigO.of_bound 1
  have he : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), ‖z‖≤1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    exact (show ‖z‖<1 by simpa only [Metric.mem_ball, dist_zero_right] using hz).le
  filter_upwards [he.filter_mono hl] with z hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg z) _), one_mul] using
    pow_le_pow_of_le_one (norm_nonneg z) hz hNM

/-- Substitution by z^p preserves the exact fixed formal series, with only
zeros inserted at indices not divisible by p. -/
theorem completeExpansion_power_pullback
    {l l' : Filter ℂ} (hl : l ≤ 𝓝 (0 : ℂ))
    {c : ℂ → Mat (m := m)} {A : PowerSeries (Mat (m := m))}
    (hc : CompleteExpansion l' c A)
    (p : ℕ) (hp : 0<p) (ht : Tendsto (fun z : ℂ => z^p) l l') :
    CompleteExpansion l (fun z => c (z^p)) (expandSeries p A) := by
  intro N
  have happrox : (fun z : ℂ => c (z^p) - eval (expandedTruncation p N A) z) =O[l]
      (fun z : ℂ => ‖z‖^(p*N)) := by
    have h := (hc N).comp_tendsto ht
    change (fun z : ℂ => c (z^p) - eval (PowerSeries.trunc N A) (z^p)) =O[l]
      (fun z : ℂ => ‖z^p‖^N) at h
    simpa only [eval_expandedTruncation, norm_pow, ← pow_mul] using h
  have hfinite : eval (expandedTruncation p N A - PowerSeries.trunc N (expandSeries p A)) =O[l]
      (fun z : ℂ => ‖z‖^N) := by
    apply (isBigO_eval_of_X_pow_dvd _ N ?_).mono hl
    apply Polynomial.X_pow_dvd_iff.mpr
    intro k hk
    rw [Polynomial.coeff_sub, coeff_expandedTruncation p N hp A k,
      PowerSeries.coeff_trunc, if_pos hk]
    simp only [expandSeries, PowerSeries.coeff_mk]
    by_cases hd : p ∣ k
    · have hn : k/p<N := (Nat.div_le_self k p).trans_lt hk
      simp [hd,hn]
    · simp [hd]
  have hn : N ≤ p*N := Nat.le_mul_of_pos_left N hp
  have he := (happrox.trans (isBigO_norm_pow_of_le hl hn)).add hfinite
  exact he.congr_left (fun z => by rw [eval_sub]; abel)

/-- The same exact coefficient shift used in formal pole clearing. -/
def shiftedTruncation (k : ℂ) (e N : ℕ) (A : PowerSeries (Mat (m := m))) :
    Polynomial (Mat (m := m)) := k • (Polynomial.X^e * PowerSeries.trunc N A)

theorem eval_smul (k : ℂ) (P : Polynomial (Mat (m := m))) (z : ℂ) :
    eval (k • P) z = k • eval P z := by
  change evaluation z (k • P) = _
  rw [Algebra.smul_def, map_mul]
  simp [eval, evaluation, Polynomial.eval₂RingHom'_apply, Algebra.algebraMap_eq_smul_one]

theorem completeExpansion_monomial
    {l : Filter ℂ} (hl : l ≤ 𝓝 (0 : ℂ))
    {c : ℂ → Mat (m := m)} {A : PowerSeries (Mat (m := m))}
    (hc : CompleteExpansion l c A) (k : ℂ) (e : ℕ) :
    CompleteExpansion l (fun z => (k*z^e) • c z) (k • (PowerSeries.X^e*A)) := by
  intro N
  have hm : (fun z : ℂ => k*z^e) =O[l] (fun _ : ℂ => (1:ℝ)) :=
    isBigO_const_of_tendsto (((continuous_const.mul (continuous_pow e)).tendsto 0).mono_left hl)
      (by norm_num)
  have happrox : (fun z : ℂ => (k*z^e) • c z - eval (shiftedTruncation k e N A) z) =O[l]
      (fun z : ℂ => ‖z‖^N) := by
    have hh : (fun z : ℂ => (k*z^e) • (c z - eval (PowerSeries.trunc N A) z)) =O[l]
        (fun z : ℂ => ‖z‖^N) := by
      simpa only [one_smul] using hm.smul (hc N)
    exact hh.congr_left (fun z => by
      simp only [shiftedTruncation, eval_smul, eval_X_pow_mul, smul_smul, smul_sub])
  have hfinite : eval (shiftedTruncation k e N A - PowerSeries.trunc N (k • (PowerSeries.X^e*A))) =O[l]
      (fun z : ℂ => ‖z‖^N) := by
    apply (isBigO_eval_of_X_pow_dvd _ N ?_).mono hl
    apply Polynomial.X_pow_dvd_iff.mpr
    intro n hn
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hn]
    simp only [shiftedTruncation, Polynomial.coeff_smul, Polynomial.coeff_X_pow_mul',
      PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_mul']
    split_ifs with he
    · rw [PowerSeries.coeff_trunc, if_pos (by omega)]
      exact sub_self _
    · exact sub_self _
  exact (happrox.add hfinite).congr_left (fun z => by rw [eval_sub]; abel)

#print axioms coeff_expandedTruncation
#print axioms eval_expandedTruncation
#print axioms isBigO_norm_pow_of_le
#print axioms completeExpansion_power_pullback
#print axioms eval_smul
#print axioms completeExpansion_monomial
end CRGAsymptoticCoefficientPullback
