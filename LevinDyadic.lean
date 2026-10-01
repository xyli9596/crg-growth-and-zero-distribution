import LevinDensity

/-!
# Assembling dyadic radial exceptional sets

Actual Lebesgue outer-measure bounds on dyadic annuli imply bounds at every
large radius. No measurability hypothesis or analytic estimate is hidden here.
-/

open MeasureTheory Set Filter Topology

namespace LevinDyadic

/-- The finite geometric sum used in the radial-measure estimate. -/
theorem sum_two_pow (k : ℕ) :
    ∑ n ∈ Finset.range k, (2 : ℝ) ^ n = 2 ^ k - 1 := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, div_one] using
    geom_sum_eq (show (2 : ℝ) ≠ 1 by norm_num) k

/-- Dyadic annular estimates after scale `N` give an estimate at every `R ≥ 1`.
The additive term is the uncontrolled finite initial segment. -/
theorem volume_le_of_dyadic_bounds (E : Set ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (N : ℕ)
    (hE : ∀ n : ℕ, N ≤ n →
      volume (E ∩ Icc ((2 : ℝ) ^ n) (2 ^ (n + 1))) ≤
        ENNReal.ofReal (eta * 2 ^ n))
    {R : ℝ} (hR : 1 ≤ R) :
    volume (E ∩ Icc 0 R) ≤ ENNReal.ofReal (2 ^ N + 2 * eta * R) := by
  classical
  obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near hR (show (1 : ℝ) < 2 by norm_num)
  let A : ℕ → Set ℝ := fun n =>
    if N ≤ n then E ∩ Icc ((2 : ℝ) ^ n) (2 ^ (n + 1)) else ∅
  have hcover : E ∩ Icc 0 R ⊆
      Icc 0 ((2 : ℝ) ^ N) ∪ ⋃ n ∈ Finset.range (k + 1), A n := by
    intro r hr
    by_cases hsmall : r ≤ (2 : ℝ) ^ N
    · exact Or.inl ⟨hr.2.1, hsmall⟩
    · have hlarge : (2 : ℝ) ^ N < r := lt_of_not_ge hsmall
      have hone : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
      obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near (hone.trans hlarge.le)
        (show (1 : ℝ) < 2 by norm_num)
      have hnN : N ≤ n := by
        by_contra h
        have hle : n + 1 ≤ N := by omega
        have hp : (2 : ℝ) ^ (n + 1) ≤ 2 ^ N :=
          pow_le_pow_right₀ (by norm_num) hle
        linarith
      have hnk : n < k + 1 := by
        by_contra h
        have hle : k + 1 ≤ n := by omega
        have hp : (2 : ℝ) ^ (k + 1) ≤ 2 ^ n :=
          pow_le_pow_right₀ (by norm_num) hle
        linarith [hr.2.2]
      right
      apply mem_iUnion₂.2
      refine ⟨n, Finset.mem_range.2 hnk, ?_⟩
      simp only [A, if_pos hnN]
      exact ⟨hr.1, hn₁, hn₂.le⟩
  have hA (n : ℕ) : volume (A n) ≤ ENNReal.ofReal (eta * 2 ^ n) := by
    by_cases hn : N ≤ n
    · simpa only [A, if_pos hn] using hE n hn
    · simp only [A, if_neg hn, measure_empty]
      exact bot_le
  have hsum_nonneg : 0 ≤ ∑ n ∈ Finset.range (k + 1), eta * (2 : ℝ) ^ n := by
    exact Finset.sum_nonneg (fun n _ => mul_nonneg heta (by positivity))
  calc
    volume (E ∩ Icc 0 R) ≤ volume (Icc 0 ((2 : ℝ) ^ N) ∪
        ⋃ n ∈ Finset.range (k + 1), A n) := measure_mono hcover
    _ ≤ volume (Icc 0 ((2 : ℝ) ^ N)) +
        volume (⋃ n ∈ Finset.range (k + 1), A n) := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ N) +
        ∑ n ∈ Finset.range (k + 1), ENNReal.ofReal (eta * (2 : ℝ) ^ n) := by
      apply add_le_add
      · simp only [Real.volume_Icc, sub_zero, le_refl]
      · exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum (fun n _ => hA n))
    _ = ENNReal.ofReal ((2 : ℝ) ^ N +
        ∑ n ∈ Finset.range (k + 1), eta * (2 : ℝ) ^ n) := by
      rw [ENNReal.ofReal_add (by positivity) hsum_nonneg,
        ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg heta (by positivity))]
    _ = ENNReal.ofReal ((2 : ℝ) ^ N + eta * (2 ^ (k + 1) - 1)) := by
      rw [← Finset.mul_sum, sum_two_pow]
    _ ≤ ENNReal.ofReal (2 ^ N + 2 * eta * R) := by
      apply ENNReal.ofReal_le_ofReal
      have hp : (2 : ℝ) ^ (k + 1) ≤ 2 * R := by
        rw [pow_succ]
        nlinarith
      nlinarith

/-- The finite initial segment can be absorbed into an arbitrarily large
radius. A factor of three suffices for the resulting density bound. -/
theorem eventually_volume_le_of_dyadic_bounds (E : Set ℝ) (eta : ℝ)
    (heta : 0 < eta) (N : ℕ)
    (hE : ∀ n : ℕ, N ≤ n →
      volume (E ∩ Icc ((2 : ℝ) ^ n) (2 ^ (n + 1))) ≤
        ENNReal.ofReal (eta * 2 ^ n)) :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      volume (E ∩ Icc 0 R) ≤ ENNReal.ofReal (3 * eta * R) := by
  refine ⟨max 1 ((2 : ℝ) ^ N / eta),
    (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left _ _), ?_⟩
  intro R hR
  have hRone : 1 ≤ R := (le_max_left _ _).trans hR
  apply (volume_le_of_dyadic_bounds E eta heta.le N hE hRone).trans
  apply ENNReal.ofReal_le_ofReal
  have hdiv := (le_max_right 1 ((2 : ℝ) ^ N / eta)).trans hR
  have := (div_le_iff₀ heta).1 hdiv
  nlinarith

/-- If the relative annular bound becomes arbitrarily small at sufficiently
late dyadic scales, then the whole exceptional set has zero radial density. -/
theorem zeroRadialDensity_of_dyadic_bounds (E : Set ℝ)
    (hE : ∀ eta : ℝ, 0 < eta → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      volume (E ∩ Icc ((2 : ℝ) ^ n) (2 ^ (n + 1))) ≤
        ENNReal.ofReal (eta * 2 ^ n)) : LevinDensity.ZeroRadialDensity E := by
  intro ε hε
  obtain ⟨N, hN⟩ := hE (ε / 3) (by positivity)
  obtain ⟨R₀, hR₀, hbound⟩ := eventually_volume_le_of_dyadic_bounds E (ε / 3)
    (by positivity) N hN
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  convert hbound R hR using 1
  congr 1
  ring

end LevinDyadic

#print axioms LevinDyadic.sum_two_pow
#print axioms LevinDyadic.volume_le_of_dyadic_bounds
#print axioms LevinDyadic.eventually_volume_le_of_dyadic_bounds
#print axioms LevinDyadic.zeroRadialDensity_of_dyadic_bounds
