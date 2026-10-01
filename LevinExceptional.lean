import LevinDyadic
import LevinSmallDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Exceptional radii from annular integral majorants

The hypotheses concern actual nonnegative measurable functions and Lebesgue
integrals on dyadic shells. Markov's inequality, countable subadditivity, and
dyadic summation construct the exceptional set. A single exceptional set for
each density budget supports all requested angular precisions.
-/

noncomputable section
open MeasureTheory Set Filter Topology Metric
open LevinDensity LevinCompact LevinAssembly LevinSmallDensity

namespace LevinExceptional

/-- Uniform-in-scale integral control of an angular modulus, outside `Z`.
The coefficient `cost δ` may already include a fixed analytic constant. -/
def AnnularMajorants {M : Type*} [PseudoMetricSpace M]
    (G : ℝ → M → ℝ) (Z : Set ℝ) (cost : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ P : ℝ → ℝ,
    Measurable P ∧ IntervalIntegrable P volume ((2 : ℝ) ^ n) (2 * 2 ^ n) ∧
    (∀ r : ℝ, 0 ≤ P r) ∧
    (∫ r in ((2 : ℝ) ^ n)..(2 * 2 ^ n), P r) ≤ (2 : ℝ) ^ n * cost δ ∧
    ∀ r ∈ Icc ((2 : ℝ) ^ n) (2 * 2 ^ n), r ∉ Z →
      ∀ v w : M, dist v w ≤ δ → dist (G r v) (G r w) ≤ P r

/-- Markov's inequality on one actual radial shell, expressed in outer measure. -/
theorem shell_markov (P : ℝ → ℝ) {R ε β : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hPm : Measurable P) (hPi : IntervalIntegrable P volume R (2 * R))
    (hPnonneg : ∀ r, 0 ≤ P r)
    (hbound : (∫ r in R..(2 * R), P r) ≤ ε * (β * R)) :
    volume (Ico R (2 * R) ∩ {r : ℝ | ε ≤ P r}) ≤ ENNReal.ofReal (β * R) := by
  let μ := volume.restrict (Icc R (2 * R))
  have hi : Integrable P μ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 hPi
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hPnonneg : 0 ≤ᵐ[μ] P) hi ε
  have hint : (∫ r, P r ∂μ) = ∫ r in R..(2 * R), P r := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  rw [hint] at hm
  have hreal : μ.real {r : ℝ | ε ≤ P r} ≤ β * R := by
    exact (mul_le_mul_iff_right₀ hε).1 (hm.trans hbound)
  have hmeas : MeasurableSet {r : ℝ | ε ≤ P r} := measurableSet_le measurable_const hPm
  have hfinite : μ {r : ℝ | ε ≤ P r} ≠ ⊤ := by
    change volume.restrict (Icc R (2 * R)) {r : ℝ | ε ≤ P r} ≠ ⊤
    rw [Measure.restrict_apply hmeas]
    exact (measure_lt_top_of_subset inter_subset_right (by simp [Real.volume_Icc])).ne
  calc
    volume (Ico R (2 * R) ∩ {r : ℝ | ε ≤ P r}) ≤
        μ {r : ℝ | ε ≤ P r} := by
      rw [Measure.restrict_apply hmeas]
      apply measure_mono
      intro r hr
      exact ⟨hr.2, hr.1.1, hr.1.2.le⟩
    _ = ENNReal.ofReal (μ.real {r : ℝ | ε ≤ P r}) :=
      (ENNReal.ofReal_toReal hfinite).symm
    _ ≤ ENNReal.ofReal (β * R) := ENNReal.ofReal_le_ofReal hreal

/-- The limit of the uniform cost supplies one angular scale that works on all
radial shells at once. -/
theorem exists_small_scale {cost : ℝ → ℝ}
    (hc : Tendsto cost (𝓝[>] (0 : ℝ)) (𝓝 0)) {t : ℝ} (ht : 0 < t) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ cost δ ≤ t := by
  have hc' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), cost δ < t := (tendsto_order.1 hc).2 t ht
  have hp : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, hδ, hδ1, hct⟩ := (hp.and (h1.and hc')).exists
  exact ⟨δ, hδ, hδ1.le, hct.le⟩

/-- Half-open dyadic shells have unique indices. -/
theorem dyadic_shell_index_unique {m n : ℕ} {r : ℝ}
    (hm : r ∈ Ico ((2 : ℝ) ^ m) (2 * 2 ^ m))
    (hn : r ∈ Ico ((2 : ℝ) ^ n) (2 * 2 ^ n)) : m = n := by
  apply Nat.le_antisymm
  · by_contra h
    have hp : (2 : ℝ) ^ (n + 1) ≤ 2 ^ m :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_succ] at hp
    nlinarith [hm.1, hn.2]
  · by_contra h
    have hp : (2 : ℝ) ^ (m + 1) ≤ 2 ^ n :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_succ] at hp
    nlinarith [hn.1, hm.2]

/-- On a closed dyadic shell, a union of shell-supported sets contributes only
its own shell, apart from one endpoint of zero Lebesgue measure. -/
theorem volume_dyadic_union_shell_le (B : ℕ → Set ℝ)
    (hB : ∀ n, B n ⊆ Ico ((2 : ℝ) ^ n) (2 * 2 ^ n)) (n : ℕ) :
    volume ((⋃ m, B m) ∩ Icc ((2 : ℝ) ^ n) (2 * 2 ^ n)) ≤ volume (B n) := by
  have hsub : (⋃ m, B m) ∩ Icc ((2 : ℝ) ^ n) (2 * 2 ^ n) ⊆
      B n ∪ {2 * (2 : ℝ) ^ n} := by
    intro r hr
    by_cases heq : r = 2 * (2 : ℝ) ^ n
    · exact Or.inr (mem_singleton_iff.2 heq)
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hr.1
      have hindex : m = n := dyadic_shell_index_unique (hB m hm)
        ⟨hr.2.1, lt_of_le_of_ne hr.2.2 heq⟩
      exact Or.inl (hindex ▸ hm)
  calc
    volume ((⋃ m, B m) ∩ Icc ((2 : ℝ) ^ n) (2 * 2 ^ n)) ≤
        volume (B n ∪ {2 * (2 : ℝ) ^ n}) := measure_mono hsub
    _ ≤ volume (B n) + volume {2 * (2 : ℝ) ^ n} := measure_union_le _ _
    _ = volume (B n) := by simp

/-- Allocate a summable bad-set budget to all angular precisions on every
shell. The chosen angular scales are independent of the shell index. -/
theorem exists_shell_badsets {M : Type*} [PseudoMetricSpace M]
    (G : ℝ → M → ℝ) (Z : Set ℝ) (cost : ℝ → ℝ)
    (hc : Tendsto cost (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hcontrol : AnnularMajorants G Z cost) {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℕ → ℝ, (∀ k, 0 < δ k) ∧ ∃ B : ℕ → Set ℝ,
      (∀ n, MeasurableSet (B n)) ∧
      (∀ n, B n ⊆ Ico ((2 : ℝ) ^ n) (2 * 2 ^ n)) ∧
      (∀ n, volume (B n) ≤ ENNReal.ofReal (b * 2 ^ n)) ∧
      ∀ n k r, r ∈ Ico ((2 : ℝ) ^ n) (2 * 2 ^ n) → r ∉ B n → r ∉ Z →
        ∀ v w : M, dist v w ≤ δ k → dist (G r v) (G r w) < (1 / 2 : ℝ) ^ k := by
  classical
  let e : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  have he (k : ℕ) : 0 < e k := by dsimp [e]; positivity
  let β : ℕ → ℝ := fun k => (b / 2) * e k
  have hβ (k : ℕ) : 0 < β k := mul_pos (by positivity) (he k)
  have hδexists (k : ℕ) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ cost δ ≤ e k * β k :=
    exists_small_scale hc (mul_pos (he k) (hβ k))
  choose δ hδpos hδone hδcost using hδexists
  have hPexists := fun n k => hcontrol n (δ k) (hδpos k) (hδone k)
  choose P hPm hPi hPnonneg hPbound hPosc using hPexists
  let bad : ℕ → ℕ → Set ℝ := fun n k =>
    Ico ((2 : ℝ) ^ n) (2 * 2 ^ n) ∩ {r : ℝ | e k ≤ P n k r}
  let B : ℕ → Set ℝ := fun n => ⋃ k, bad n k
  have hbad (n k : ℕ) : volume (bad n k) ≤ ENNReal.ofReal (β k * (2 : ℝ) ^ n) := by
    apply shell_markov (P n k) (by positivity) (he k)
      (hPm n k) (hPi n k) (hPnonneg n k)
    calc
      (∫ r in ((2 : ℝ) ^ n)..(2 * 2 ^ n), P n k r) ≤
          (2 : ℝ) ^ n * cost (δ k) := hPbound n k
      _ ≤ (2 : ℝ) ^ n * (e k * β k) :=
        mul_le_mul_of_nonneg_left (hδcost k) (by positivity)
      _ = e k * (β k * (2 : ℝ) ^ n) := by ring
  refine ⟨δ, hδpos, B, ?_, ?_, ?_, ?_⟩
  · intro n
    exact MeasurableSet.iUnion (fun k => measurableSet_Ico.inter
      (measurableSet_le measurable_const (hPm n k)))
  · intro n r hr
    obtain ⟨k, hk⟩ := mem_iUnion.1 hr
    exact hk.1
  · intro n
    have hsum : Summable (fun k => β k * (2 : ℝ) ^ n) :=
      (summable_geometric_two.mul_left (b / 2)).mul_right ((2 : ℝ) ^ n)
    calc
      volume (B n) ≤ ∑' k, volume (bad n k) := measure_iUnion_le _
      _ ≤ ∑' k, ENNReal.ofReal (β k * (2 : ℝ) ^ n) :=
        ENNReal.tsum_le_tsum (fun k => hbad n k)
      _ = ENNReal.ofReal (∑' k, β k * (2 : ℝ) ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hβ k).le (by positivity)) hsum).symm
      _ = ENNReal.ofReal (b * (2 : ℝ) ^ n) := by
        simp only [β, e, tsum_mul_right, tsum_mul_left, tsum_geometric_two]
        congr 1
        ring
  · intro n k r hr hrB hrZ v w hvw
    have hp : P n k r < e k := by
      by_contra h
      apply hrB
      exact mem_iUnion.2 ⟨k, hr, le_of_not_gt h⟩
    exact (hPosc n k r ⟨hr.1, hr.2.le⟩ hrZ v w hvw).trans_lt hp

/-- Actual annular integral majorants produce one measurable exceptional set
for each positive density budget. Outside that set the family is asymptotically
uniformly equicontinuous at every angular precision. -/
theorem exists_small_density_equicontinuity {M : Type*} [PseudoMetricSpace M]
    (G : ℝ → M → ℝ) (Z : Set ℝ) (hZm : MeasurableSet Z)
    (hZz : ZeroRadialDensity Z) (cost : ℝ → ℝ)
    (hc : Tendsto cost (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hcontrol : AnnularMajorants G Z cost) :
    ∀ η : ℝ, 0 < η → ∃ E : Set ℝ, MeasurableSet E ∧
      EventuallyDensityLE E η ∧ AsymptoticUniformEquicontinuous G (outsideFilter E) := by
  intro η hη
  obtain ⟨δ, hδpos, B, hBm, hBsub, hBmeasure, hgood⟩ :=
    exists_shell_badsets G Z cost hc hcontrol (show 0 < η / 6 by positivity)
  let Ebad : Set ℝ := ⋃ n, B n
  have hEbadm : MeasurableSet Ebad := MeasurableSet.iUnion hBm
  have hEbadbound : EventuallyDensityLE Ebad (3 * (η / 6)) := by
    apply LevinDyadic.eventually_volume_le_of_dyadic_bounds Ebad (η / 6)
      (by positivity) 0
    intro n _
    have hpow : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    rw [hpow]
    exact (volume_dyadic_union_shell_le B hBsub n).trans (hBmeasure n)
  have hEbound : EventuallyDensityLE (Ebad ∪ Z) η := by
    have h := density_bound_union_zero hEbadbound hZz (show 0 < 3 * (η / 6) by positivity)
    have heq : 2 * (3 * (η / 6)) = η := by ring
    rwa [heq] at h
  refine ⟨Ebad ∪ Z, hEbadm.union hZm, hEbound, ?_⟩
  intro ε hε
  have herror : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨k, hk⟩ := ((tendsto_order.1 herror).2 ε hε).exists
  refine ⟨δ k, hδpos k, ?_⟩
  apply eventually_inf_principal.mpr
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr hrE v w hvw
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near hr (show (1 : ℝ) < 2 by norm_num)
  have hshell : r ∈ Ico ((2 : ℝ) ^ n) (2 * 2 ^ n) := by
    refine ⟨hn₁, ?_⟩
    simpa only [pow_succ, mul_comm] using hn₂
  have hrB : r ∉ B n := fun h => hrE (Or.inl (mem_iUnion.2 ⟨n, h⟩))
  have hrZ : r ∉ Z := fun h => hrE (Or.inr h)
  exact (hgood n k r hshell hrB hrZ v w hvw.le).trans hk

end LevinExceptional

#print axioms LevinExceptional.shell_markov
#print axioms LevinExceptional.exists_small_scale

#print axioms LevinExceptional.dyadic_shell_index_unique
#print axioms LevinExceptional.volume_dyadic_union_shell_le

#print axioms LevinExceptional.exists_shell_badsets

#print axioms LevinExceptional.exists_small_density_equicontinuity
