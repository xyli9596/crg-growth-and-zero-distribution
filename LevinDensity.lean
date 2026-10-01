import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Radial exceptional sets of zero relative Lebesgue measure

These statements concern actual Lebesgue outer measure on real radii. No
regular-growth or analytic compactness theorem is assumed or asserted.
-/

open MeasureTheory Set Filter Topology

namespace LevinDensity

/-- Zero relative Lebesgue outer measure on the positive real axis. -/
def ZeroRadialDensity (E : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
    volume (E ∩ Icc 0 R) ≤ ENNReal.ofReal (ε * R)

/-- The normalized, real-valued Lebesgue outer measure inside `[0,R]`. -/
noncomputable def radialDensity (E : Set ℝ) (R : ℝ) : ℝ :=
  (volume (E ∩ Icc 0 R)).toReal / R

theorem local_volume_ne_top (E : Set ℝ) (R : ℝ) :
    volume (E ∩ Icc 0 R) ≠ ⊤ := by
  exact (measure_lt_top_of_subset inter_subset_right (by simp [Real.volume_Icc])).ne

theorem radialDensity_nonneg (E : Set ℝ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ radialDensity E R := by
  exact div_nonneg ENNReal.toReal_nonneg hR

theorem radialDensity_mono {E F : Set ℝ} (h : E ⊆ F) {R : ℝ} (hR : 0 ≤ R) :
    radialDensity E R ≤ radialDensity F R := by
  exact div_le_div_of_nonneg_right
    (ENNReal.toReal_mono (local_volume_ne_top F R)
      (measure_mono (inter_subset_inter_left _ h))) hR

theorem radialDensity_le_iff (E : Set ℝ) {R ε : ℝ} (hR : 0 < R) (hε : 0 ≤ ε) :
    radialDensity E R ≤ ε ↔
      volume (E ∩ Icc 0 R) ≤ ENNReal.ofReal (ε * R) := by
  rw [radialDensity, div_le_iff₀ hR,
    ← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hε hR.le),
    ENNReal.ofReal_toReal (local_volume_ne_top E R)]

theorem zeroRadialDensity_iff_tendsto (E : Set ℝ) :
    ZeroRadialDensity E ↔ Tendsto (radialDensity E) atTop (𝓝 0) := by
  constructor
  · intro h
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      exact ha.trans_le (radialDensity_nonneg E hR)
    · intro ε hε
      obtain ⟨R₀, _, h₀⟩ := h (ε / 2) (by positivity)
      filter_upwards [eventually_ge_atTop (max R₀ 1)] with R hR
      have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) ((le_max_right R₀ 1).trans hR)
      have hb := (radialDensity_le_iff E hRpos (show 0 ≤ ε / 2 by positivity)).2
        (h₀ R ((le_max_left R₀ 1).trans hR))
      linarith
  · intro h ε hε
    obtain ⟨R₀, h₀⟩ := eventually_atTop.1 ((tendsto_order.1 h).2 ε hε)
    refine ⟨max R₀ 1, le_trans (by norm_num) (le_max_right _ _), ?_⟩
    intro R hR
    have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) ((le_max_right R₀ 1).trans hR)
    exact (radialDensity_le_iff E hRpos hε.le).1
      (h₀ R ((le_max_left R₀ 1).trans hR)).le

theorem ZeroRadialDensity.mono {E F : Set ℝ} (hF : ZeroRadialDensity F)
    (h : E ⊆ F) : ZeroRadialDensity E := by
  intro ε hε
  obtain ⟨R₀, hR₀, h₀⟩ := hF ε hε
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  exact (measure_mono (inter_subset_inter_left _ h)).trans (h₀ R hR)

/-- Countable subadditivity after normalization; all sets may be nonmeasurable. -/
theorem radialDensity_iUnion_le (E : ℕ → Set ℝ) {R : ℝ} (hR : 0 < R)
    (hs : Summable (fun n => radialDensity (E n) R)) :
    radialDensity (⋃ n, E n) R ≤ ∑' n, radialDensity (E n) R := by
  have hnonneg : ∀ n, 0 ≤ radialDensity (E n) R :=
    fun n => radialDensity_nonneg (E n) hR.le
  apply (radialDensity_le_iff _ hR (tsum_nonneg hnonneg)).2
  have heq (n : ℕ) : volume (E n ∩ Icc 0 R) =
      ENNReal.ofReal (radialDensity (E n) R * R) := by
    rw [radialDensity, div_mul_cancel₀ _ hR.ne',
      ENNReal.ofReal_toReal (local_volume_ne_top (E n) R)]
  calc
    volume ((⋃ n, E n) ∩ Icc 0 R) = volume (⋃ n, E n ∩ Icc 0 R) := by
      congr 1
      exact iUnion_inter _ _
    _ ≤ ∑' n, volume (E n ∩ Icc 0 R) := measure_iUnion_le _
    _ = ∑' n, ENNReal.ofReal (radialDensity (E n) R * R) := tsum_congr heq
    _ = ENNReal.ofReal ((∑' n, radialDensity (E n) R) * R) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (hnonneg n) hR.le) (hs.mul_right R), tsum_mul_right]

/-- A uniformly summable bound allows countably many zero-density sets to be united. -/
theorem zeroRadialDensity_iUnion_of_summable_bound (E : ℕ → Set ℝ)
    (hE : ∀ n, ZeroRadialDensity (E n)) (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ᶠ R : ℝ in atTop, ∀ n, radialDensity (E n) R ≤ b n) :
    ZeroRadialDensity (⋃ n, E n) := by
  have hnorm : ∀ᶠ R : ℝ in atTop, ∀ n, ‖radialDensity (E n) R‖ ≤ b n := by
    filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with R hbR hR n
    simpa only [Real.norm_of_nonneg (radialDensity_nonneg (E n) hR)] using hbR n
  have hlim : Tendsto (fun R => ∑' n, radialDensity (E n) R) atTop (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hb
      (fun n => (zeroRadialDensity_iff_tendsto (E n)).1 (hE n)) hnorm
  apply (zeroRadialDensity_iff_tendsto _).2
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact radialDensity_nonneg _ hR
  · filter_upwards [hnorm, eventually_ge_atTop (1 : ℝ)] with R hn hR
    exact radialDensity_iUnion_le E (by linarith) (hb.of_norm_bounded hn)

/-- Truncating each exceptional set sufficiently far out makes their union have
zero radial density. The proof uses the summable geometric weights `2⁻ⁿ`. -/
theorem exists_truncation_zeroRadialDensity (E : ℕ → Set ℝ)
    (hE : ∀ n, ZeroRadialDensity (E n)) :
    ∃ cutoff : ℕ → ℝ, (∀ n, 0 ≤ cutoff n) ∧
      ZeroRadialDensity (⋃ n, E n ∩ Ici (cutoff n)) := by
  have hex : ∀ n : ℕ, ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      volume (E n ∩ Icc 0 R) ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ n) * R) := by
    intro n
    exact hE n _ (by positivity)
  choose cutoff hcut_nonneg hcut using hex
  refine ⟨cutoff, hcut_nonneg, ?_⟩
  apply zeroRadialDensity_iUnion_of_summable_bound
    (fun n => E n ∩ Ici (cutoff n))
    (fun n => (hE n).mono inter_subset_left)
    (fun n => (1 / 2 : ℝ) ^ n) summable_geometric_two
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR n
  have hRpos : 0 < R := by linarith
  by_cases hc : cutoff n ≤ R
  · exact (radialDensity_mono inter_subset_left hRpos.le).trans
      ((radialDensity_le_iff _ hRpos (by positivity)).2 (hcut n R hc))
  · have hempty : (E n ∩ Ici (cutoff n)) ∩ Icc 0 R = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      rintro x ⟨⟨_, hxcut⟩, _, hxR⟩
      exact hc (hxcut.trans hxR)
    simp only [radialDensity, hempty, measure_empty, ENNReal.toReal_zero, zero_div]
    positivity

/-- One exceptional set of zero density eventually contains each set of a
countable family of zero-density exceptional sets. -/
theorem exists_zeroRadialDensity_eventually_contains (E : ℕ → Set ℝ)
    (hE : ∀ n, ZeroRadialDensity (E n)) :
    ∃ F : Set ℝ, ZeroRadialDensity F ∧
      ∀ n, ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ r : ℝ, R₀ ≤ r → r ∈ E n → r ∈ F := by
  obtain ⟨cutoff, hc, hF⟩ := exists_truncation_zeroRadialDensity E hE
  refine ⟨⋃ n, E n ∩ Ici (cutoff n), hF, ?_⟩
  intro n
  refine ⟨cutoff n, hc n, ?_⟩
  intro r hr hrE
  exact mem_iUnion.2 ⟨n, hrE, hr⟩

/-- The measurable version retains measurability of the common exceptional set. -/
theorem exists_measurable_zeroRadialDensity_eventually_contains (E : ℕ → Set ℝ)
    (hE : ∀ n, ZeroRadialDensity (E n)) (hm : ∀ n, MeasurableSet (E n)) :
    ∃ F : Set ℝ, MeasurableSet F ∧ ZeroRadialDensity F ∧
      ∀ n, ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ r : ℝ, R₀ ≤ r → r ∈ E n → r ∈ F := by
  obtain ⟨cutoff, hc, hF⟩ := exists_truncation_zeroRadialDensity E hE
  refine ⟨⋃ n, E n ∩ Ici (cutoff n), ?_, hF, ?_⟩
  · exact MeasurableSet.iUnion (fun n => (hm n).inter measurableSet_Ici)
  · intro n
    refine ⟨cutoff n, hc n, ?_⟩
    intro r hr hrE
    exact mem_iUnion.2 ⟨n, hrE, hr⟩

/-- Eventual properties outside countably many zero-density exceptional sets
can be transferred to a single zero-density exceptional set. The radius still
may depend on the property index. -/
theorem exists_common_exceptional_set (E : ℕ → Set ℝ) (P : ℕ → ℝ → Prop)
    (hE : ∀ n, ZeroRadialDensity (E n))
    (hP : ∀ n, ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r → r ∉ E n → P n r) :
    ∃ F : Set ℝ, ZeroRadialDensity F ∧
      ∀ n, ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r → r ∉ F → P n r := by
  obtain ⟨F, hF, hinc⟩ := exists_zeroRadialDensity_eventually_contains E hE
  refine ⟨F, hF, ?_⟩
  intro n
  obtain ⟨A, _, hA⟩ := hinc n
  obtain ⟨B, hB⟩ := hP n
  refine ⟨max A B, ?_⟩
  intro r hr hrF
  apply hB r ((le_max_right A B).trans hr)
  intro hrE
  exact hrF (hA r ((le_max_left A B).trans hr) hrE)

/-- Tail intersections have zero density when arbitrarily late exceptional
sets have arbitrarily small eventual relative-measure bounds. -/
theorem zeroRadialDensity_tail_iInter (E : ℕ → Set ℝ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        volume (E n ∩ Icc 0 R) ≤ ENNReal.ofReal (ε * R)) (N : ℕ) :
    ZeroRadialDensity (⋂ n ≥ N, E n) := by
  intro ε hε
  obtain ⟨n, hn, R₀, hR₀, hbound⟩ := hsmall ε hε N
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  apply le_trans (measure_mono (inter_subset_inter_left _ ?_)) (hbound R hR)
  intro r hr
  exact mem_iInter.1 (mem_iInter.1 hr n) hn

/-- An epsilon/eta diagonal principle for a sequence of increasingly strong
properties. This includes positive exceptional-density bounds tending to zero;
it does not require the input exceptional sets themselves to have density zero. -/
theorem exists_common_exceptional_set_of_small_density (E : ℕ → Set ℝ)
    (P : ℕ → ℝ → Prop)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        volume (E n ∩ Icc 0 R) ≤ ENNReal.ofReal (ε * R))
    (hP : ∀ n r, r ∉ E n → P n r)
    (hmono : ∀ n m, n ≤ m → ∀ r, P m r → P n r) :
    ∃ F : Set ℝ, ZeroRadialDensity F ∧
      ∀ n, ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r → r ∉ F → P n r := by
  classical
  apply exists_common_exceptional_set (fun n => ⋂ m ≥ n, E m) P
    (fun n => zeroRadialDensity_tail_iInter E hsmall n)
  intro n
  refine ⟨0, fun r _ hr => ?_⟩
  by_contra hnot
  apply hr
  simp only [mem_iInter]
  intro m hnm
  by_contra hrm
  exact hnot (hmono n m hnm r (hP m r hrm))

/-- A convenient version of the epsilon/eta principle with explicit bounds
`eta n` tending to zero. The bounds use actual Lebesgue outer measure. -/
theorem exists_common_exceptional_set_of_density_bounds (E : ℕ → Set ℝ)
    (P : ℕ → ℝ → Prop) (eta : ℕ → ℝ) (heta : Tendsto eta atTop (𝓝 0))
    (hE : ∀ n, ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      volume (E n ∩ Icc 0 R) ≤ ENNReal.ofReal (eta n * R))
    (hP : ∀ n r, r ∉ E n → P n r)
    (hmono : ∀ n m, n ≤ m → ∀ r, P m r → P n r) :
    ∃ F : Set ℝ, ZeroRadialDensity F ∧
      ∀ n, ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r → r ∉ F → P n r := by
  apply exists_common_exceptional_set_of_small_density E P ?_ hP hmono
  intro ε hε N
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((tendsto_order.1 heta).2 ε hε)
  obtain ⟨R₀, hR₀, hbound⟩ := hE (max N M)
  refine ⟨max N M, le_max_left _ _, R₀, hR₀, fun R hR => ?_⟩
  apply (hbound R hR).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (hM _ (le_max_right _ _)).le (hR₀.trans hR)

/-- A finite initial interval has zero radial density. -/
theorem zeroRadialDensity_Iic (A : ℝ) : ZeroRadialDensity (Iic A) := by
  intro ε hε
  refine ⟨max 0 (max A 0 / ε), le_max_left _ _, ?_⟩
  intro R hR
  have hsubset : Iic A ∩ Icc 0 R ⊆ Icc 0 (max A 0) := by
    intro r hr
    exact ⟨hr.2.1, hr.1.trans (le_max_left _ _)⟩
  calc
    volume (Iic A ∩ Icc 0 R) ≤ volume (Icc 0 (max A 0)) := measure_mono hsubset
    _ = ENNReal.ofReal (max A 0) := by rw [Real.volume_Icc, sub_zero]
    _ ≤ ENNReal.ofReal (ε * R) := by
      apply ENNReal.ofReal_le_ofReal
      have hdiv := (le_max_right 0 (max A 0 / ε)).trans hR
      have := (div_le_iff₀ hε).1 hdiv
      linarith

/-- Normalized finite subadditivity. -/
theorem radialDensity_union_le (E F : Set ℝ) {R : ℝ} (hR : 0 ≤ R) :
    radialDensity (E ∪ F) R ≤ radialDensity E R + radialDensity F R := by
  unfold radialDensity
  rw [union_inter_distrib_right, ← add_div]
  apply div_le_div_of_nonneg_right _ hR
  exact measureReal_union_le _ _

theorem ZeroRadialDensity.union {E F : Set ℝ}
    (hE : ZeroRadialDensity E) (hF : ZeroRadialDensity F) :
    ZeroRadialDensity (E ∪ F) := by
  apply (zeroRadialDensity_iff_tendsto _).2
  have hlim : Tendsto (fun R => radialDensity E R + radialDensity F R) atTop (𝓝 0) := by
    simpa only [add_zero] using ((zeroRadialDensity_iff_tendsto E).1 hE).add
      ((zeroRadialDensity_iff_tendsto F).1 hF)
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact radialDensity_nonneg _ hR
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact radialDensity_union_le E F hR

/-- The full epsilon/eta diagonal principle also allows each input property
to start at its own radius. Finite initial failures are absorbed into each
exceptional set before performing the tail-intersection construction. -/
theorem exists_common_exceptional_set_of_eventual_density_bounds (E : ℕ → Set ℝ)
    (P : ℕ → ℝ → Prop) (eta : ℕ → ℝ) (heta : Tendsto eta atTop (𝓝 0))
    (hE : ∀ n, ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      volume (E n ∩ Icc 0 R) ≤ ENNReal.ofReal (eta n * R))
    (hP : ∀ n, ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r → r ∉ E n → P n r)
    (hmono : ∀ n m, n ≤ m → ∀ r, P m r → P n r) :
    ∃ F : Set ℝ, ZeroRadialDensity F ∧
      ∀ n, ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r → r ∉ F → P n r := by
  choose cutoff hcut using hP
  apply exists_common_exceptional_set_of_small_density
    (fun n => E n ∪ Iic (cutoff n)) P ?_ ?_ hmono
  · intro ε hε N
    obtain ⟨M, hM⟩ := eventually_atTop.1
      ((tendsto_order.1 heta).2 (ε / 2) (by positivity))
    let n := max N M
    obtain ⟨A, hA, hEA⟩ := hE n
    obtain ⟨B, hB, hIB⟩ := zeroRadialDensity_Iic (cutoff n) (ε / 2) (by positivity)
    refine ⟨n, le_max_left _ _, max (max A B) 1, ?_, ?_⟩
    · exact (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_right _ _)
    · intro R hR
      have hRA : A ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hR)
      have hRB : B ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hR)
      have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hR)
      apply (radialDensity_le_iff _ hRpos hε.le).1
      have hEn : radialDensity (E n) R ≤ ε / 2 := by
        apply (radialDensity_le_iff _ hRpos (by positivity)).2
        exact (hEA R hRA).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (hM n (le_max_right _ _)).le hRpos.le))
      have hIn : radialDensity (Iic (cutoff n)) R ≤ ε / 2 :=
        (radialDensity_le_iff _ hRpos (by positivity)).2 (hIB R hRB)
      exact (radialDensity_union_le _ _ hRpos.le).trans (by linarith)
  · intro n r hr
    apply hcut n r
    · by_contra h
      exact hr (Or.inr (le_of_not_ge h))
    · exact fun hrE => hr (Or.inl hrE)

end LevinDensity

#print axioms LevinDensity.local_volume_ne_top
#print axioms LevinDensity.radialDensity_nonneg
#print axioms LevinDensity.radialDensity_mono
#print axioms LevinDensity.radialDensity_le_iff
#print axioms LevinDensity.zeroRadialDensity_iff_tendsto
#print axioms LevinDensity.ZeroRadialDensity.mono
#print axioms LevinDensity.radialDensity_iUnion_le
#print axioms LevinDensity.zeroRadialDensity_iUnion_of_summable_bound
#print axioms LevinDensity.exists_truncation_zeroRadialDensity
#print axioms LevinDensity.exists_zeroRadialDensity_eventually_contains
#print axioms LevinDensity.exists_measurable_zeroRadialDensity_eventually_contains
#print axioms LevinDensity.exists_common_exceptional_set
#print axioms LevinDensity.zeroRadialDensity_tail_iInter
#print axioms LevinDensity.exists_common_exceptional_set_of_small_density
#print axioms LevinDensity.exists_common_exceptional_set_of_density_bounds
#print axioms LevinDensity.zeroRadialDensity_Iic
#print axioms LevinDensity.radialDensity_union_le
#print axioms LevinDensity.ZeroRadialDensity.union
#print axioms LevinDensity.exists_common_exceptional_set_of_eventual_density_bounds
