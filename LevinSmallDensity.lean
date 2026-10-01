import LevinAssembly
import LevinMeasurableDensity

/-!
# The positive-density version of Levin's topological assembly

Unlike `LevinAssembly`, the angular equicontinuity exceptional sets in this
module may have small positive density. Their upper bounds tend to zero.
The analytic equicontinuity assertion is an explicit input; the conclusion
constructs a single zero-density exceptional set for uniform convergence.
-/

open MeasureTheory Set Filter Topology
open LevinDensity LevinCompact LevinAssembly

namespace LevinSmallDensity

/-- An eventual upper bound for actual relative Lebesgue measure. -/
def EventuallyDensityLE (E : Set ℝ) (η : ℝ) : Prop :=
  ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
    volume (E ∩ Icc 0 R) ≤ ENNReal.ofReal (η * R)

/-- Even an exceptional set of sufficiently small positive density has
arbitrarily large good radii. -/
theorem exists_ge_outside_of_density_bound {E : Set ℝ} {η : ℝ}
    (hE : EventuallyDensityLE E η) (hη : η ≤ 1 / 2) (A : ℝ) :
    ∃ r : ℝ, A ≤ r ∧ r ∉ E := by
  by_contra h
  push Not at h
  obtain ⟨R₀, hR₀, hbound⟩ := hE
  let B := max A 0
  let R := max R₀ (2 * B + 1)
  have hB : 0 ≤ B := le_max_right A 0
  have hBR : 2 * B + 1 ≤ R := le_max_right _ _
  have hRpos : 0 < R := by linarith
  have hsub : Icc B R ⊆ E ∩ Icc 0 R := by
    intro r hr
    exact ⟨h r ((le_max_left A 0).trans hr.1), hB.trans hr.1, hr.2⟩
  have hmeasure : volume (Icc B R) ≤ ENNReal.ofReal ((1 / 2 : ℝ) * R) :=
    (measure_mono hsub).trans ((hbound R (le_max_left _ _)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hη hRpos.le)))
  rw [Real.volume_Icc] at hmeasure
  have hreal := (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ (1 / 2 : ℝ) * R by positivity)).mp hmeasure
  linarith

/-- The corresponding outside filter is nontrivial. -/
theorem outsideFilter_neBot_of_density_bound {E : Set ℝ} {η : ℝ}
    (hE : EventuallyDensityLE E η) (hη : η ≤ 1 / 2) :
    (outsideFilter E).NeBot := by
  apply Filter.inf_principal_neBot_iff.mpr
  intro U hU
  obtain ⟨A, hA⟩ := eventually_atTop.mp hU
  obtain ⟨r, hr, hrE⟩ := exists_ge_outside_of_density_bound hE hη A
  exact ⟨r, hA r hr, hrE⟩

/-- Adding a zero-density set at most doubles any positive eventual bound. -/
theorem density_bound_union_zero {E D : Set ℝ} {η : ℝ}
    (hE : EventuallyDensityLE E η) (hD : ZeroRadialDensity D) (hη : 0 < η) :
    EventuallyDensityLE (E ∪ D) (2 * η) := by
  obtain ⟨A, hA, hEA⟩ := hE
  obtain ⟨B, hB, hDB⟩ := hD η hη
  refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
  intro R hR
  have hRA : A ≤ R := (le_max_left _ _).trans hR
  have hRB : B ≤ R := (le_max_right _ _).trans hR
  have hRnonneg : 0 ≤ R := hA.trans hRA
  rw [union_inter_distrib_right]
  calc
    volume (E ∩ Icc 0 R ∪ D ∩ Icc 0 R) ≤
        volume (E ∩ Icc 0 R) + volume (D ∩ Icc 0 R) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η * R) + ENNReal.ofReal (η * R) := add_le_add (hEA R hRA) (hDB R hRB)
    _ = ENNReal.ofReal ((2 * η) * R) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hη.le hRnonneg) (mul_nonneg hη.le hRnonneg)]
      congr 1
      ring

/-- The outside filter of a union is finer than either individual outside
filter; bounded initial tails are not needed for this special case. -/
theorem outsideFilter_union_le_left (E D : Set ℝ) :
    outsideFilter (E ∪ D) ≤ outsideFilter E :=
  outsideFilter_le_of_eventually_contains ⟨0, fun _ _ hr => Or.inl hr⟩

theorem outsideFilter_union_le_right (E D : Set ℝ) :
    outsideFilter (E ∪ D) ≤ outsideFilter D :=
  outsideFilter_le_of_eventually_contains ⟨0, fun _ _ hr => Or.inr hr⟩

/-- Limits obtained with different small positive-density equicontinuity sets
are identical, because their values agree on the given dense directions. -/
theorem exists_single_limit_all_density_bounds
    {M : Type*} [PseudoMetricSpace M] [CompactSpace M]
    (G : ℝ → M → ℝ) (d : ℕ → M) (hd : DenseRange d) (a : ℕ → ℝ)
    (hdir : ∀ n, ∃ E : Set ℝ, MeasurableSet E ∧ ZeroRadialDensity E ∧
      Tendsto (fun r => G r (d n)) (outsideFilter E) (𝓝 (a n)))
    (Eeq : ℕ → Set ℝ) (η : ℕ → ℝ)
    (hηpos : ∀ n, 0 < η n) (hηsmall : ∀ n, η n ≤ 1 / 4)
    (hbound : ∀ n, EventuallyDensityLE (Eeq n) (η n))
    (heq : ∀ n, AsymptoticUniformEquicontinuous G (outsideFilter (Eeq n))) :
    ∃ D : Set ℝ, MeasurableSet D ∧ ZeroRadialDensity D ∧
      ∃ h : M → ℝ, UniformContinuous h ∧ (∀ n, h (d n) = a n) ∧
        ∀ n, TendstoUniformly G h (outsideFilter (Eeq n ∪ D)) := by
  choose Edir hdm hdz hlim using hdir
  obtain ⟨D, hDm, hDz, hcontains⟩ :=
    exists_measurable_zeroRadialDensity_eventually_contains Edir hdz hdm
  have hdirD (n : ℕ) : Tendsto (fun r => G r (d n)) (outsideFilter D) (𝓝 (a n)) := by
    obtain ⟨A, _, hA⟩ := hcontains n
    exact (hlim n).mono_left (outsideFilter_le_of_eventually_contains ⟨A, hA⟩)
  have hex (k : ℕ) : ∃ h : M → ℝ, UniformContinuous h ∧
      TendstoUniformly G h (outsideFilter (Eeq k ∪ D)) ∧ ∀ n, h (d n) = a n := by
    have hbound' := density_bound_union_zero (hbound k) hDz (hηpos k)
    let : (outsideFilter (Eeq k ∪ D)).NeBot :=
      outsideFilter_neBot_of_density_bound hbound' (by linarith [hηsmall k])
    have heq' := asymptoticUniformEquicontinuous_mono (heq k)
      (outsideFilter_union_le_left (Eeq k) D)
    have hlim' (n : ℕ) := (hdirD n).mono_left (outsideFilter_union_le_right (Eeq k) D)
    obtain ⟨h, hh, hconv⟩ := exists_uniform_limit_of_asymptotic_dense_sequence heq' hd
      (fun n => ⟨a n, hlim' n⟩)
    exact ⟨h, hh, hconv, fun n => tendsto_nhds_unique (hconv.tendsto_at (d n)) (hlim' n)⟩
  choose H hHuc hHconv hHdense using hex
  refine ⟨D, hDm, hDz, H 0, hHuc 0, hHdense 0, ?_⟩
  intro k
  have hequal : H k = H 0 := by
    have hdense_eq : EqOn (H k) (H 0) (range d) := by
      rintro x ⟨n, rfl⟩
      rw [hHdense k n, hHdense 0 n]
    exact funext fun x => hdense_eq.closure (hHuc k).continuous (hHuc 0).continuous (hd x)
  simpa only [hequal] using hHconv k

/-- The actual epsilon/eta assembly. Each equicontinuity exceptional set may
have positive density bounded by `η n`; only these bounds tend to zero. A
single measurable zero-density exceptional set supports uniform convergence. -/
theorem exists_zero_density_uniform_limit
    {M : Type*} [PseudoMetricSpace M] [CompactSpace M]
    (G : ℝ → M → ℝ) (d : ℕ → M) (hd : DenseRange d) (a : ℕ → ℝ)
    (hdir : ∀ n, ∃ E : Set ℝ, MeasurableSet E ∧ ZeroRadialDensity E ∧
      Tendsto (fun r => G r (d n)) (outsideFilter E) (𝓝 (a n)))
    (Eeq : ℕ → Set ℝ) (η : ℕ → ℝ)
    (hEm : ∀ n, MeasurableSet (Eeq n))
    (hηpos : ∀ n, 0 < η n) (hηsmall : ∀ n, η n ≤ 1 / 4)
    (hηlim : Tendsto η atTop (𝓝 0))
    (hbound : ∀ n, EventuallyDensityLE (Eeq n) (η n))
    (heq : ∀ n, AsymptoticUniformEquicontinuous G (outsideFilter (Eeq n))) :
    ∃ E : Set ℝ, MeasurableSet E ∧ ZeroRadialDensity E ∧
      ∃ h : M → ℝ, UniformContinuous h ∧ TendstoUniformly G h (outsideFilter E) ∧
        ∀ n, h (d n) = a n := by
  obtain ⟨D, hDm, hDz, h, hh, hdense, hconv⟩ :=
    exists_single_limit_all_density_bounds G d hd a hdir Eeq η hηpos hηsmall hbound heq
  let P : ℕ → ℝ → Prop := fun n r => ∀ x, dist (h x) (G r x) < (1 / 2 : ℝ) ^ n
  have hηlim' : Tendsto (fun n => 2 * η n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hηlim
  have hbounds (n : ℕ) : EventuallyDensityLE (Eeq n ∪ D) (2 * η n) :=
    density_bound_union_zero (hbound n) hDz (hηpos n)
  have hP (n : ℕ) : ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r → r ∉ Eeq n ∪ D → P n r := by
    have hevent := (Metric.tendstoUniformly_iff.mp (hconv n)) ((1 / 2 : ℝ) ^ n) (by positivity)
    exact eventually_atTop.mp (Filter.eventually_inf_principal.mp hevent)
  have hmono : ∀ n m, n ≤ m → ∀ r, P m r → P n r := by
    intro n m hnm r hr x
    exact (hr x).trans_le (pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm)
  obtain ⟨E, hEmeas, hEzero, hEP⟩ :=
    LevinMeasurableDensity.exists_common_exceptional_set_of_eventual_density_bounds
      (fun n => Eeq n ∪ D) P (fun n => (hEm n).union hDm) (fun n => 2 * η n)
      hηlim' hbounds hP hmono
  refine ⟨E, hEmeas, hEzero, h, hh, ?_, hdense⟩
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have herror : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨n, hn⟩ := ((tendsto_order.mp herror).2 ε hε).exists
  obtain ⟨A, hA⟩ := hEP n
  apply Filter.eventually_inf_principal.mpr
  apply eventually_atTop.mpr
  refine ⟨A, fun r hr hrE x => ?_⟩
  exact (hA r hr hrE x).trans hn

/-- A direct interface matching the positive-density angular estimate: for
each positive density budget there is an exceptional set outside which the
family is asymptotically uniformly equicontinuous. Together with the separate
zero-density raywise limits, this yields one zero-density set and angularly
uniform convergence. -/
theorem exists_zero_density_uniform_limit_of_arbitrarily_small_density
    {M : Type*} [PseudoMetricSpace M] [CompactSpace M]
    (G : ℝ → M → ℝ) (d : ℕ → M) (hd : DenseRange d) (a : ℕ → ℝ)
    (hdir : ∀ n, ∃ E : Set ℝ, MeasurableSet E ∧ ZeroRadialDensity E ∧
      Tendsto (fun r => G r (d n)) (outsideFilter E) (𝓝 (a n)))
    (heq : ∀ η : ℝ, 0 < η → ∃ E : Set ℝ, MeasurableSet E ∧
      EventuallyDensityLE E η ∧ AsymptoticUniformEquicontinuous G (outsideFilter E)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ ZeroRadialDensity E ∧
      ∃ h : M → ℝ, UniformContinuous h ∧ TendstoUniformly G h (outsideFilter E) ∧
        ∀ n, h (d n) = a n := by
  let η : ℕ → ℝ := fun n => (1 / 4) * (1 / 2 : ℝ) ^ n
  have hηpos (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  have hηsmall (n : ℕ) : η n ≤ 1 / 4 := by
    have hh : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [η]
    linarith
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [η] using tendsto_const_nhds.mul hh
  choose E hEm hbound hEeq using fun n => heq (η n) (hηpos n)
  exact exists_zero_density_uniform_limit G d hd a hdir E η hEm hηpos hηsmall hηlim hbound hEeq

#print axioms exists_zero_density_uniform_limit_of_arbitrarily_small_density
#print axioms exists_zero_density_uniform_limit
#print axioms exists_single_limit_all_density_bounds
#print axioms exists_ge_outside_of_density_bound
#print axioms outsideFilter_neBot_of_density_bound
#print axioms density_bound_union_zero
#print axioms outsideFilter_union_le_left
#print axioms outsideFilter_union_le_right

end LevinSmallDensity
