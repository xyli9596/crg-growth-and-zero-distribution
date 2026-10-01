import LevinCompact
import LevinDensity

/-!
# Combining radial exceptional sets with the dense-direction compactness step

The conclusion here follows from an explicit asymptotic equicontinuity
hypothesis. The analytic theorem establishing that hypothesis for entire
functions is not assumed as an axiom and is not proved by this module.
-/

open MeasureTheory Set Filter Topology
open LevinDensity LevinCompact

namespace LevinAssembly

/-- Radii tending to infinity outside an exceptional set. -/
def outsideFilter (E : Set ℝ) : Filter ℝ := atTop ⊓ 𝓟 Eᶜ

/-- A zero-density set cannot contain an entire final ray. -/
theorem exists_ge_outside {E : Set ℝ} (hE : ZeroRadialDensity E) (A : ℝ) :
    ∃ r : ℝ, A ≤ r ∧ r ∉ E := by
  by_contra h
  push Not at h
  obtain ⟨R₀, hR₀, hbound⟩ := hE (1 / 2) (by norm_num)
  let B := max A 0
  let R := max R₀ (2 * B + 1)
  have hB : 0 ≤ B := le_max_right A 0
  have hBR : 2 * B + 1 ≤ R := le_max_right _ _
  have hRpos : 0 < R := by linarith
  have hsub : Icc B R ⊆ E ∩ Icc 0 R := by
    intro r hr
    exact ⟨h r ((le_max_left A 0).trans hr.1), hB.trans hr.1, hr.2⟩
  have hmeasure := (measure_mono hsub).trans (hbound R (le_max_left _ _))
  rw [Real.volume_Icc] at hmeasure
  have hreal := (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ (1 / 2 : ℝ) * R by positivity)).mp hmeasure
  linarith

/-- In particular, restricting to the complement of a zero-density set never
makes convergence vacuous. -/
theorem outsideFilter_neBot {E : Set ℝ} (hE : ZeroRadialDensity E) :
    (outsideFilter E).NeBot := by
  apply Filter.inf_principal_neBot_iff.mpr
  intro U hU
  obtain ⟨A, hA⟩ := eventually_atTop.mp hU
  obtain ⟨r, hr, hrE⟩ := exists_ge_outside hE A
  exact ⟨r, hA r hr, hrE⟩

/-- Eventual inclusion of exceptional sets reverses the corresponding outside
filters, and therefore transports convergence hypotheses. -/
theorem outsideFilter_le_of_eventually_contains {E F : Set ℝ}
    (h : ∃ A : ℝ, ∀ r, A ≤ r → r ∈ E → r ∈ F) :
    outsideFilter F ≤ outsideFilter E := by
  obtain ⟨A, hA⟩ := h
  apply le_inf inf_le_left
  apply Filter.le_principal_iff.mpr
  have htail : ∀ᶠ r in outsideFilter F, A ≤ r :=
    (eventually_ge_atTop A).filter_mono inf_le_left
  have hout : ∀ᶠ r in outsideFilter F, r ∉ F :=
    Filter.mem_of_superset (Filter.mem_inf_of_right (Filter.mem_principal_self Fᶜ)) (fun _ => id)
  filter_upwards [htail, hout] with r hr hrF
  exact fun hrE => hrF (hA r hr hrE)

/-- Asymptotic equicontinuity passes to any finer index filter. -/
theorem asymptoticUniformEquicontinuous_mono {ι M Y : Type*}
    [PseudoMetricSpace M] [MetricSpace Y] {G : ι → M → Y} {l k : Filter ι}
    (hG : AsymptoticUniformEquicontinuous G l) (hkl : k ≤ l) :
    AsymptoticUniformEquicontinuous G k := by
  intro ε hε
  obtain ⟨δ, hδ, heq⟩ := hG ε hε
  exact ⟨δ, hδ, heq.filter_mono hkl⟩

/-- A single measurable zero-density set simultaneously supports the angular
modulus and all prescribed limits on countably many dense directions. The
resulting limit is uniformly continuous and convergence is uniform in angle. -/
theorem exists_common_exceptional_uniform_limit
    {M : Type*} [PseudoMetricSpace M] [CompactSpace M]
    (G : ℝ → M → ℝ) (d : ℕ → M) (hd : DenseRange d) (a : ℕ → ℝ)
    (Edir : ℕ → Set ℝ) (Eeq : Set ℝ)
    (hdir_meas : ∀ n, MeasurableSet (Edir n))
    (hdir_zero : ∀ n, ZeroRadialDensity (Edir n))
    (heq_meas : MeasurableSet Eeq) (heq_zero : ZeroRadialDensity Eeq)
    (hdir_lim : ∀ n, Tendsto (fun r => G r (d n)) (outsideFilter (Edir n)) (𝓝 (a n)))
    (heq : AsymptoticUniformEquicontinuous G (outsideFilter Eeq)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ ZeroRadialDensity E ∧
      ∃ h : M → ℝ, UniformContinuous h ∧
        TendstoUniformly G h (outsideFilter E) ∧ ∀ n, h (d n) = a n := by
  let family : ℕ → Set ℝ
    | 0 => Eeq
    | n + 1 => Edir n
  have hfamily_zero : ∀ n, ZeroRadialDensity (family n) := by
    intro n
    cases n with
    | zero => exact heq_zero
    | succ n => exact hdir_zero n
  have hfamily_meas : ∀ n, MeasurableSet (family n) := by
    intro n
    cases n with
    | zero => exact heq_meas
    | succ n => exact hdir_meas n
  obtain ⟨E, hEm, hEz, hcontains⟩ :=
    exists_measurable_zeroRadialDensity_eventually_contains family hfamily_zero hfamily_meas
  have hfilters (n : ℕ) : outsideFilter E ≤ outsideFilter (family n) := by
    obtain ⟨A, _, hA⟩ := hcontains n
    exact outsideFilter_le_of_eventually_contains ⟨A, hA⟩
  let : (outsideFilter E).NeBot := outsideFilter_neBot hEz
  have heq' : AsymptoticUniformEquicontinuous G (outsideFilter E) :=
    asymptoticUniformEquicontinuous_mono heq (hfilters 0)
  have hlim' (n : ℕ) : Tendsto (fun r => G r (d n)) (outsideFilter E) (𝓝 (a n)) :=
    (hdir_lim n).mono_left (hfilters (n + 1))
  obtain ⟨h, hh, hconv⟩ := exists_uniform_limit_of_asymptotic_dense_sequence heq' hd
    (fun n => ⟨a n, hlim' n⟩)
  refine ⟨E, hEm, hEz, h, hh, hconv, ?_⟩
  intro n
  exact tendsto_nhds_unique (hconv.tendsto_at (d n)) (hlim' n)

/-- Existential-input version: the separate raywise exceptional sets need not
be chosen in advance. Only the final common set appears in the conclusion. -/
theorem exists_uniform_limit_from_separate_exceptional_sets
    {M : Type*} [PseudoMetricSpace M] [CompactSpace M]
    (G : ℝ → M → ℝ) (d : ℕ → M) (hd : DenseRange d) (a : ℕ → ℝ)
    (hdir : ∀ n, ∃ E : Set ℝ, MeasurableSet E ∧ ZeroRadialDensity E ∧
      Tendsto (fun r => G r (d n)) (outsideFilter E) (𝓝 (a n)))
    (heq : ∃ E : Set ℝ, MeasurableSet E ∧ ZeroRadialDensity E ∧
      AsymptoticUniformEquicontinuous G (outsideFilter E)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ ZeroRadialDensity E ∧
      ∃ h : M → ℝ, UniformContinuous h ∧
        TendstoUniformly G h (outsideFilter E) ∧ ∀ n, h (d n) = a n := by
  choose Edir hdm hdz hlim using hdir
  obtain ⟨Eeq, hem, hez, heq⟩ := heq
  exact exists_common_exceptional_uniform_limit G d hd a Edir Eeq hdm hdz hem hez hlim heq

#print axioms exists_common_exceptional_uniform_limit
#print axioms exists_uniform_limit_from_separate_exceptional_sets
#print axioms exists_ge_outside
#print axioms outsideFilter_neBot
#print axioms outsideFilter_le_of_eventually_contains
#print axioms asymptoticUniformEquicontinuous_mono

end LevinAssembly
