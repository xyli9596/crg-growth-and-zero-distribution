import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-!
# Compactness step of Levin's dense-direction criterion

These are topological convergence results. They do not assert that logarithmic
moduli of entire functions satisfy the required equicontinuity hypothesis.
The index filter is arbitrary, so it can be a radial filter with an exceptional
set removed. No countability of the dense set is required by this module.
-/

open Set Filter Topology

namespace LevinCompact

variable {ι X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {F : ι → X → Y} {l : Filter ι} {s : Set X}

/-- Equicontinuity and convergence at dense points make every evaluation Cauchy. -/
theorem cauchy_of_dense_convergence [l.NeBot]
    (hF : Equicontinuous F) (hs : Dense s)
    (hlim : ∀ y ∈ s, ∃ z, Tendsto (fun i => F i y) l (𝓝 z)) (x : X) :
    Cauchy (map (fun i => F i x) l) := by
  refine Metric.cauchy_iff.mpr ⟨inferInstance, ?_⟩
  intro ε hε
  have hsmall : 0 < ε / 4 := by positivity
  obtain ⟨y, hys, hy⟩ := hs.inter_nhds_nonempty
    ((Metric.equicontinuousAt_iff_right.mp (hF x)) (ε / 4) hsmall)
  obtain ⟨z, hz⟩ := hlim y hys
  have hnear : ∀ᶠ i in l, dist (F i y) z < ε / 4 :=
    (Metric.tendsto_nhds.mp hz) (ε / 4) hsmall
  refine ⟨(fun i => F i x) '' {i | dist (F i y) z < ε / 4}, image_mem_map hnear, ?_⟩
  rintro a ⟨i, hi, rfl⟩ b ⟨j, hj, rfl⟩
  change dist (F i y) z < ε / 4 at hi
  change dist (F j y) z < ε / 4 at hj
  calc
    dist (F i x) (F j x) ≤ dist (F i x) (F i y) + dist (F i y) (F j x) :=
      dist_triangle _ _ _
    _ ≤ dist (F i x) (F i y) + (dist (F i y) z + dist z (F j y) +
          dist (F j y) (F j x)) := by
      grw [dist_triangle (F i y) (F j y) (F j x), dist_triangle (F i y) z (F j y)]
    _ < ε := by rw [dist_comm z (F j y), dist_comm (F j y) (F j x)]; linarith [hy i, hy j]

/-- On a compact space, convergence on a dense set yields a continuous uniform
limit for an equicontinuous family with complete metric target. -/
theorem exists_continuous_uniform_limit [CompactSpace X] [CompleteSpace Y] [l.NeBot]
    (hF : Equicontinuous F) (hs : Dense s)
    (hlim : ∀ y ∈ s, ∃ z, Tendsto (fun i => F i y) l (𝓝 z)) :
    ∃ f : X → Y, Continuous f ∧ TendstoUniformly F f l := by
  have hex : ∀ x : X, ∃ z, Tendsto (fun i => F i x) l (𝓝 z) := fun x =>
    cauchy_map_iff_exists_tendsto.mp (cauchy_of_dense_convergence hF hs hlim x)
  choose f hf using hex
  have hpoint : Tendsto F l (𝓝 f) := tendsto_pi_nhds.mpr hf
  refine ⟨f, hpoint.continuous_of_equicontinuous hF, ?_⟩
  exact UniformFun.tendsto_iff_tendstoUniformly.mp
    ((hF.tendsto_uniformFun_iff_pi l f).mpr hpoint)

/-- A continuous candidate limit is determined on a dense set. -/
theorem uniform_limit_of_dense [CompactSpace X] (hF : Equicontinuous F)
    (hs : Dense s) {f : X → Y} (hf : Continuous f)
    (hlim : ∀ x ∈ s, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    TendstoUniformly F f l := by
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (hF.tendsto_uniformFun_iff_pi l f).mpr
  apply tendsto_pi_nhds.mpr
  intro x
  exact (hF x).tendsto_of_mem_closure hf.continuousAt.continuousWithinAt hlim (hs x)

section Asymptotic

variable {M : Type*} [PseudoMetricSpace M] {G : ι → M → Y} {D : Set M}

/-- Uniform angular equicontinuity only for sufficiently large indices, with the
threshold allowed to depend on the requested error. This is weaker than
requiring the whole family to be equicontinuous. -/
def AsymptoticUniformEquicontinuous (G : ι → M → Y) (l : Filter ι) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ᶠ i in l, ∀ x y, dist x y < δ → dist (G i x) (G i y) < ε

/-- Asymptotic equicontinuity suffices for Cauchy convergence at every point. -/
theorem cauchy_of_asymptotic_dense [l.NeBot]
    (hG : AsymptoticUniformEquicontinuous G l) (hD : Dense D)
    (hlim : ∀ y ∈ D, ∃ z, Tendsto (fun i => G i y) l (𝓝 z)) (x : M) :
    Cauchy (map (fun i => G i x) l) := by
  refine Metric.cauchy_iff.mpr ⟨inferInstance, ?_⟩
  intro ε hε
  have hsmall : 0 < ε / 4 := by positivity
  obtain ⟨δ, hδ, heq⟩ := hG (ε / 4) hsmall
  obtain ⟨y, hyD, hxy⟩ := hD.exists_dist_lt x hδ
  obtain ⟨z, hz⟩ := hlim y hyD
  have hnear : ∀ᶠ i in l, dist (G i y) z < ε / 4 :=
    (Metric.tendsto_nhds.mp hz) (ε / 4) hsmall
  have hgood : ∀ᶠ i in l, dist (G i x) (G i y) < ε / 4 ∧ dist (G i y) z < ε / 4 := by
    filter_upwards [heq, hnear] with i hi hiz
    exact ⟨hi x y (by simpa [dist_comm] using hxy), hiz⟩
  refine ⟨(fun i => G i x) '' {i | dist (G i x) (G i y) < ε / 4 ∧
      dist (G i y) z < ε / 4}, image_mem_map hgood, ?_⟩
  rintro a ⟨i, hi, rfl⟩ b ⟨j, hj, rfl⟩
  change dist (G i x) (G i y) < ε / 4 ∧ dist (G i y) z < ε / 4 at hi
  change dist (G j x) (G j y) < ε / 4 ∧ dist (G j y) z < ε / 4 at hj
  calc
    dist (G i x) (G j x) ≤ dist (G i x) (G i y) + dist (G i y) (G j x) :=
      dist_triangle _ _ _
    _ ≤ dist (G i x) (G i y) + (dist (G i y) z + dist z (G j y) +
          dist (G j y) (G j x)) := by
      grw [dist_triangle (G i y) (G j y) (G j x), dist_triangle (G i y) z (G j y)]
    _ < ε := by
      rw [dist_comm z (G j y), dist_comm (G j y) (G j x)]
      linarith [hi.1, hi.2, hj.1, hj.2]

/-- A pointwise limit inherits uniform continuity from asymptotic uniform
 equicontinuity; no continuity of the candidate limit is assumed. -/
theorem uniformContinuous_of_asymptotic [l.NeBot] {f : M → Y}
    (hG : AsymptoticUniformEquicontinuous G l)
    (hlim : ∀ x, Tendsto (fun i => G i x) l (𝓝 (f x))) : UniformContinuous f := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, heq⟩ := hG (ε / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  have hbound : dist (f x) (f y) ≤ ε / 2 :=
    le_of_tendsto ((hlim x).dist (hlim y))
      (heq.mono fun i hi => (hi x y hxy).le)
  linarith

/-- Finite compact covering upgrades pointwise convergence to uniform convergence
under an asymptotic uniform modulus. -/
theorem uniform_of_asymptotic_pointwise [CompactSpace M] [l.NeBot] {f : M → Y}
    (hG : AsymptoticUniformEquicontinuous G l)
    (hlim : ∀ x, Tendsto (fun i => G i x) l (𝓝 (f x))) : TendstoUniformly G f l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, heq⟩ := hG (ε / 3) (by positivity)
  have hlimitmod : ∀ x y, dist x y < δ → dist (f x) (f y) ≤ ε / 3 := by
    intro x y hxy
    exact le_of_tendsto ((hlim x).dist (hlim y))
      (heq.mono fun i hi => (hi x y hxy).le)
  obtain ⟨A, hA⟩ := CompactSpace.elim_nhds_subcover (fun x : M => Metric.ball x δ)
    (fun x => Metric.ball_mem_nhds x hδ)
  have hcenters : ∀ᶠ i in l, ∀ a ∈ A, dist (G i a) (f a) < ε / 3 := by
    rw [Filter.eventually_all_finset]
    intro a ha
    exact (Metric.tendsto_nhds.mp (hlim a)) (ε / 3) (by positivity)
  filter_upwards [heq, hcenters] with i hi hc
  intro x
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hA.symm.subset (Set.mem_univ x))
  change dist x a < δ at hxa
  have hfa := hlimitmod x a hxa
  have hGia := hi a x (by simpa [dist_comm] using hxa)
  have hca := hc a ha
  calc
    dist (f x) (G i x) ≤ dist (f x) (f a) + dist (f a) (G i x) := dist_triangle _ _ _
    _ ≤ dist (f x) (f a) + (dist (f a) (G i a) + dist (G i a) (G i x)) := by
      grw [dist_triangle (f a) (G i a) (G i x)]
    _ < ε := by rw [dist_comm (f a) (G i a)]; linarith

/-- Full topological conclusion needed after the analytic Levin estimate:
dense-point convergence plus asymptotic equicontinuity constructs a continuous
uniform limit. Completeness supplies the missing limits outside the dense set. -/
theorem exists_uniform_limit_of_asymptotic_dense [CompactSpace M] [CompleteSpace Y] [l.NeBot]
    (hG : AsymptoticUniformEquicontinuous G l) (hD : Dense D)
    (hlim : ∀ y ∈ D, ∃ z, Tendsto (fun i => G i y) l (𝓝 z)) :
    ∃ f : M → Y, UniformContinuous f ∧ TendstoUniformly G f l := by
  have hex : ∀ x : M, ∃ z, Tendsto (fun i => G i x) l (𝓝 z) := fun x =>
    cauchy_map_iff_exists_tendsto.mp (cauchy_of_asymptotic_dense hG hD hlim x)
  choose f hf using hex
  exact ⟨f, uniformContinuous_of_asymptotic hG hf, uniform_of_asymptotic_pointwise hG hf⟩

/-- Prescribed limits on the dense set are retained by the constructed limit. -/
theorem exists_uniform_extension_of_asymptotic_dense [CompactSpace M] [CompleteSpace Y] [l.NeBot]
    (hG : AsymptoticUniformEquicontinuous G l) (hD : Dense D) {g : M → Y}
    (hlim : ∀ y ∈ D, Tendsto (fun i => G i y) l (𝓝 (g y))) :
    ∃ f : M → Y, UniformContinuous f ∧ TendstoUniformly G f l ∧ EqOn f g D := by
  obtain ⟨f, hf, huf⟩ := exists_uniform_limit_of_asymptotic_dense hG hD
    (fun y hy => ⟨g y, hlim y hy⟩)
  exact ⟨f, hf, huf, fun y hy => tendsto_nhds_unique (huf.tendsto_at y) (hlim y hy)⟩

/-- A continuous prescribed candidate is the unique possible uniform limit. -/
theorem uniform_of_asymptotic_dense [CompactSpace M] [CompleteSpace Y] [l.NeBot]
    (hG : AsymptoticUniformEquicontinuous G l) (hD : Dense D) {g : M → Y}
    (hg : Continuous g)
    (hlim : ∀ y ∈ D, Tendsto (fun i => G i y) l (𝓝 (g y))) :
    TendstoUniformly G g l := by
  obtain ⟨f, hf, huf, hfg⟩ := exists_uniform_extension_of_asymptotic_dense hG hD hlim
  have : f = g := funext fun x => hfg.closure hf.continuous hg (hD x)
  simpa only [this] using huf

/-- Countably many dense test directions suffice; no limit is supplied at other
angles and continuity is obtained as part of the conclusion. -/
theorem exists_uniform_limit_of_asymptotic_dense_sequence
    [CompactSpace M] [CompleteSpace Y] [l.NeBot] {d : ℕ → M}
    (hG : AsymptoticUniformEquicontinuous G l) (hd : DenseRange d)
    (hlim : ∀ n, ∃ z, Tendsto (fun i => G i (d n)) l (𝓝 z)) :
    ∃ f : M → Y, UniformContinuous f ∧ TendstoUniformly G f l := by
  apply exists_uniform_limit_of_asymptotic_dense hG hd
  rintro y ⟨n, rfl⟩
  exact hlim n

end Asymptotic

#print axioms exists_uniform_extension_of_asymptotic_dense
#print axioms uniform_of_asymptotic_dense
#print axioms exists_uniform_limit_of_asymptotic_dense_sequence
#print axioms cauchy_of_asymptotic_dense
#print axioms uniformContinuous_of_asymptotic
#print axioms uniform_of_asymptotic_pointwise
#print axioms exists_uniform_limit_of_asymptotic_dense
#print axioms cauchy_of_dense_convergence
#print axioms exists_continuous_uniform_limit
#print axioms uniform_limit_of_dense

end LevinCompact
