import CRGZeroDistributionSector

/-! Fixed equation-dependent exceptional directions for harmonicity of the
actual homogeneous indicators. Principal argument charts add the negative
real ray to the finite collision directions. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory Real Complex InnerProductSpace Polynomial
open scoped Topology
namespace CRGZeroDistributionHarmonic
open LevinGrowth LevinIndicatorModulus CRGIndicatorFixedPhases CRGIndicatorAlternatives
open CRGIndicatorPartition CRGFinitePhaseEndgame CRGPhaseDirections CRGZeroDistributionProfile

/-- Local angular indicator equality constructs a genuinely harmonic
homogeneous profile near the corresponding nonzero complex point. -/
theorem harmonicAt_of_indicator_interval {h : Direction → ℝ} {c : ℂ} {ρ u v : ℝ}
    (hformula : ∀ θ ∈ Ioo u v, h (CRGOrderLevin.angleDirection θ) = leadingReal c ρ θ)
    {z : ℂ} (hz : z ∈ Complex.slitPlane) (hzarg : z.arg ∈ Ioo u v) :
    HarmonicAt (homogeneousIndicator ρ h) z := by
  have hza : AnalyticAt ℂ (fun w : ℂ => c * w^(ρ : ℂ)) z :=
    analyticAt_const.mul (analyticAt_id.cpow analyticAt_const hz)
  have hang : {w : ℂ | w.arg ∈ Ioo u v} ∈ 𝓝 z :=
    (Complex.continuousAt_arg hz).preimage_mem_nhds (isOpen_Ioo.mem_nhds hzarg)
  have heq : homogeneousIndicator ρ h =ᶠ[𝓝 z]
      (fun w : ℂ => (c * w^(ρ : ℂ)).re) := by
    filter_upwards [hang, Complex.isOpen_slitPlane.mem_nhds hz] with w hw hws
    exact homogeneousIndicator_eq_cpow (Complex.slitPlane_ne_zero hws) (hformula w.arg hw)
  exact (harmonicAt_congr_nhds heq).mpr hza.harmonicAt_re

/-- A finite collision set on a principal argument chart gives a finite set
of actual rays outside which every continuous selecting indicator is harmonic. -/
theorem finite_alternatives_harmonic_off_rays (C : Finset ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ R : Finset Direction, ∀ h : Direction → ℝ, Continuous h →
      (∀ θ : ℝ, ∃ c ∈ C, h (CRGOrderLevin.angleDirection θ) = leadingReal c ρ θ) →
      ∀ z : ℂ, z ≠ 0 → normalizedDirection z ∉ R →
        HarmonicAt (homogeneousIndicator ρ h) z := by
  classical
  let T := collisionDirections C ρ (-Real.pi) Real.pi
  have hT : T.Finite := collisionDirections_finite C hρ
  let s := insert (-Real.pi) (insert Real.pi hT.toFinset)
  let R := s.image CRGOrderLevin.angleDirection
  refine ⟨R, ?_⟩
  intro h hh halt z hz haway
  have hargnot : z.arg ∉ s := by
    intro harg
    exact haway (Finset.mem_image.mpr
      ⟨z.arg, harg, (normalizedDirection_eq_angleDirection hz).symm⟩)
  have hnotpi : z.arg ≠ Real.pi := by
    intro heq
    apply hargnot
    rw [heq]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hzslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff_arg.mpr ⟨hnotpi, hz⟩
  have harg : z.arg ∈ Ioo (-Real.pi) Real.pi :=
    ⟨Complex.neg_pi_lt_arg z, lt_of_le_of_ne (Complex.arg_le_pi z) hnotpi⟩
  have hnotT : z.arg ∉ T := by
    intro hmem
    exact hargnot (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (hT.mem_toFinset.mpr hmem)))
  have hnhds : Ioo (-Real.pi) Real.pi ∩ Tᶜ ∈ 𝓝 z.arg :=
    (isOpen_Ioo.inter hT.isClosed.isOpen_compl).mem_nhds ⟨harg, hnotT⟩
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let u := z.arg - d/2
  let v := z.arg + d/2
  have huv : u < v := by dsimp [u, v]; linarith
  have hinterval : Ioo u v ⊆ Ioo (-Real.pi) Real.pi ∩ Tᶜ := by
    intro θ hθ
    apply hball
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp [u, v] at hθ
    constructor <;> linarith [hθ.1, hθ.2]
  have hsub : Ioo u v ⊆ Icc (-Real.pi) Real.pi :=
    fun θ hθ => ⟨(hinterval hθ).1.1.le, (hinterval hθ).1.2.le⟩
  have havoid : Disjoint (Ioo u v) T :=
    Set.disjoint_left.mpr (fun θ hθ hθT => (hinterval hθ).2 hθT)
  obtain ⟨c, _hc, hformula⟩ := indicator_on_interval C hρ huv hsub havoid
    (fun θ => h (CRGOrderLevin.angleDirection θ))
    (hh.comp CRGOrderLevin.continuous_angleDirection) halt
  exact harmonicAt_of_indicator_interval hformula hzslit
    ⟨by dsimp [u]; linarith, by dsimp [v]; linarith⟩

/-- The finite ray set is fixed before choosing a solution. Away from it,
each solution's actual homogeneous unrestricted indicator is harmonic. -/
theorem exists_fixed_harmonic_rays {n : ℕ} (E : EquationData n) :
    ∃ R : Finset Direction, ∀ f : ℂ → ℂ, Differentiable ℂ f → CRGOrder.FiniteOrder f →
      (¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z) → E.Solves f →
      ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ : ℝ) ∧ FinitePositiveType f (σ : ℝ) ∧
        ∃ h : Direction → ℝ, DiskRegular f (σ : ℝ) h ∧ IsIndicator f (σ : ℝ) h ∧
          ∀ z : ℂ, z ≠ 0 → normalizedDirection z ∉ R →
            HarmonicAt (homogeneousIndicator (σ : ℝ) h) z := by
  classical
  obtain ⟨ι, inst, p, hp, P, hP0, hcompare⟩ := E.exists_fixed_phases
  letI := inst
  let d : ι → ℚ := fun i => ((P i).natDegree : ℚ)/(p i : ℚ)
  let C : ℚ → Finset ℂ := fun σ => Finset.univ.image
    (fun i => if (d i : ℝ) = (σ : ℝ) then (P i).leadingCoeff else 0)
  let I := {i : ι // 0 < d i}
  choose R hR using fun i : I =>
    finite_alternatives_harmonic_off_rays (C (d i.val)) (ρ := (d i.val : ℝ))
      (by exact_mod_cast i.property)
  let S := Finset.univ.biUnion R
  refine ⟨S, ?_⟩
  intro f hf hfinite htrans heq
  have hphase := hcompare f hf hfinite htrans heq
  have hdata := ae_rayData_of_phase_comparison p hp P hP0 hphase
  obtain ⟨i, hdi, horder, htype⟩ := order_mem_of_ae_rayData hf hfinite htrans d
    (fun i θ => leading (p i) (P i) θ) hdata
  obtain ⟨σ, _hσ, hoσ, _htσ, hman⟩ := complete_of_finite_phases hf hfinite htrans p hp P hP0 hphase
  have he : σ = d i := Rat.cast_injective (isOrder_unique hoσ horder)
  subst σ
  obtain ⟨h, hcrg, hi⟩ := hman
  refine ⟨d i, hdi, horder, htype, h, hcrg, hi, ?_⟩
  have halt : ∀ θ : ℝ, ∃ c ∈ C (d i),
      h (CRGOrderLevin.angleDirection θ) = leadingReal c (d i : ℝ) θ := by
    intro θ
    obtain ⟨j, hj⟩ := indicator_alternatives hf (by exact_mod_cast hdi)
      horder htype p hp P hP0 hphase hcrg hi θ
    refine ⟨if (d j : ℝ) = (d i : ℝ) then (P j).leadingCoeff else 0,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    simpa only [d, Rat.cast_div, Rat.cast_natCast] using hj
  intro z hz haway
  apply hR ⟨i, hdi⟩ h hcrg.1 halt z hz
  intro hmem
  exact haway (Finset.mem_biUnion.mpr ⟨⟨i, hdi⟩, Finset.mem_univ _, hmem⟩)

#print axioms harmonicAt_of_indicator_interval
#print axioms finite_alternatives_harmonic_off_rays
#print axioms exists_fixed_harmonic_rays
end CRGZeroDistributionHarmonic
