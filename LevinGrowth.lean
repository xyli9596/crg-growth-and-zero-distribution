import LevinGeometry
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
Precise constant-order growth definitions for the manuscript. The nonzero clauses
ensure that totalized `Real.log 0 = 0` cannot erase zeros from the mathematical
statement. The original full dense-ray-to-C₀ proposition is defined at the end.
Its proof is supplied by `LevinC0.constantOrderLevin` in LevinC0.lean.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace LevinGrowth

abbrev Direction := {ζ : ℂ // ‖ζ‖ = 1}

def rayPoint (r : ℝ) (ζ : Direction) : ℂ := (r : ℂ) * ζ.val

def normalizedLog (f : ℂ → ℂ) (ρ r : ℝ) (ζ : Direction) : ℝ :=
  Real.log ‖f (rayPoint r ζ)‖ / r ^ ρ

/-- For the unrestricted indicator, zeros have value minus infinity rather than
the totalized real logarithm's value zero. All applications are at positive radii. -/
def extendedNormalizedLog (f : ℂ → ℂ) (ρ r : ℝ) (ζ : Direction) : EReal :=
  if f (rayPoint r ζ) = 0 then ⊥ else (normalizedLog f ρ r ζ : EReal)

def IsIndicator (f : ℂ → ℂ) (ρ : ℝ) (h : Direction → ℝ) : Prop :=
  ∀ ζ : Direction,
    Filter.limsup (fun r : ℝ => extendedNormalizedLog f ρ r ζ) atTop = (h ζ : EReal)

theorem norm_rayPoint {r : ℝ} (hr : 0 ≤ r) (ζ : Direction) :
    ‖rayPoint r ζ‖ = r := by
  simp [rayPoint, ζ.property, Real.norm_of_nonneg hr]

/-- Upper finite type and positive type along an unbounded sequence, at the same
fixed exponent. For positive ρ these are the usual finite nonzero type bounds. -/
def FinitePositiveType (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (C * ‖z‖ ^ ρ)) ∧
  (∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∃ z : ℂ, max R 1 ≤ ‖z‖ ∧
    Real.exp (c * ‖z‖ ^ ρ) ≤ ‖f z‖)

theorem finitePositiveType_nontrivial {f : ℂ → ℂ} {ρ : ℝ}
    (hf : FinitePositiveType f ρ) : ∃ z : ℂ, f z ≠ 0 := by
  obtain ⟨c, _, hc⟩ := hf.2
  obtain ⟨z, _, hz⟩ := hc 1
  refine ⟨z, ?_⟩
  have hp : 0 < ‖f z‖ := (Real.exp_pos _).trans_le hz
  exact norm_pos_iff.mp hp

theorem entire_zeroSet_countable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∃ z : ℂ, f z ≠ 0) : {z : ℂ | f z = 0}.Countable := by
  have ha : AnalyticOnNhd ℂ f univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with hz | hz
  · obtain ⟨z, hnz⟩ := hn
    exact False.elim (hnz (hz (mem_univ z)))
  · have hc : {z : ℂ | f z = 0}ᶜ ∈ codiscrete ℂ := hz
    obtain ⟨hclosed, hdiscrete⟩ := compl_mem_codiscrete_iff.mp hc
    exact hclosed.isLindelof.countable_of_isDiscrete hdiscrete

def zeroRadii (f : ℂ → ℂ) : Set ℝ := (fun z : ℂ => ‖z‖) '' {z : ℂ | f z = 0}

theorem zeroRadii_countable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∃ z : ℂ, f z ≠ 0) : (zeroRadii f).Countable :=
  (entire_zeroSet_countable hf hn).image _

theorem zeroRadii_zero_density {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∃ z : ℂ, f z ≠ 0) : LevinDensity.ZeroRadialDensity (zeroRadii f) := by
  have hzero := (zeroRadii_countable hf hn).measure_zero (volume : Measure ℝ)
  intro ε hε
  refine ⟨0, le_rfl, fun R hR => ?_⟩
  calc
    volume (zeroRadii f ∩ Icc 0 R) ≤ volume (zeroRadii f) := measure_mono inter_subset_left
    _ = 0 := hzero
    _ ≤ _ := bot_le

theorem nonzero_of_not_zeroRadii {f : ℂ → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (he : r ∉ zeroRadii f) (ζ : Direction) : f (rayPoint r ζ) ≠ 0 := by
  intro hz
  apply he
  exact ⟨rayPoint r ζ, hz, norm_rayPoint hr ζ⟩

/-- One can choose a circle avoiding every zero inside any nonempty radial interval.
This supplies the boundary condition for local finite Blaschke decomposition. -/
theorem exists_zero_free_sphere_between {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∃ z : ℂ, f z ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ R ∈ Ioo a b, ∀ z : ℂ, ‖z‖ = R → f z ≠ 0 := by
  have hzero := (zeroRadii_countable hf hn).measure_zero (volume : Measure ℝ)
  have hnot : ¬ Ioo a b ⊆ zeroRadii f := by
    intro hsub
    have hle : volume (Ioo a b) ≤ volume (zeroRadii f) := measure_mono hsub
    rw [hzero, Real.volume_Ioo] at hle
    have hp : (0 : ℝ≥0∞) < ENNReal.ofReal (b - a) := ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
    exact (not_le_of_gt hp) hle
  obtain ⟨R, hR, hnR⟩ := Set.not_subset.mp hnot
  refine ⟨R, hR, fun z hz hnz => ?_⟩
  exact hnR ⟨z, hnz, hz⟩

/-- One ray has a finite limit outside a measurable zero-density radial set. -/
def RayRegular (f : ℂ → ℂ) (ρ : ℝ) (ζ : Direction) (h : ℝ) : Prop :=
  ∃ E : Set ℝ, MeasurableSet E ∧ LevinDensity.ZeroRadialDensity E ∧
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ r : ℝ, R ≤ r → r ∉ E →
        f (rayPoint r ζ) ≠ 0 ∧ |normalizedLog f ρ r ζ - h| < ε

/-- One common radial exceptional set and uniform convergence over the unit circle. -/
def RadialRegular (f : ℂ → ℂ) (ρ : ℝ) (h : Direction → ℝ) : Prop :=
  Continuous h ∧ ∃ E : Set ℝ, MeasurableSet E ∧ LevinDensity.ZeroRadialDensity E ∧
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ r : ℝ, R ≤ r → r ∉ E → ∀ ζ : Direction,
        f (rayPoint r ζ) ≠ 0 ∧ |normalizedLog f ρ r ζ - h ζ| < ε

/-- Uniform CRG outside a concrete family of C₀ disks, as required by the manuscript. -/
def DiskRegular (f : ℂ → ℂ) (ρ : ℝ) (h : Direction → ℝ) : Prop :=
  Continuous h ∧ ∃ D : LevinGeometry.DiskFamily, LevinGeometry.IsC0 D ∧
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ r : ℝ, R ≤ r → ∀ ζ : Direction, rayPoint r ζ ∉ LevinGeometry.disks D →
        f (rayPoint r ζ) ≠ 0 ∧ |normalizedLog f ρ r ζ - h ζ| < ε

/-- The easy geometric direction of the equivalence uses the actual radial shadow
of the exceptional disks. It requires no analytic hypothesis on f. -/
theorem diskRegular_radialRegular {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : DiskRegular f ρ h) : RadialRegular f ρ h := by
  obtain ⟨hh, D, hD, hgrowth⟩ := hf
  refine ⟨hh, LevinGeometry.radialShadow D,
    LevinGeometry.measurableSet_radialShadow D,
    LevinGeometry.radialShadow_zero_density D hD, ?_⟩
  intro ε hε
  obtain ⟨R, hR, hbound⟩ := hgrowth ε hε
  refine ⟨R, hR, fun r hr he ζ => hbound r hr ζ ?_⟩
  intro hz
  apply he
  have hs := LevinGeometry.norm_mem_radialShadow D hz
  simpa only [norm_rayPoint (hR.le.trans hr) ζ] using hs

theorem radialRegular_rayRegular {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : RadialRegular f ρ h) (ζ : Direction) : RayRegular f ρ ζ (h ζ) := by
  obtain ⟨_, E, hE, hzero, hgrowth⟩ := hf
  refine ⟨E, hE, hzero, fun ε hε => ?_⟩
  obtain ⟨R, hR, hbound⟩ := hgrowth ε hε
  exact ⟨R, hR, fun r hr he => hbound r hr he ζ⟩

/-- The manuscript uses the unrestricted Phragmén--Lindelöf indicator, so its
identification is retained as an explicit part of the final goal. -/
def ManuscriptCRG (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∃ h : Direction → ℝ, DiskRegular f ρ h ∧ IsIndicator f ρ h

/-- The original full analytic goal, proved by `LevinC0.constantOrderLevin`. -/
def ConstantOrderLevinGoal : Prop :=
  ∀ (f : ℂ → ℂ) (ρ : ℝ), Differentiable ℂ f → 0 < ρ →
    FinitePositiveType f ρ →
    Dense {ζ : Direction | ∃ h : ℝ, RayRegular f ρ ζ h} →
    ManuscriptCRG f ρ

#print axioms norm_rayPoint
#print axioms finitePositiveType_nontrivial
#print axioms entire_zeroSet_countable
#print axioms zeroRadii_countable
#print axioms zeroRadii_zero_density
#print axioms nonzero_of_not_zeroRadii
#print axioms exists_zero_free_sphere_between
#print axioms diskRegular_radialRegular
#print axioms radialRegular_rayRegular
end LevinGrowth
