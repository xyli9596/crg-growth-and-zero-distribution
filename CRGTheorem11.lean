import CRGCollectedResidual
import CRGPolynomialGroupComparison
import CRGFinitePhaseEndgame

/-! Manuscript Theorem 1.1 for the actual monic scalar differential equation
with exponential-polynomial coefficients. The proof constructs its groups,
Gundersen exceptional directions, continuous small residuals, fixed Wasow phase
families, and the Phragmen-Lindelof / Levin conclusion from the stated inputs. -/
set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory Polynomial
open scoped Topology BigOperators
namespace CRGTheorem11
open CRGNormalFormGoal CRGCollectedEquation CRGCollectedResidual
open CRGExponentialCoefficients CRGGroupHighest

/-- The complete analytic conclusion for an actual nonempty collected equation.
No derivative estimate, residual bound, or phase comparison is a hypothesis. -/
theorem of_collected_equation {n : ℕ} {f : ℂ→ℂ}
    (E : CollectedEquation n f) (hf : Differentiable ℂ f)
    (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬ ∃P : Polynomial ℂ, ∀z : ℂ,f z=P.eval z) :
    ∃σ : ℚ,0<σ ∧ CRGOrder.IsOrder f (σ:ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ:ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ:ℝ) := by
  classical
  let : Nonempty E.exponents := E.nonempty.to_subtype
  let H : (q:E.exponents)→Highest (E.coeff q.val) := fun q=>
    Classical.choice (exists_highest (E.coeff q.val) (E.nonzero_group q.val q.property))
  choose d p hp G hG hcompare using fun q:E.exponents=>
    CRGPolynomialGroupComparison.group_ray_comparison (E.coeff q.val) (H q)
  let ι := (q:E.exponents) × Fin (d q+1)
  apply CRGFinitePhaseEndgame.complete_of_finite_phases (ι:=ι) hf hfinite htrans
    (fun i=>p i.1) (fun i=>hp i.1) (fun i=>G i.1 i.2) (fun i=>hG i.1 i.2)
  obtain ⟨ρ,hρ,ho⟩ := hfinite
  have hn : ∃z : ℂ,f z≠0 := by
    by_contra hz
    push Not at hz
    apply htrans
    exact ⟨0,fun z=>by simpa using hz z⟩
  have hdom := CRGExponentialDominance.ae_exists_dominant_group
    (fun q:E.exponents=>q.val) (fun q=>E.normalized q.val q.property) Subtype.val_injective
  filter_upwards [hdom,GundersenTheorem.ae_ray_input hf hn hρ ho] with θ hθ hg
  obtain ⟨ν,c,hc,hphase⟩ := hθ
  have hnon : ∀ᶠr in atTop,f (ray θ r)≠0 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact hg.1 r hr
  have hjet := hg.2.1 n 1 zero_lt_one
  obtain ⟨B,hB,J,hJ,R,_hR,hcont,hcontrol⟩ := exists_residual_control E hf θ ρ hρ ν
    (E.coeff ν.val (H ν).index) (H ν).nonzero c hc hphase hnon hjet
  have hcommon := common_jet_bound θ ρ hρ hnon hjet
  obtain ⟨j,M,_hM,herror⟩ := hcompare ν θ f hf
    (residual E ν (E.coeff ν.val (H ν).index) θ) R B J c hcont hB hJ hc
    (fun r hr=>(hcontrol r hr).2.2.1)
    (fun r hr=>⟨(hcontrol r hr).1,(hcontrol r hr).2.2.2.2,
      (hcontrol r hr).2.2.2.1⟩)
    hnon 1 ((n:ℝ)*ρ) zero_lt_one (mul_nonneg (Nat.cast_nonneg _) hρ) (by
      filter_upwards [hcommon] with r hr
      intro k _hk hkn
      simpa only [one_mul] using hr ⟨k,Nat.lt_succ_of_le hkn⟩)
  exact ⟨⟨ν,j⟩,hnon,M,herror⟩

/-- Manuscript Theorem 1.1: every transcendental entire finite-order solution
of a monic ODE with exponential-polynomial coefficients has positive rational
order, finite positive type, and completely regular growth in the C0-disk sense
with its unrestricted indicator. -/
theorem theorem_1_1 {n : ℕ} (a : Fin n→ℂ→ℂ) (f : ℂ→ℂ)
    (ha : ∀k,IsExponentialPolynomial (a k))
    (hf : Differentiable ℂ f) (hfinite : CRGOrder.FiniteOrder f)
    (htrans : ¬ ∃P : Polynomial ℂ, ∀z : ℂ,f z=P.eval z)
    (heq : SolvesMonicEquation n a f) :
    ∃σ : ℚ,0<σ ∧ CRGOrder.IsOrder f (σ:ℝ) ∧
      LevinGrowth.FinitePositiveType f (σ:ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ:ℝ) := by
  obtain ⟨E⟩ := exists_collected_equation a f ha heq
  exact of_collected_equation E hf hfinite htrans

#print axioms of_collected_equation
#print axioms theorem_1_1
end CRGTheorem11
