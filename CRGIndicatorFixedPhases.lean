import CRGTheorem11

/-! Fixed phase data for a fixed, possibly nonmonic, exponential-polynomial ODE.
The coefficient data and phase family are constructed before any solution is
chosen. This is the equation-independent input required by Corollary 3.6. -/
set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory Polynomial
open scoped Topology BigOperators
namespace CRGIndicatorFixedPhases
open CRGExponentialCoefficients CRGCollectedEquation CRGCollectedResidual
open CRGNormalFormGoal CRGGroupHighest

/-- An actual finite collection of coefficient groups, with no solution stored. -/
structure EquationData (n : ℕ) where
  exponents : Finset (Polynomial ℂ)
  nonempty : exponents.Nonempty
  coeff : Polynomial ℂ → Fin (n+1) → Polynomial ℂ
  normalized : ∀ q ∈ exponents, q.coeff 0 = 0
  nonzero_group : ∀ q ∈ exponents, ∃ j, coeff q j ≠ 0

def EquationData.Solves {n : ℕ} (E : EquationData n) (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ∑ q ∈ E.exponents, Complex.exp (q.eval z) *
    (∑ j, (E.coeff q j).eval z * iteratedDeriv j.val f z) = 0

def EquationData.withSolution {n : ℕ} (E : EquationData n)
    (f : ℂ → ℂ) (hf : E.Solves f) : CollectedEquation n f :=
  ⟨E.exponents, E.nonempty, E.coeff, E.normalized, E.nonzero_group, hf⟩

/-- The nonmonic differential equation, including the leading coefficient. -/
def SolvesEquation {n : ℕ} (A : Fin (n+1) → ℂ → ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ∑ j, A j z * iteratedDeriv j.val f z = 0

/-- Collection depends only on the given coefficients, and works simultaneously
for every solution of the fixed nonmonic equation. -/
theorem exists_fixed_equation_data {n : ℕ} (A : Fin (n+1) → ℂ → ℂ)
    (hA : ∀ j, IsExponentialPolynomial (A j))
    (htop : ∃ z : ℂ, A (Fin.last n) z ≠ 0) :
    ∃ E : EquationData n, ∀ f : ℂ → ℂ, SolvesEquation A f ↔ E.Solves f := by
  classical
  choose N P Q hrep using hA
  let ι := (j : Fin (n+1)) × Fin (N j)
  let P' : ι → Polynomial ℂ := fun i => P i.1 i.2
  let Q' : ι → Polynomial ℂ := fun i => Q i.1 i.2
  let k : ι → Fin (n+1) := fun i => i.1
  let b := coefficientGroup P' Q' k
  let S := Finset.univ.image (fun i : ι => normalizedExponent (Q' i))
  let T := S.filter (fun q => ∃ j, b q j ≠ 0)
  have hid (v : Fin (n+1) → ℂ) (z : ℂ) :
      (∑ j, A j z * v j) = ∑ q ∈ T, Complex.exp (q.eval z) *
        (∑ j, (b q j).eval z * v j) := by
    calc
      _ = ∑ i : ι, (P' i).eval z * Complex.exp ((Q' i).eval z) * v (k i) := by
        simp only [ι, Fintype.sum_sigma]
        simp_rw [hrep, Finset.sum_mul]
        rfl
      _ = ∑ q ∈ S, Complex.exp (q.eval z) *
          (∑ j, (b q j).eval z * v j) := collected_identity P' Q' k v z
      _ = _ := by
        rw [show T = S.filter (fun q => ∃ j, b q j ≠ 0) from rfl, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro q _
        split_ifs with h
        · rfl
        · have hz : ∀ j, b q j = 0 := by simpa using h
          simp [hz]
  have hT : T.Nonempty := by
    by_contra h
    have hTe : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨z, hz⟩ := htop
    have hh := hid (fun j => if j = Fin.last n then 1 else 0) z
    apply hz
    simpa [hTe] using hh
  refine ⟨⟨T, hT, b, ?_, ?_⟩, ?_⟩
  · intro q hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
    rw [← hi]
    exact normalizedExponent_zero _
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro f
    change (∀ z, _ = 0) ↔ (∀ z, _ = 0)
    simp_rw [hid]

/-- The actual a.e. comparison with one fixed finite ramified-polynomial family. -/
def PhaseComparison {ι : Type*} (p : ι → ℕ) (hp : ∀ i, 0 < p i)
    (P : ι → Polynomial ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ᵐ θ : ℝ, ∃ i : ι,
    (∀ᶠ r : ℝ in atTop, f (ray θ r) ≠ 0) ∧
    ∃ C : ℝ, ∀ᶠ r : ℝ in atTop,
      |Real.log ‖f (ray θ r)‖ - (phaseOnRay (p i) (P i) θ ⟨0, hp i⟩ r).re| ≤ C * Real.log r

/-- The finite phase family of a fixed coefficient collection is independent
of the chosen finite-order nonpolynomial entire solution. -/
theorem EquationData.exists_fixed_phases {n : ℕ} (E : EquationData n) :
    ∃ ι : Type, ∃ _ : Fintype ι, ∃ p : ι → ℕ, ∃ hp : ∀ i, 0 < p i,
      ∃ P : ι → Polynomial ℂ, (∀ i, (P i).coeff 0 = 0) ∧
      ∀ f : ℂ → ℂ, Differentiable ℂ f → CRGOrder.FiniteOrder f →
        (¬ ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z) →
        E.Solves f → PhaseComparison p hp P f := by
  classical
  let : Nonempty E.exponents := E.nonempty.to_subtype
  let H : (q : E.exponents) → Highest (E.coeff q.val) := fun q =>
    Classical.choice (exists_highest (E.coeff q.val) (E.nonzero_group q.val q.property))
  choose d p hp G hG hcompare using fun q : E.exponents =>
    CRGPolynomialGroupComparison.group_ray_comparison (E.coeff q.val) (H q)
  let ι := (q : E.exponents) × Fin (d q + 1)
  refine ⟨ι, inferInstance, fun i => p i.1,
    fun i => hp i.1, fun i => G i.1 i.2, fun i => hG i.1 i.2, ?_⟩
  intro f hf hfinite htrans heq
  let Ef := E.withSolution f heq
  obtain ⟨ρ, hρ, ho⟩ := hfinite
  have hn : ∃ z : ℂ, f z ≠ 0 := by
    by_contra hz
    push Not at hz
    exact htrans ⟨0, fun z => by simpa using hz z⟩
  have hdom := CRGExponentialDominance.ae_exists_dominant_group
    (fun q : E.exponents => q.val) (fun q => E.normalized q.val q.property)
    Subtype.val_injective
  filter_upwards [hdom, GundersenTheorem.ae_ray_input hf hn hρ ho] with θ hθ hg
  obtain ⟨ν, c, hc, hphase⟩ := hθ
  have hnon : ∀ᶠ r in atTop, f (ray θ r) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact hg.1 r hr
  have hjet := hg.2.1 n 1 zero_lt_one
  obtain ⟨B, hB, J, hJ, R, _hR, hcont, hcontrol⟩ := exists_residual_control Ef hf θ ρ hρ ν
    (E.coeff ν.val (H ν).index) (H ν).nonzero c hc hphase hnon hjet
  have hcommon := common_jet_bound θ ρ hρ hnon hjet
  obtain ⟨j, M, _hM, herror⟩ := hcompare ν θ f hf
    (residual Ef ν (E.coeff ν.val (H ν).index) θ) R B J c hcont hB hJ hc
    (fun r hr => (hcontrol r hr).2.2.1)
    (fun r hr => ⟨(hcontrol r hr).1, (hcontrol r hr).2.2.2.2,
      (hcontrol r hr).2.2.2.1⟩)
    hnon 1 ((n : ℝ) * ρ) zero_lt_one (mul_nonneg (Nat.cast_nonneg _) hρ) (by
      filter_upwards [hcommon] with r hr
      intro k _hk hkn
      simpa only [one_mul] using hr ⟨k, Nat.lt_succ_of_le hkn⟩)
  exact ⟨⟨ν, j⟩, hnon, M, herror⟩

#print axioms exists_fixed_equation_data
#print axioms EquationData.exists_fixed_phases
end CRGIndicatorFixedPhases
