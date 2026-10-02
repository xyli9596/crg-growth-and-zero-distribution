import CRGIndicatorFixedPhases
import CRGPuiseuxMonic

/-! Explicit manuscript Theorems 3.2 and 3.5. The phase list of each
coefficient differential equation is fixed before a solution or direction.
For linear exponents, a vertex sector is encoded by its strict supporting
inequalities. No sector-uniform logarithmic error is asserted. -/
set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory Polynomial
open scoped Topology BigOperators
namespace CRGSection3Alignment
open CRGNormalFormGoal CRGIndicatorFixedPhases CRGCollectedResidual
open CRGExponentialCoefficients CRGGroupHighest CRGPuiseuxMonic

def GrowthConclusion (f : ℂ → ℂ) : Prop :=
  ∃ σ : ℚ, 0 < σ ∧ CRGOrder.IsOrder f (σ : ℝ) ∧
    LevinGrowth.FinitePositiveType f (σ : ℝ) ∧ LevinGrowth.ManuscriptCRG f (σ : ℝ)

structure GroupPhases {n : ℕ} (E : EquationData n) where
  count : E.exponents → ℕ
  denominator : E.exponents → ℕ
  positive : ∀ ν, 0 < denominator ν
  polynomial : (ν : E.exponents) → Fin (count ν + 1) → Polynomial ℂ
  normalized : ∀ ν j, (polynomial ν j).coeff 0 = 0

def RayDominant {n : ℕ} (E : EquationData n) (ν : E.exponents) (θ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in atTop, ∀ μ : E.exponents, μ ≠ ν →
    ((μ.val - ν.val).eval (ray θ r)).re ≤ -c*r

def GroupComparison {n : ℕ} {E : EquationData n} (D : GroupPhases E)
    (ν : E.exponents) (f : ℂ → ℂ) (θ : ℝ) : Prop :=
  ∃ j : Fin (D.count ν + 1), ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℝ in atTop,
    f (ray θ r) ≠ 0 ∧
    |Real.log ‖f (ray θ r)‖ -
      (phaseOnRay (D.denominator ν) (D.polynomial ν j) θ ⟨0,D.positive ν⟩ r).re|
      ≤ C * Real.log r

/-- One family per actual coefficient equation, with a common denominator
within each group. The selected group is retained in the conclusion. -/
theorem exists_group_phases {n : ℕ} (E : EquationData n) :
    ∃ D : GroupPhases E, ∀ f : ℂ → ℂ, Differentiable ℂ f →
      CRGOrder.FiniteOrder f → (¬∃ P : Polynomial ℂ, ∀ z, f z = P.eval z) →
      E.Solves f → ∀ᵐ θ : ℝ, ∀ ν : E.exponents,
        RayDominant E ν θ → GroupComparison D ν f θ := by
  classical
  let H : (ν : E.exponents) → Highest (E.coeff ν.val) := fun ν =>
    Classical.choice (exists_highest (E.coeff ν.val) (E.nonzero_group ν.val ν.property))
  choose d p hp G hG hcompare using fun ν : E.exponents =>
    CRGPolynomialGroupComparison.group_ray_comparison (E.coeff ν.val) (H ν)
  let D : GroupPhases E := ⟨d,p,hp,G,hG⟩
  refine ⟨D,?_⟩
  intro f hf hfinite htrans heq
  let Ef := E.withSolution f heq
  obtain ⟨ρ,hρ,ho⟩ := hfinite
  have hn : ∃ z : ℂ, f z ≠ 0 := by
    by_contra hz
    push Not at hz
    exact htrans ⟨0,fun z => by simpa using hz z⟩
  filter_upwards [GundersenTheorem.ae_ray_input hf hn hρ ho] with θ hg
  intro ν hdom
  obtain ⟨c,hc,hphase⟩ := hdom
  have hnon : ∀ᶠ r : ℝ in atTop, f (ray θ r) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact hg.1 r hr
  have hjet := hg.2.1 n 1 zero_lt_one
  obtain ⟨B,hB,J,hJ,R,_hR,hcont,hcontrol⟩ := exists_residual_control Ef hf θ ρ hρ ν
    (E.coeff ν.val (H ν).index) (H ν).nonzero c hc hphase hnon hjet
  have hcommon := common_jet_bound θ ρ hρ hnon hjet
  obtain ⟨j,M,hM,herror⟩ := hcompare ν θ f hf
    (residual Ef ν (E.coeff ν.val (H ν).index) θ) R B J c hcont hB hJ hc
    (fun r hr => (hcontrol r hr).2.2.1)
    (fun r hr => ⟨(hcontrol r hr).1,(hcontrol r hr).2.2.2.2,
      (hcontrol r hr).2.2.2.1⟩)
    hnon 1 ((n:ℝ)*ρ) zero_lt_one (mul_nonneg (Nat.cast_nonneg _) hρ) (by
      filter_upwards [hcommon] with r hr
      intro k _hk hkn
      simpa only [one_mul] using hr ⟨k,Nat.lt_succ_of_le hkn⟩)
  refine ⟨j,M,hM,?_⟩
  filter_upwards [hnon,herror] with r hr he
  exact ⟨hr,he⟩

/-- Convert the almost-everywhere assertion into the manuscript's explicit
Lebesgue-null exceptional set in one argument interval. -/
theorem exists_null_set_in_turn {P : ℝ → Prop} (hP : ∀ᵐ θ : ℝ, P θ) :
    ∃ N : Set ℝ, N ⊆ Ico 0 (2*Real.pi) ∧ volume N = 0 ∧
      ∀ θ ∈ Ico 0 (2*Real.pi), θ ∉ N → P θ := by
  classical
  let N := Ico 0 (2*Real.pi) ∩ {θ | ¬P θ}
  refine ⟨N,inter_subset_left,measure_mono_null inter_subset_right (ae_iff.mp hP),?_⟩
  intro θ hθ hn
  by_contra hp
  exact hn ⟨hθ,hp⟩

def Theorem35Conclusion {n : ℕ} {E : EquationData n} (D : GroupPhases E)
    (f : ℂ → ℂ) : Prop :=
  GrowthConclusion f ∧ ∃ N : Set ℝ, N ⊆ Ico 0 (2*Real.pi) ∧ volume N = 0 ∧
    ∀ θ ∈ Ico 0 (2*Real.pi), θ ∉ N →
      ∃ ν : E.exponents, RayDominant E ν θ ∧ GroupComparison D ν f θ

/-- Full Theorem 3.5 for the actual collected equation. The order/type/CRG
and complete ray-tail estimate hold together, using coefficient-only phases. -/
theorem theorem_3_5_collected {n : ℕ} (E : EquationData n) :
    ∃ D : GroupPhases E, ∀ f : ℂ → ℂ, Differentiable ℂ f →
      CRGOrder.FiniteOrder f → (¬∃ P : Polynomial ℂ, ∀ z, f z = P.eval z) →
      E.Solves f → Theorem35Conclusion D f := by
  classical
  let : Nonempty E.exponents := E.nonempty.to_subtype
  obtain ⟨D,hD⟩ := exists_group_phases E
  refine ⟨D,?_⟩
  intro f hf hfinite htrans heq
  refine ⟨CRGTheorem11.of_collected_equation (E.withSolution f heq) hf hfinite htrans,?_⟩
  apply exists_null_set_in_turn
  have hdom := CRGExponentialDominance.ae_exists_dominant_group
    (fun ν : E.exponents => ν.val) (fun ν => E.normalized ν.val ν.property)
    Subtype.val_injective
  filter_upwards [hdom,hD f hf hfinite htrans heq] with θ hθ hcomp
  obtain ⟨ν,c,hc,hphase⟩ := hθ
  exact ⟨ν,⟨c,hc,hphase⟩,hcomp ν ⟨c,hc,hphase⟩⟩

theorem fullCoefficient_isExponentialPolynomial {n : ℕ} (a : Fin n → ℂ → ℂ)
    (ha : ∀ j, IsExponentialPolynomial (a j)) :
    ∀ j, IsExponentialPolynomial (fullCoefficient a j) := by
  intro j
  induction j using Fin.lastCases with
  | last =>
    refine ⟨1,fun _ => 1,fun _ => 0,?_⟩
    intro z
    simp [fullCoefficient]
  | cast j => simpa only [fullCoefficient,Fin.lastCases_castSucc] using ha j

/-- The original monic exponential-polynomial equation of Theorem 3.5,
without assuming derivative bounds, residuals or a normal form. -/
theorem theorem_3_5 {n : ℕ} (a : Fin n → ℂ → ℂ)
    (ha : ∀ j, IsExponentialPolynomial (a j)) :
    ∃ E : EquationData n,
      (∀ f : ℂ → ℂ, SolvesMonicEquation n a f ↔ E.Solves f) ∧
      ∃ D : GroupPhases E, ∀ f : ℂ → ℂ, Differentiable ℂ f →
        CRGOrder.FiniteOrder f → (¬∃ P : Polynomial ℂ, ∀ z, f z = P.eval z) →
        SolvesMonicEquation n a f → Theorem35Conclusion D f := by
  obtain ⟨E,hE⟩ := exists_fixed_equation_data (fullCoefficient a)
    (fullCoefficient_isExponentialPolynomial a ha) ⟨0,by simp⟩
  have hsame (f : ℂ → ℂ) : SolvesMonicEquation n a f ↔ E.Solves f := by
    rw [←hE]
    constructor
    · exact full_equation a f
    · intro h z
      have hh := h z
      rw [Fin.sum_univ_castSucc] at hh
      simpa only [fullCoefficient_last,fullCoefficient_castSucc,Fin.val_last,
        Fin.val_castSucc,one_mul,add_comm] using hh
  obtain ⟨D,hD⟩ := theorem_3_5_collected E
  exact ⟨E,hsame,D,fun f hf hfinite htrans heq => hD f hf hfinite htrans ((hsame f).mp heq)⟩

def LinearExponents {n : ℕ} (E : EquationData n) : Prop :=
  ∀ ν : E.exponents, ν.val.natDegree ≤ 1

/-- Strict supporting inequalities for the conjugate-frequency hull. This
defines the interior vertex sector without choosing a polygon enumeration;
it also covers a segment hull and the one-frequency case. -/
def VertexDirection {n : ℕ} (E : EquationData n) (ν : E.exponents) (θ : ℝ) : Prop :=
  ∀ μ : E.exponents, μ ≠ ν →
    ((μ.val.coeff 1 - ν.val.coeff 1) * Complex.exp ((θ:ℂ)*Complex.I)).re < 0

theorem linear_eval_on_ray {P : Polynomial ℂ} (hP : P.natDegree ≤ 1)
    (hP0 : P.coeff 0 = 0) (θ r : ℝ) :
    P.eval (ray θ r) = (r:ℂ) * (P.coeff 1 * Complex.exp ((θ:ℂ)*Complex.I)) := by
  have he := P.eq_X_add_C_of_natDegree_le_one hP
  conv_lhs => rw [he]
  simp only [eval_add,eval_mul,eval_C,eval_X,hP0,add_zero,ray]
  ring

/-- Every interior vertex direction has one positive decay gap for all
other frequency groups on its complete positive ray. -/
theorem vertexDirection_rayDominant {n : ℕ} (E : EquationData n)
    (hlinear : LinearExponents E) (ν : E.exponents) (θ : ℝ)
    (hθ : VertexDirection E ν θ) : RayDominant E ν θ := by
  classical
  let : Nonempty E.exponents := E.nonempty.to_subtype
  let c : E.exponents → ℝ := fun μ =>
    if μ = ν then 1 else -((μ.val.coeff 1 - ν.val.coeff 1) *
      Complex.exp ((θ:ℂ)*Complex.I)).re
  have hc (μ : E.exponents) : 0 < c μ := by
    by_cases he : μ = ν
    · simp [c,he]
    · simpa [c,he] using neg_pos.mpr (hθ μ he)
  let s := Finset.univ.image c
  have hs : s.Nonempty := Finset.univ_nonempty.image c
  let C := s.min' hs
  have hC : 0 < C := by
    obtain ⟨μ,_hμ,he⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
    dsimp [C]
    rw [←he]
    exact hc μ
  have hCμ (μ : E.exponents) : C ≤ c μ :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨μ,Finset.mem_univ _,rfl⟩)
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  intro μ hμ
  have heval : ((μ.val - ν.val).eval (ray θ r)).re =
      r * ((μ.val.coeff 1 - ν.val.coeff 1) * Complex.exp ((θ:ℂ)*Complex.I)).re := by
    rw [eval_sub,linear_eval_on_ray (hlinear μ) (E.normalized μ.val μ.property),
      linear_eval_on_ray (hlinear ν) (E.normalized ν.val ν.property)]
    rw [←mul_sub,←sub_mul]
    simp
  rw [heval]
  have hh := neg_le_neg (hCμ μ)
  simp only [c,if_neg hμ,neg_neg] at hh
  exact (mul_le_mul_of_nonneg_left hh hr).trans_eq (by ring)

def Theorem32Conclusion {n : ℕ} {E : EquationData n} (D : GroupPhases E)
    (f : ℂ → ℂ) : Prop :=
  GrowthConclusion f ∧ ∃ N : Set ℝ, N ⊆ Ico 0 (2*Real.pi) ∧ volume N = 0 ∧
    ∀ θ ∈ Ico 0 (2*Real.pi), θ ∉ N → ∀ ν : E.exponents,
      VertexDirection E ν θ → GroupComparison D ν f θ

/-- Full Theorem 3.2 for collected linear exponents. A vertex's phase list
and denominator come from that vertex's coefficient differential equation. -/
theorem theorem_3_2_collected {n : ℕ} (E : EquationData n)
    (hlinear : LinearExponents E) :
    ∃ D : GroupPhases E, ∀ f : ℂ → ℂ, Differentiable ℂ f →
      CRGOrder.FiniteOrder f → (¬∃ P : Polynomial ℂ, ∀ z, f z = P.eval z) →
      E.Solves f → Theorem32Conclusion D f := by
  obtain ⟨D,hD⟩ := exists_group_phases E
  refine ⟨D,?_⟩
  intro f hf hfinite htrans heq
  refine ⟨CRGTheorem11.of_collected_equation (E.withSolution f heq) hf hfinite htrans,?_⟩
  apply exists_null_set_in_turn
  filter_upwards [hD f hf hfinite htrans heq] with θ hθ
  exact fun ν hν => hθ ν (vertexDirection_rayDominant E hlinear ν θ hν)

def IsExponentialSum (g : ℂ → ℂ) : Prop :=
  ∃ N : ℕ, ∃ P : Fin N → Polynomial ℂ, ∃ ω : Fin N → ℂ,
    ∀ z, g z = ∑ i, (P i).eval z * Complex.exp (ω i * z)

/-- Collect the original exponential sums, retaining their linear exponents
and cancelling zero groups before any solution is chosen. -/
theorem exists_linear_equation_data {n : ℕ} (A : Fin (n+1) → ℂ → ℂ)
    (hA : ∀ j, IsExponentialSum (A j)) (htop : ∃ z, A (Fin.last n) z ≠ 0) :
    ∃ E : EquationData n, LinearExponents E ∧
      ∀ f : ℂ → ℂ, SolvesEquation A f ↔ E.Solves f := by
  classical
  choose N P ω hrep using hA
  let ι := (j : Fin (n+1)) × Fin (N j)
  let P' : ι → Polynomial ℂ := fun i => P i.1 i.2
  let Q' : ι → Polynomial ℂ := fun i => C (ω i.1 i.2) * X
  let k : ι → Fin (n+1) := fun i => i.1
  let b := CRGCollectedEquation.coefficientGroup P' Q' k
  let S := Finset.univ.image (fun i : ι => normalizedExponent (Q' i))
  let T := S.filter (fun q => ∃ j, b q j ≠ 0)
  have hid (v : Fin (n+1) → ℂ) (z : ℂ) :
      (∑ j, A j z * v j) = ∑ q ∈ T, Complex.exp (q.eval z) *
        (∑ j, (b q j).eval z * v j) := by
    calc
      _ = ∑ i : ι, (P' i).eval z * Complex.exp ((Q' i).eval z) * v (k i) := by
        simp only [ι,Fintype.sum_sigma]
        simp_rw [hrep,Finset.sum_mul]
        simp [P',Q',k]
      _ = ∑ q ∈ S, Complex.exp (q.eval z) *
          (∑ j, (b q j).eval z * v j) := CRGCollectedEquation.collected_identity P' Q' k v z
      _ = _ := by
        rw [show T = S.filter (fun q => ∃ j, b q j ≠ 0) from rfl,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro q _
        split_ifs with h
        · rfl
        · have hz : ∀ j, b q j = 0 := by simpa using h
          simp [hz]
  have hT : T.Nonempty := by
    by_contra h
    have hTe : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨z,hz⟩ := htop
    have hh := hid (fun j => if j = Fin.last n then 1 else 0) z
    apply hz
    simpa [hTe] using hh
  let E : EquationData n := ⟨T,hT,b,
    (by
      intro q hq
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
      rw [←hi]
      exact normalizedExponent_zero _),
    (by intro q hq; exact (Finset.mem_filter.mp hq).2)⟩
  refine ⟨E,?_,?_⟩
  · intro ν
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ν.property).1
    rw [←hi]
    simpa [Q',normalizedExponent] using natDegree_C_mul_X_pow_le (ω i.1 i.2) 1
  · intro f
    change (∀ z, _ = 0) ↔ (∀ z, _ = 0)
    simp_rw [hid]
    rfl

theorem fullCoefficient_isExponentialSum {n : ℕ} (a : Fin n → ℂ → ℂ)
    (ha : ∀ j, IsExponentialSum (a j)) :
    ∀ j, IsExponentialSum (fullCoefficient a j) := by
  intro j
  induction j using Fin.lastCases with
  | last =>
    refine ⟨1,fun _ => 1,fun _ => 0,?_⟩
    intro z
    simp [fullCoefficient]
  | cast j => simpa only [fullCoefficient,Fin.lastCases_castSucc] using ha j

/-- The original monic exponential-sum equation of manuscript Theorem 3.2.
Vertex geometry, group-specific ramification, the finite phase lists, the
explicit null set, and the growth conclusion are all retained. -/
theorem theorem_3_2 {n : ℕ} (a : Fin n → ℂ → ℂ)
    (ha : ∀ j, IsExponentialSum (a j)) :
    ∃ E : EquationData n, LinearExponents E ∧
      (∀ f : ℂ → ℂ, SolvesMonicEquation n a f ↔ E.Solves f) ∧
      ∃ D : GroupPhases E, ∀ f : ℂ → ℂ, Differentiable ℂ f →
        CRGOrder.FiniteOrder f → (¬∃ P : Polynomial ℂ, ∀ z, f z = P.eval z) →
        SolvesMonicEquation n a f → Theorem32Conclusion D f := by
  obtain ⟨E,hlinear,hE⟩ := exists_linear_equation_data (fullCoefficient a)
    (fullCoefficient_isExponentialSum a ha) ⟨0,by simp⟩
  have hsame (f : ℂ → ℂ) : SolvesMonicEquation n a f ↔ E.Solves f := by
    rw [←hE]
    constructor
    · exact full_equation a f
    · intro h z
      have hh := h z
      rw [Fin.sum_univ_castSucc] at hh
      simpa only [fullCoefficient_last,fullCoefficient_castSucc,Fin.val_last,
        Fin.val_castSucc,one_mul,add_comm] using hh
  obtain ⟨D,hD⟩ := theorem_3_2_collected E hlinear
  exact ⟨E,hlinear,hsame,D,fun f hf hfinite htrans heq =>
    hD f hf hfinite htrans ((hsame f).mp heq)⟩

#print axioms exists_group_phases
#print axioms exists_null_set_in_turn
#print axioms theorem_3_5_collected
#print axioms fullCoefficient_isExponentialPolynomial
#print axioms theorem_3_5
#print axioms linear_eval_on_ray
#print axioms vertexDirection_rayDominant
#print axioms theorem_3_2_collected
#print axioms exists_linear_equation_data
#print axioms fullCoefficient_isExponentialSum
#print axioms theorem_3_2
end CRGSection3Alignment
