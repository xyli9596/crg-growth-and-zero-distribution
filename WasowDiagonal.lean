import WasowRational
import WasowScalarGauge
import WasowPolynomialPhase

/-! Exact ray normal forms for diagonal rational systems. The polynomial phases
are chosen from the rational coefficients, and the gauges are constructed by
integrating their proper remainders. This is a proved special case, not a proof
of the general matrix normal-form goal. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
open CRGNormalFormGoal WasowRational WasowScalarGauge
namespace WasowDiagonal

theorem diagonal_mulVec_norm_le {m : ℕ} (d x : Fin m → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hd : ∀ i, ‖d i‖ ≤ B) :
    ‖(Matrix.diagonal d).mulVec x‖ ≤ B * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (norm_nonneg x))).mpr
  intro i
  rw [Matrix.mulVec_diagonal, norm_mul]
  exact mul_le_mul (hd i) (norm_le_pi_norm x i) (norm_nonneg _) hB

theorem coefficientOnRay_diagonal {m : ℕ} (a : Fin m → RatFunc ℂ) (θ r : ℝ) :
    coefficientOnRay (Matrix.diagonal a) θ r =
      Matrix.diagonal (fun i => Complex.exp ((θ : ℂ) * Complex.I) *
        RatFunc.eval (RingHom.id ℂ) (ray θ r) (a i)) := by
  classical
  ext i j
  by_cases h : i = j <;> simp [coefficientOnRay, h]

/-- The full witness is constructed whenever the chosen phases have the
polynomial-part derivatives. No gauge or inverse bounds are assumed. -/
theorem exists_diagonal_rayGauge {m : ℕ} (a : Fin m → RatFunc ℂ)
    (θ : ℝ) (q : Fin m → ℝ → ℂ)
    (hq : ∀ i r, HasDerivAt (q i)
      (Complex.exp ((θ : ℂ) * Complex.I) * (polynomialPart (a i)).eval (ray θ r)) r) :
    Nonempty (RayGaugeWitness (Matrix.diagonal a) θ q) := by
  classical
  choose C hC R hR hp using fun i => exists_ray_polynomial_part (a i)
  let S : ℝ := 1 + ∑ i, R i
  let K : ℝ := ∑ i, C i
  have hRS (i : Fin m) : R i ≤ S := by
    have hh : R i ≤ ∑ j, R j := Finset.single_le_sum (fun j _ => (by linarith [hR j]))
      (Finset.mem_univ i)
    dsimp [S]
    linarith
  have hS : 1 ≤ S := by
    have hh : 0 ≤ ∑ j, R j := Finset.sum_nonneg (fun j _ => (by linarith [hR j]))
    dsimp [S]
    linarith
  have hCK (i : Fin m) : C i ≤ K :=
    Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => (hC i).le)
  let b : Fin m → ℝ → ℂ := fun i => residualOnRay (a i) θ
  have hb (i : Fin m) : ContinuousOn (b i) (Ici S) :=
    ((hp i θ).1).mono (Ici_subset_Ici.mpr (hRS i))
  have hbound (i : Fin m) (r : ℝ) (hr : S ≤ r) : ‖b i r‖ ≤ C i / r :=
    ((hp i θ).2 r ((hRS i).trans hr)).2.2
  have hg (i : Fin m) (r : ℝ) (hr : S ≤ r) :
      ‖gauge (b i) S r‖ ≤ r ^ K ∧ ‖inverseGauge (b i) S r‖ ≤ r ^ K := by
    have hh := gauge_norm_bounds hS (hC i).le (hb i) (hbound i) hr
    have hpow : r ^ C i ≤ r ^ K := Real.rpow_le_rpow_of_exponent_le (hS.trans hr) (hCK i)
    exact ⟨hh.1.trans hpow, hh.2.trans hpow⟩
  refine ⟨{
    T := fun r => Matrix.diagonal (fun i => gauge (b i) S r)
    S := fun r => Matrix.diagonal (fun i => inverseGauge (b i) S r)
    T' := fun r => Matrix.diagonal (fun i => b i r * gauge (b i) S r)
    R := S, C := 1, K := K
    R_pos := by linarith
    C_pos := by norm_num
    K_nonneg := hK
    pole_free := ?_
    T_derivative := ?_
    inverse_left := ?_
    inverse_right := ?_
    T_bound := ?_
    S_bound := ?_
    gauge_identity := ?_ }⟩
  · intro r hr i j
    by_cases hij : i = j
    · subst j
      simpa using ((hp i θ).2 r ((hRS i).trans hr.le)).1
    · simp [hij, RatFunc.denom_zero]
  · intro r hr i j
    by_cases hij : i = j
    · subst j
      simpa using gauge_hasDerivAt (hb i) hr.le
    · simpa [Matrix.diagonal_apply, hij] using hasDerivAt_const r (0 : ℂ)
  · intro r hr
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact (gauge_inverse (b i) S r).1
  · intro r hr
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact (gauge_inverse (b i) S r).2
  · intro r hr x
    simpa only [one_mul] using diagonal_mulVec_norm_le _ x (Real.rpow_nonneg (by linarith) _)
      (fun i => (hg i r hr.le).1)
  · intro r hr x
    simpa only [one_mul] using diagonal_mulVec_norm_le _ x (Real.rpow_nonneg (by linarith) _)
      (fun i => (hg i r hr.le).2)
  · intro r hr
    rw [coefficientOnRay_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub]
    congr 1
    funext i
    rw [(hq i r).deriv]
    have hid := ((hp i θ).2 r ((hRS i).trans hr.le)).2.1
    have hinv := (gauge_inverse (b i) S r).1
    change inverseGauge (b i) S r * _ * gauge (b i) S r -
      inverseGauge (b i) S r * (b i r * gauge (b i) S r) = _
    calc
      _ = (inverseGauge (b i) S r * gauge (b i) S r) *
        (Complex.exp ((θ : ℂ) * Complex.I) * RatFunc.eval (RingHom.id ℂ) (ray θ r) (a i)
          - b i r) := by ring
      _ = _ := by rw [hinv, one_mul]; exact (sub_eq_iff_eq_add.mp hid).symm ▸ by ring

/-- The original normal-form conclusion for every diagonal rational system.
The phases are selected before the angle and have zero constant term. -/
theorem diagonal_rational_normal_form {m : ℕ} (a : Fin m → RatFunc ℂ) :
    ∃ (p : ℕ), 0 < p ∧ ∃ G : Fin m → Polynomial ℂ,
      (∀ i, (G i).coeff 0 = 0) ∧
      ∀ θ : ℝ, ∃ ℓ : Fin p,
        Nonempty (RayGaugeWitness (Matrix.diagonal a) θ
          (fun i => phaseOnRay p (G i) θ ℓ)) := by
  refine ⟨1, by norm_num, fun i => WasowPolynomialPhase.zeroConstantPrimitive (polynomialPart (a i)),
    fun i => WasowPolynomialPhase.zeroConstantPrimitive_coeff_zero _, fun θ => ⟨0, ?_⟩⟩
  exact exists_diagonal_rayGauge a θ _
    (fun i r => WasowPolynomialPhase.phase_hasDerivAt (polynomialPart (a i)) θ r)

/-- Every one-dimensional rational system satisfies the unmodified normal-form
conclusion, without any assumption on its coefficient. -/
theorem scalar_rational_normal_form (A : Matrix (Fin 1) (Fin 1) (RatFunc ℂ)) :
    ∃ (p : ℕ), 0 < p ∧ ∃ G : Fin 1 → Polynomial ℂ,
      (∀ i, (G i).coeff 0 = 0) ∧
      ∀ θ : ℝ, ∃ ℓ : Fin p,
        Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (G i) θ ℓ)) := by
  have hA : Matrix.diagonal (fun i => A i i) = A := by
    ext i j
    have hij : i = j := Subsingleton.elim i j
    subst j
    simp
  simpa only [hA] using diagonal_rational_normal_form (fun i => A i i)

#print axioms diagonal_mulVec_norm_le
#print axioms coefficientOnRay_diagonal
#print axioms exists_diagonal_rayGauge
#print axioms diagonal_rational_normal_form
#print axioms scalar_rational_normal_form
end WasowDiagonal
