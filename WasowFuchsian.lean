import WasowFuchsianFundamental
import WasowFuchsianBounds
import WasowFuchsianRational

/-! The general regular-singular analytic stopping branch. The fundamental
matrix and its inverse are constructed by actual ODE existence. No diagonal,
semisimple, constant-residue, or pre-existing gauge assumption is imposed. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Operator
namespace WasowFuchsian
open CRGNormalFormGoal
variable {m : ℕ}

/-- A continuous actual coefficient with a `K/r` bound has an exact zero-phase
gauge on the ray. Both the gauge and its inverse have polynomial growth. -/
theorem exists_fuchsian_rayGauge
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ a K : ℝ)
    (ha : 1 ≤ a) (hK : 0 ≤ K)
    (hcont : ContinuousOn (coefficientOnRay A θ) (Ici a))
    (hbound : ∀ r ≥ a, ‖coefficientOnRay A θ r‖ ≤ K / r)
    (hpoles : ∀ r ≥ a, ∀ i j, (A i j).denom.eval (ray θ r) ≠ 0) :
    Nonempty (RayGaugeWitness A θ (fun _ _ => 0)) := by
  obtain ⟨T, S, hT0, hS0, hTc, hSc, hTd, hSd⟩ :=
    WasowFuchsianFundamental.exists_matrix_solutions (coefficientOnRay A θ) hcont
  have hinv := WasowFuchsianBounds.matrix_solutions_inverse a
    (coefficientOnRay A θ) T S hT0 hS0 hTc hSc hTd hSd
  obtain ⟨C, hC, hb⟩ := WasowFuchsianBounds.matrix_solutions_bounds a (a + 1) K
    (coefficientOnRay A θ) T S (by linarith) (by linarith) hK hTd hSd
    (fun r hr => hbound r hr.le)
  refine ⟨{
    T := T
    S := S
    T' := fun r => coefficientOnRay A θ r * T r
    R := a + 1
    C := C
    K := K
    R_pos := by linarith
    C_pos := hC
    K_nonneg := hK
    pole_free := fun r hr => hpoles r (by linarith)
    T_derivative := ?_
    inverse_left := fun r hr => (hinv r (by linarith)).1
    inverse_right := fun r hr => (hinv r (by linarith)).2
    T_bound := ?_
    S_bound := ?_
    gauge_identity := ?_ }⟩
  · intro r hr i j
    exact ((WasowGaugeAssembly.entryMap i j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      r (hTd r (by linarith))
  · intro r hr x
    exact (Matrix.linfty_opNorm_mulVec (T r) x).trans
      (mul_le_mul_of_nonneg_right (hb r hr.le).1 (norm_nonneg x))
  · intro r hr x
    exact (Matrix.linfty_opNorm_mulVec (S r) x).trans
      (mul_le_mul_of_nonneg_right (hb r hr.le).2 (norm_nonneg x))
  · intro r _
    simp [Matrix.mul_assoc]

/-- For proper rational matrices the continuity, pole exclusion and inverse-
radius estimate are consequences, not additional analytic assumptions. -/
theorem exists_proper_rayGauge
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (hproper : ∀ i j, WasowRational.polynomialPart (A i j) = 0) (θ : ℝ) :
    Nonempty (RayGaugeWitness A θ (fun _ _ => 0)) := by
  obtain ⟨K, hK, a, ha, h⟩ := WasowFuchsianRational.exists_proper_ray_bound A hproper
  exact exists_fuchsian_rayGauge A θ a K ha hK.le (h θ).1
    (fun r hr => ((h θ).2 r hr).2) (fun r hr => ((h θ).2 r hr).1)

/-- The entire proper rational class has one fixed, zero phase family before
choosing the ray angle. This is the regular-singular stopping case of the
original normal-form conclusion, for arbitrary matrix size and multiplicities. -/
theorem proper_rational_normal_form
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (hproper : ∀ i j, WasowRational.polynomialPart (A i j) = 0) :
    ∃ p : ℕ, 0 < p ∧ ∃ G : Fin m → Polynomial ℂ,
      (∀ i, (G i).coeff 0 = 0) ∧
      ∀ θ : ℝ, ∃ ℓ : Fin p,
        Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (G i) θ ℓ)) := by
  refine ⟨1, zero_lt_one, fun _ => 0, by simp, fun θ => ⟨0, ?_⟩⟩
  have heq : (fun _ : Fin m => phaseOnRay 1 (0 : Polynomial ℂ) θ (0 : Fin 1)) =
      (fun _ _ => (0 : ℂ)) := by
    funext i r
    simp [phaseOnRay]
  rw [heq]
  exact exists_proper_rayGauge A hproper θ

#print axioms exists_fuchsian_rayGauge
#print axioms exists_proper_rayGauge
#print axioms proper_rational_normal_form
end WasowFuchsian
