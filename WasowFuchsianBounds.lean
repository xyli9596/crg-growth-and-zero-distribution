import WasowGaugeComposition
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Polynomial growth on a ray for actual solutions of a Fuchsian system.
The estimate uses the genuine logarithmic change of real time and Gronwall.
Existence of the solutions is handled in the separate ODE construction. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Operator
namespace WasowFuchsianBounds

/-- A derivative estimate K/r gives a polynomial bound in the original
radius. The starting radius lies strictly inside the differentiability tail. -/
theorem norm_le_polynomial_of_deriv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f f' : ℝ → E) (a R K : ℝ) (hR : 1 ≤ R) (haR : a < R) (hK : 0 ≤ K)
    (hd : ∀ r > a, HasDerivAt f (f' r) r)
    (hb : ∀ r > a, ‖f' r‖ ≤ K / r * ‖f r‖)
    {r : ℝ} (hr : R ≤ r) : ‖f r‖ ≤ ‖f R‖ * r ^ K := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hrp : 0 < r := hRp.trans_le hr
  have hl : Real.log R ≤ Real.log r := Real.log_le_log hRp hr
  have hex {t : ℝ} (ht : Real.log R ≤ t) : R ≤ Real.exp t := by
    calc R = Real.exp (Real.log R) := (Real.exp_log hRp).symm
         _ ≤ _ := Real.exp_le_exp.mpr ht
  have hder (t : ℝ) (ht : t ∈ Icc (Real.log R) (Real.log r)) :
      HasDerivAt (fun u => f (Real.exp u)) (Real.exp t • f' (Real.exp t)) t := by
    exact (hd _ (haR.trans_le (hex ht.1))).scomp t (Real.hasDerivAt_exp t)
  have hcont : ContinuousOn (fun t => f (Real.exp t)) (Icc (Real.log R) (Real.log r)) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (K := K) (ε := 0)
    (δ := ‖f R‖) hcont
    (fun t ht => (hder t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (by rw [Real.exp_log hRp]) (by
      intro t ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t), add_zero]
      calc
        _ ≤ Real.exp t * (K / Real.exp t * ‖f (Real.exp t)‖) :=
          mul_le_mul_of_nonneg_left (hb _ (haR.trans_le (hex ht.1))) (Real.exp_pos t).le
        _ = K * ‖f (Real.exp t)‖ := by field_simp)
    (Real.log r) ⟨hl, le_rfl⟩
  rw [Real.exp_log hrp, gronwallBound_ε0] at hg
  apply hg.trans
  rw [Real.rpow_def_of_pos hrp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR
  nlinarith

#print axioms norm_le_polynomial_of_deriv_bound

/-- The two independently constructed ODE solutions are genuine inverses.
Continuity at the initial endpoint supplies the boundary value. -/
theorem matrix_solutions_inverse {m : ℕ} (a : ℝ)
    (A T S : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (hT0 : T a = 1) (hS0 : S a = 1)
    (hTc : ContinuousOn T (Ici a)) (hSc : ContinuousOn S (Ici a))
    (hTd : ∀ r > a, HasDerivAt T (A r * T r) r)
    (hSd : ∀ r > a, HasDerivAt S (-(S r * A r)) r) :
    ∀ r ≥ a, S r * T r = 1 ∧ T r * S r = 1 := by
  have hd (r : ℝ) (hr : a < r) :
      HasDerivAt (fun t => S t * T t) 0 r := by
    have he : -(S r * A r) * T r + S r * (A r * T r) = 0 := by noncomm_ring
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    have hp := WasowRealization.matrix_product_hasDerivAt S T (-(S r * A r)) (A r * T r)
      (fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp (hSd r hr) i) j)
      (fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp (hTd r hr) i) j) i j
    simpa only [he, Matrix.zero_apply] using hp
  have he : EqOn (fun t => S t * T t) (fun _ => S (a + 1) * T (a + 1)) (Ioi a) := by
    intro r hr
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (f := fun t => S t * T t) (convex_Ioi a).isPreconnected
      (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hd r hr).deriv) hr (show a < a + 1 by linarith)
  have he' : EqOn (fun t => S t * T t) (fun _ => S (a + 1) * T (a + 1)) (Ici a) :=
    he.of_subset_closure (hSc.mul hTc) continuousOn_const Ioi_subset_Ici_self
      (by rw [closure_Ioi])
  have hinit := he' (show a ∈ Ici a from le_refl a)
  change S a * T a = S (a + 1) * T (a + 1) at hinit
  rw [hS0, hT0, one_mul] at hinit
  intro r hr
  have hleft : S r * T r = 1 := (he' hr).trans hinit.symm
  exact ⟨hleft, mul_eq_one_comm.mp hleft⟩

/-- Both actual fundamental matrices have a common polynomial bound. -/
theorem matrix_solutions_bounds {m : ℕ} (a R K : ℝ)
    (A T S : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (hR : 1 ≤ R) (haR : a < R) (hK : 0 ≤ K)
    (hTd : ∀ r > a, HasDerivAt T (A r * T r) r)
    (hSd : ∀ r > a, HasDerivAt S (-(S r * A r)) r)
    (hA : ∀ r > a, ‖A r‖ ≤ K / r) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ≥ R,
      ‖T r‖ ≤ C * r ^ K ∧ ‖S r‖ ≤ C * r ^ K := by
  let C := ‖T R‖ + ‖S R‖ + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro r hr
  have ht := norm_le_polynomial_of_deriv_bound T (fun t => A t * T t)
    a R K hR haR hK hTd (fun t ht => (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hA t ht) (norm_nonneg _))) hr
  have hs := norm_le_polynomial_of_deriv_bound S (fun t => -(S t * A t))
    a R K hR haR hK hSd (by
      intro t ht
      rw [norm_neg]
      calc
        _ ≤ ‖S t‖ * ‖A t‖ := norm_mul_le _ _
        _ ≤ ‖S t‖ * (K / t) := mul_le_mul_of_nonneg_left (hA t ht) (norm_nonneg _)
        _ = _ := mul_comm _ _) hr
  have hp : 0 ≤ r ^ K := Real.rpow_nonneg (by linarith) _
  constructor
  · exact ht.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [norm_nonneg (S R)]) hp)
  · exact hs.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [norm_nonneg (T R)]) hp)

#print axioms matrix_solutions_inverse
#print axioms matrix_solutions_bounds
end WasowFuchsianBounds
