import WasowGaugeComposition

/-! Actual analytic closure under integer diagonal shearing on every complex
ray. The transformed coefficient is the existing rational shearing expression;
its evaluated identity, actual derivative, inverse and growth are proved. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators Matrix.Norms.Operator
namespace WasowShearingGauge
open CRGNormalFormGoal WasowShearing WasowGaugeComposition WasowRationalEvaluation
variable {m : ℕ}

/-- The genuine rational coefficient already used in the formal shear step. -/
def shearedCoefficient (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (k : Fin m → ℤ) :=
  inverseShear k (RatFunc.X : RatFunc ℂ) * A * shear k (RatFunc.X : RatFunc ℂ) -
    inverseShear k (RatFunc.X : RatFunc ℂ) * derivativeShear k (RatFunc.X : RatFunc ℂ)

/-- Integer powers on an arbitrary ray have their actual complex-direction derivative. -/
theorem shear_ray_hasDerivAt (k : Fin m → ℤ) (θ : ℝ) {r : ℝ} (hr : 0 < r) (i j : Fin m) :
    HasDerivAt (fun t => shear k (ray θ t) i j)
      ((Complex.exp ((θ : ℂ) * Complex.I) • derivativeShear k (ray θ r)) i j) r := by
  have hz : ray θ r ≠ 0 := norm_pos_iff.mp (by rw [WasowRational.norm_ray θ hr.le]; exact hr)
  have hRay : HasDerivAt (ray θ) (Complex.exp ((θ : ℂ) * Complex.I)) r := by
    convert! ((hasDerivAt_id r).ofReal_comp).mul_const
      (Complex.exp ((θ : ℂ) * Complex.I)) using 1
    simp
  by_cases hij : i = j
  · subst j
    have hh := (hasDerivAt_zpow (k i) (ray θ r) (Or.inl hz)).scomp r hRay
    simp only [shear, derivativeShear, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
    convert! hh using 1
  · simpa [shear, derivativeShear, Matrix.diagonal_apply, hij] using hasDerivAt_const r (0 : ℂ)

/-- Both integer shearing factors have a common polynomial bound on every ray. -/
theorem shear_ray_bounds (k : Fin m → ℤ) (θ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r → ∀ x : Fin m → ℂ,
      ‖(shear k (ray θ r)).mulVec x‖ ≤ r ^ K * ‖x‖ ∧
      ‖(inverseShear k (ray θ r)).mulVec x‖ ≤ r ^ K * ‖x‖ := by
  let K : ℝ := ∑ i, |(k i : ℝ)|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hki (i : Fin m) : |(k i : ℝ)| ≤ K :=
    Finset.single_le_sum (fun j _ => abs_nonneg (k j : ℝ)) (Finset.mem_univ i)
  refine ⟨K, hK, fun r hr x => ?_⟩
  have hb (w : Fin m → ℤ) (hw : ∀ i, (w i : ℝ) ≤ K) :
      ‖(shear w (ray θ r)).mulVec x‖ ≤ r ^ K * ‖x‖ := by
    apply WasowDiagonal.diagonal_mulVec_norm_le _ x (Real.rpow_nonneg (zero_le_one.trans hr) _)
    intro i
    rw [norm_zpow, WasowRational.norm_ray θ (zero_le_one.trans hr), ← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le hr (hw i)
  exact ⟨hb k (fun i => (le_abs_self _).trans (hki i)),
    hb (fun i => -k i) (fun i => by simpa using (neg_le_abs (k i : ℝ)).trans (hki i))⟩

/-- The rational shear itself evaluates to the actual complex diagonal powers. -/
theorem eventually_value_shear (k : Fin m → ℤ) (θ : ℝ) :
    ∀ᶠ r in atTop, (shear k (RatFunc.X : RatFunc ℂ)).map (value θ r) = shear k (ray θ r) := by
  have hh : ∀ᶠ r in atTop, ∀ i, value θ r ((RatFunc.X : RatFunc ℂ) ^ k i) = (ray θ r) ^ k i := by
    simp only [Filter.eventually_all]
    intro i
    simpa only [value, RatFunc.eval_X] using eventually_value_zpow (RatFunc.X : RatFunc ℂ) θ (k i)
  filter_upwards [hh] with r hr
  ext i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.map_apply, shear, Matrix.diagonal_apply_eq] using hr i
  · simp [shear, hij, value]

/-- The rational derivative matrix evaluates to its actual complex derivative. -/
theorem eventually_value_derivativeShear (k : Fin m → ℤ) (θ : ℝ) :
    ∀ᶠ r in atTop, (derivativeShear k (RatFunc.X : RatFunc ℂ)).map (value θ r) =
      derivativeShear k (ray θ r) := by
  have hc (r : ℝ) (n : ℤ) : value θ r (n : RatFunc ℂ) = (n : ℂ) := by
    have he : (n : RatFunc ℂ) = algebraMap ℂ (RatFunc ℂ) (n : ℂ) := by simp
    rw [he, value_constant]
  have hh : ∀ᶠ r in atTop, ∀ i,
      value θ r ((k i : RatFunc ℂ) * RatFunc.X ^ (k i - 1)) =
        (k i : ℂ) * (ray θ r) ^ (k i - 1) := by
    simp only [Filter.eventually_all]
    intro i
    filter_upwards [eventually_value_mul (k i : RatFunc ℂ) (RatFunc.X ^ (k i - 1)) θ,
      eventually_value_zpow (RatFunc.X : RatFunc ℂ) θ (k i - 1)] with r hm hp
    rw [hm, hc, hp]
    simp [value]
  filter_upwards [hh] with r hr
  ext i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.map_apply, derivativeShear, Matrix.diagonal_apply_eq] using hr i
  · simp [derivativeShear, hij, value]

/-- The full rational expression, including its derivative correction, has the
actual shearing value on a genuine tail. -/
theorem eventually_sheared_value (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (k : Fin m → ℤ) (θ : ℝ) :
    ∀ᶠ r in atTop, (shearedCoefficient A k).map (value θ r) =
      inverseShear k (ray θ r) * A.map (value θ r) * shear k (ray θ r) -
        inverseShear k (ray θ r) * derivativeShear k (ray θ r) := by
  have hsub : ∀ᶠ r in atTop, ∀ i j,
      value θ r ((shearedCoefficient A k) i j) =
        value θ r ((inverseShear k (RatFunc.X : RatFunc ℂ) * A * shear k (RatFunc.X : RatFunc ℂ)) i j) -
          value θ r ((inverseShear k (RatFunc.X : RatFunc ℂ) * derivativeShear k (RatFunc.X : RatFunc ℂ)) i j) := by
    simp only [Filter.eventually_all]
    intro i j
    exact eventually_value_sub _ _ θ
  filter_upwards [hsub,
    eventually_value_matrix_mul (inverseShear k (RatFunc.X : RatFunc ℂ) * A) (shear k (RatFunc.X : RatFunc ℂ)) θ,
    eventually_value_matrix_mul (inverseShear k (RatFunc.X : RatFunc ℂ)) A θ,
    eventually_value_matrix_mul (inverseShear k (RatFunc.X : RatFunc ℂ)) (derivativeShear k (RatFunc.X : RatFunc ℂ)) θ,
    eventually_value_shear k θ, eventually_value_shear (fun i => -k i) θ,
    eventually_value_derivativeShear k θ] with r hs h₁ h₂ h₃ ht hi hd
  have he : (shearedCoefficient A k).map (value θ r) =
      (inverseShear k (RatFunc.X : RatFunc ℂ) * A * shear k (RatFunc.X : RatFunc ℂ)).map (value θ r) -
        (inverseShear k (RatFunc.X : RatFunc ℂ) * derivativeShear k (RatFunc.X : RatFunc ℂ)).map (value θ r) := by
    ext i j
    exact hs i j
  rw [he, h₁, h₂, h₃, ht, hd]
  change (shear (fun i => -k i) RatFunc.X).map (value θ r) * _ * _ -
    (shear (fun i => -k i) RatFunc.X).map (value θ r) * _ = _
  rw [hi]
  rfl

/-- Construct the actual integer shearing change for the actual rational
transformed coefficient on an arbitrary complex ray. -/
theorem shearing_change (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (k : Fin m → ℤ) (θ : ℝ) :
    Nonempty (RayGaugeChange A (shearedCoefficient A k) θ) := by
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (eventually_sheared_value A k θ)
  obtain ⟨K, hK, hb⟩ := shear_ray_bounds k θ
  have hrpos {r : ℝ} (hr : max 1 R₀ < r) : 0 < r := zero_lt_one.trans ((le_max_left _ _).trans_lt hr)
  have hz {r : ℝ} (hr : max 1 R₀ < r) : ray θ r ≠ 0 :=
    norm_pos_iff.mp (by rw [WasowRational.norm_ray θ (hrpos hr).le]; exact hrpos hr)
  refine ⟨{
    H := fun r => shear k (ray θ r)
    S := fun r => inverseShear k (ray θ r)
    H' := fun r => Complex.exp ((θ : ℂ) * Complex.I) • derivativeShear k (ray θ r)
    R := max 1 R₀, C := 1, K := K
    R_pos := zero_lt_one.trans_le (le_max_left _ _)
    C_pos := zero_lt_one, K_nonneg := hK
    derivative := fun r hr i j => shear_ray_hasDerivAt k θ (hrpos hr) i j
    inverse_left := fun _ hr => inverseShear_mul_shear k (hz hr)
    inverse_right := fun _ hr => shear_mul_inverseShear k (hz hr)
    H_bound := ?_
    S_bound := ?_
    identity := ?_ }⟩
  · intro r hr x
    simpa only [one_mul] using (hb r ((le_max_left _ _).trans hr.le) x).1
  · intro r hr x
    simpa only [one_mul] using (hb r ((le_max_left _ _).trans hr.le) x).2
  · intro r hr
    have hc (M : Matrix (Fin m) (Fin m) (RatFunc ℂ)) :
        coefficientOnRay M θ r = Complex.exp ((θ : ℂ) * Complex.I) • M.map (value θ r) := rfl
    rw [hc (shearedCoefficient A k), hR₀ r ((le_max_right _ _).trans hr.le)]
    rw [smul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, shear_mul_inverseShear k (hz hr), Matrix.one_mul]
    rw [hc A, Matrix.smul_mul]
    simp only [← Matrix.mul_assoc, shear_mul_inverseShear k (hz hr), Matrix.one_mul]
    abel

/-- Pull back an exact normal form through the integer rational shear.
The phase functions are unchanged, and both actual inverse bounds persist. -/
theorem pullback_shearing_rayGauge (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (k : Fin m → ℤ) (θ : ℝ) (Q : Fin m → ℝ → ℂ)
    (W : RayGaugeWitness (shearedCoefficient A k) θ Q) :
    Nonempty (RayGaugeWitness A θ Q) := by
  obtain ⟨F⟩ := shearing_change A k θ
  exact pullback_rayGauge A _ θ Q F W

end WasowShearingGauge
#print axioms WasowShearingGauge.shear_ray_hasDerivAt
#print axioms WasowShearingGauge.shear_ray_bounds
#print axioms WasowShearingGauge.eventually_value_shear
#print axioms WasowShearingGauge.eventually_value_derivativeShear
#print axioms WasowShearingGauge.eventually_sheared_value
#print axioms WasowShearingGauge.shearing_change
#print axioms WasowShearingGauge.pullback_shearing_rayGauge
