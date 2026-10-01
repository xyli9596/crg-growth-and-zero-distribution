import WasowRamifiedGauge

/-! Genuine rational evaluation commutes with finite algebraic operations on
a common tail. Poles of every intermediate expression are excluded by the
proved rational-denominator theorem, not by treating totalized evaluation as a homomorphism. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace WasowRationalEvaluation
open CRGNormalFormGoal

def value (θ r : ℝ) (f : RatFunc ℂ) : ℂ := RatFunc.eval (RingHom.id ℂ) (ray θ r) f

theorem eventually_pole_free (f : RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r : ℝ in atTop, f.denom.eval (ray θ r) ≠ 0 := by
  obtain ⟨_, _, R, hR, hb⟩ := WasowRational.exists_polynomial_part_tail f
  filter_upwards [eventually_gt_atTop R] with r hr
  exact (hb (ray θ r) (by rw [WasowRational.norm_ray θ (zero_le_one.trans (hR.trans hr.le))]; exact hr)).1

@[simp] theorem value_constant (θ r : ℝ) (c : ℂ) :
    value θ r (algebraMap ℂ (RatFunc ℂ) c) = c := by
  simp [value]

theorem eventually_value_add (f g : RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, value θ r (f + g) = value θ r f + value θ r g := by
  filter_upwards [eventually_pole_free f θ, eventually_pole_free g θ] with r hf hg
  exact RatFunc.eval_add (RingHom.id ℂ) (ray θ r) (by simpa using hf) (by simpa using hg)

theorem eventually_value_mul (f g : RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, value θ r (f * g) = value θ r f * value θ r g := by
  filter_upwards [eventually_pole_free f θ, eventually_pole_free g θ] with r hf hg
  exact RatFunc.eval_mul (RingHom.id ℂ) (ray θ r) (by simpa using hf) (by simpa using hg)

theorem eventually_value_sum {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, value θ r (∑ i ∈ s, f i) = ∑ i ∈ s, value θ r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [value]
  | @insert i s hi ih =>
    filter_upwards [ih, eventually_value_add (f i) (∑ j ∈ s, f j) θ] with r hr ha
    simpa only [Finset.sum_insert hi, hr] using ha

theorem eventually_value_neg (f : RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, value θ r (-f) = -value θ r f := by
  filter_upwards [eventually_value_mul (algebraMap ℂ (RatFunc ℂ) (-1)) f θ] with r hr
  rw [value_constant] at hr
  simpa only [map_neg, map_one, neg_one_mul] using hr

theorem eventually_value_sub (f g : RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, value θ r (f - g) = value θ r f - value θ r g := by
  filter_upwards [eventually_value_add f (-g) θ, eventually_value_neg g θ] with r ha hn
  simpa only [sub_eq_add_neg, hn] using ha

theorem eventually_value_inv (f : RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, value θ r f⁻¹ = (value θ r f)⁻¹ := by
  by_cases hf : f = 0
  · simp [hf, value]
  filter_upwards [eventually_value_mul f f⁻¹ θ] with r hr
  have hh : value θ r f * value θ r f⁻¹ = 1 := by
    rw [← hr, mul_inv_cancel₀ hf]
    simp [value]
  exact eq_inv_of_mul_eq_one_right hh

theorem eventually_value_pow (f : RatFunc ℂ) (θ : ℝ) (n : ℕ) :
    ∀ᶠ r in atTop, value θ r (f ^ n) = (value θ r f) ^ n := by
  induction n with
  | zero => simp [value]
  | succ n ih =>
    filter_upwards [ih, eventually_value_mul (f ^ n) f θ] with r hn hm
    simpa only [pow_succ, hn] using hm

theorem eventually_value_zpow (f : RatFunc ℂ) (θ : ℝ) (n : ℤ) :
    ∀ᶠ r in atTop, value θ r (f ^ n) = (value θ r f) ^ n := by
  cases n with
  | ofNat n =>
    change ∀ᶠ r in atTop, value θ r (f ^ (n : ℤ)) = (value θ r f) ^ (n : ℤ)
    simpa only [zpow_natCast] using eventually_value_pow f θ n
  | negSucc n =>
    filter_upwards [eventually_value_pow f θ (n + 1),
      eventually_value_inv (f ^ (n + 1)) θ] with r hn hi
    simpa only [zpow_negSucc, hn] using hi

/-- Finite matrix multiplication is evaluated exactly on a genuine tail. -/
theorem eventually_value_matrix_mul {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ) :
    ∀ᶠ r in atTop, (A * B).map (value θ r) = A.map (value θ r) * B.map (value θ r) := by
  have hs : ∀ᶠ r in atTop, ∀ i j, value θ r (∑ k, A i k * B k j) =
      ∑ k, value θ r (A i k * B k j) := by
    simp only [Filter.eventually_all]
    intro i j
    exact eventually_value_sum Finset.univ _ θ
  have hm : ∀ᶠ r in atTop, ∀ i j k,
      value θ r (A i k * B k j) = value θ r (A i k) * value θ r (B k j) := by
    simp only [Filter.eventually_all]
    intro i j k
    exact eventually_value_mul _ _ θ
  filter_upwards [hs, hm] with r hs hm
  ext i j
  exact (hs i j).trans (Finset.sum_congr rfl (fun k _ => hm i j k))

end WasowRationalEvaluation
#print axioms WasowRationalEvaluation.eventually_pole_free
#print axioms WasowRationalEvaluation.value_constant
#print axioms WasowRationalEvaluation.eventually_value_add
#print axioms WasowRationalEvaluation.eventually_value_mul
#print axioms WasowRationalEvaluation.eventually_value_sum
#print axioms WasowRationalEvaluation.eventually_value_neg
#print axioms WasowRationalEvaluation.eventually_value_sub
#print axioms WasowRationalEvaluation.eventually_value_inv
#print axioms WasowRationalEvaluation.eventually_value_pow
#print axioms WasowRationalEvaluation.eventually_value_zpow
#print axioms WasowRationalEvaluation.eventually_value_matrix_mul
