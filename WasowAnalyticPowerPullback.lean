import WasowGlobalFormalRegular
import WasowRationalAtInfinity
import Mathlib.Analysis.Analytic.Basic

/-! Actual analytic power substitution with the prescribed formal coefficients.
The coefficient series is expanded by inserting zeros at the nonmultiples of
p. The proof reindexes a genuinely convergent sum; it does not choose a new
unrelated Taylor series or assume convergence of a formal gauge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology Matrix.Norms.Operator
open Filter
namespace WasowAnalyticPowerPullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The explicit multilinear series for substitution by a positive power. -/
def expandF (p : ℕ) (s : FormalMultilinearSeries ℂ ℂ E) :
    FormalMultilinearSeries ℂ ℂ E :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
    (if p ∣ n then s.coeff (n / p) else 0)

@[simp] theorem coeff_expandF (p : ℕ) (s : FormalMultilinearSeries ℂ ℂ E) (n : ℕ) :
    (expandF p s).coeff n = if p ∣ n then s.coeff (n / p) else 0 := by
  simp only [FormalMultilinearSeries.coeff, expandF,
    ContinuousMultilinearMap.mkPiRing_apply, Pi.one_apply, Finset.prod_const_one, one_smul]

/-- Sparse reindexing of the actual convergent power sum. -/
theorem hasSum_expandF (p : ℕ) (hp : 0 < p)
    (s : FormalMultilinearSeries ℂ ℂ E) (z : ℂ) (v : E)
    (h : HasSum (fun n => (z ^ p) ^ n • s.coeff n) v) :
    HasSum (fun n => z ^ n • (expandF p s).coeff n) v := by
  let f : ℕ → E := fun n => z ^ n • (expandF p s).coeff n
  have hi : Function.Injective (fun n : ℕ => p * n) := mul_right_injective₀ hp.ne'
  have hz : ∀ n, n ∉ Set.range (fun k : ℕ => p * k) → f n = 0 := by
    intro n hn
    have hnd : ¬p ∣ n := by
      rintro ⟨k, hk⟩
      exact hn ⟨k, hk.symm⟩
    simp [f, hnd]
  apply (hi.hasSum_iff hz).mp
  simpa [f, Function.comp_def, Nat.mul_div_cancel_left _ hp, pow_mul] using h

/-- The original analytic expansion pulls back to precisely the sparse series. -/
theorem hasFPowerSeriesAt_pow {c : ℂ → E}
    {s : FormalMultilinearSeries ℂ ℂ E} (hc : HasFPowerSeriesAt c s 0)
    (p : ℕ) (hp : 0 < p) :
    HasFPowerSeriesAt (fun z => c (z ^ p)) (expandF p s) 0 := by
  rw [hasFPowerSeriesAt_iff] at hc ⊢
  have ht : Tendsto (fun z : ℂ => z ^ p) (𝓝 0) (𝓝 0) := by
    have ht := (continuous_pow p).tendsto (0 : ℂ)
    rw [zero_pow hp.ne'] at ht
    exact ht
  filter_upwards [ht.eventually hc] with z hz
  simp only [zero_add] at hz ⊢
  exact hasSum_expandF p hp s z _ hz

/-- In the scalar case this is exactly mathlib's formal `PowerSeries.expand`. -/
theorem coeff_expandF_scalar (p : ℕ) (hp : 0 < p)
    (s : FormalMultilinearSeries ℂ ℂ ℂ) (A : PowerSeries ℂ)
    (hc : ∀ n, s.coeff n = PowerSeries.coeff n A) (n : ℕ) :
    (expandF p s).coeff n = PowerSeries.coeff n (PowerSeries.expand p hp.ne' A) := by
  rw [coeff_expandF, PowerSeries.coeff_expand]
  split_ifs <;> simp_all

/-- The explicit coefficient shift for multiplication by `k * z^e`. -/
def monomialF (k : ℂ) (e : ℕ) (s : FormalMultilinearSeries ℂ ℂ E) :
    FormalMultilinearSeries ℂ ℂ E :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
    (if e ≤ n then k • s.coeff (n - e) else 0)

@[simp] theorem coeff_monomialF (k : ℂ) (e : ℕ)
    (s : FormalMultilinearSeries ℂ ℂ E) (n : ℕ) :
    (monomialF k e s).coeff n = if e ≤ n then k • s.coeff (n - e) else 0 := by
  simp only [FormalMultilinearSeries.coeff, monomialF,
    ContinuousMultilinearMap.mkPiRing_apply, Pi.one_apply, Finset.prod_const_one, one_smul]

/-- Multiplying a convergent power sum introduces the actual coefficient shift. -/
theorem hasSum_monomialF (k : ℂ) (e : ℕ)
    (s : FormalMultilinearSeries ℂ ℂ E) (z : ℂ) (v : E)
    (h : HasSum (fun n => z ^ n • s.coeff n) v) :
    HasSum (fun n => z ^ n • (monomialF k e s).coeff n) ((k * z ^ e) • v) := by
  let f : ℕ → E := fun n => z ^ n • (monomialF k e s).coeff n
  have hi : Function.Injective (fun n : ℕ => e + n) := by
    intro i j hij
    exact Nat.add_left_cancel hij
  have hz : ∀ n, n ∉ Set.range (fun j : ℕ => e + j) → f n = 0 := by
    intro n hn
    have hne : ¬e ≤ n := by
      intro hle
      exact hn ⟨n - e, Nat.add_sub_of_le hle⟩
    simp [f, hne]
  apply (hi.hasSum_iff hz).mp
  convert h.const_smul (k * z ^ e) using 1
  funext n
  simp only [Function.comp_apply, f, coeff_monomialF, Nat.le_add_right, if_pos,
    Nat.add_sub_cancel_left, pow_add, smul_smul]
  congr 1
  ring

/-- Analytic monomial multiplication, with its specified Taylor coefficients. -/
theorem hasFPowerSeriesAt_monomial {c : ℂ → E}
    {s : FormalMultilinearSeries ℂ ℂ E} (hc : HasFPowerSeriesAt c s 0)
    (k : ℂ) (e : ℕ) :
    HasFPowerSeriesAt (fun z => (k * z ^ e) • c z) (monomialF k e s) 0 := by
  rw [hasFPowerSeriesAt_iff] at hc ⊢
  filter_upwards [hc] with z hz
  simp only [zero_add] at hz ⊢
  exact hasSum_monomialF k e s z _ hz

section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For matrix coefficients it equals the existing entrywise expansion used by
all the formal ramification operations, including repeated eigenvalue blocks. -/
theorem coeff_expandF_matrix (p : ℕ)
    (s : FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ))
    (A : PowerSeries (Matrix ι ι ℂ))
    (hc : ∀ n, s.coeff n = PowerSeries.coeff n A) (n : ℕ) :
    (expandF p s).coeff n = PowerSeries.coeff n
      (WasowGlobalFormalRegular.expandSeries p A) := by
  rw [coeff_expandF]
  simp only [WasowGlobalFormalRegular.expandSeries, PowerSeries.coeff_mk]
  split_ifs
  · exact hc _
  · rfl

/-- The actual pullback of the given analytic germ is paired with the already
specified formal ramification, without any new Taylor-coefficient assumption. -/
theorem analytic_formal_power_pullback {c : ℂ → Matrix ι ι ℂ}
    {s : FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ)}
    (hc : HasFPowerSeriesAt c s 0) (A : PowerSeries (Matrix ι ι ℂ))
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n A) (p : ℕ) (hp : 0 < p) :
    HasFPowerSeriesAt (fun z => c (z ^ p)) (expandF p s) 0 ∧
    (∀ n, (expandF p s).coeff n = PowerSeries.coeff n
      (WasowGlobalFormalRegular.expandSeries p A)) ∧
    (∀ i j, WasowPowerSeries.entry (WasowGlobalFormalRegular.expandSeries p A) i j =
      PowerSeries.expand p hp.ne' (WasowPowerSeries.entry A i j)) := by
  exact ⟨hasFPowerSeriesAt_pow hc p hp, coeff_expandF_matrix p s A hcoeff,
    WasowGlobalFormalRegular.entry_expandSeries p hp A⟩

/-- The clear-pole numerator after ramification is the concrete scalar and
monomial multiple of the original, fixed expanded formal coefficient. -/
theorem coeff_monomialF_matrix (k : ℂ) (e : ℕ)
    (s : FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ))
    (A : PowerSeries (Matrix ι ι ℂ))
    (hc : ∀ n, s.coeff n = PowerSeries.coeff n A) (n : ℕ) :
    (monomialF k e s).coeff n =
      PowerSeries.coeff n (k • ((PowerSeries.X ^ e) * A)) := by
  rw [coeff_monomialF, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_mul']
  split_ifs
  · rw [hc]
  · exact (smul_zero k).symm

/-- Actual analytic ramification together with scalar Jacobian and pole clearing.
This retains the originally specified series `A` in the exact resulting series. -/
theorem analytic_formal_cleared_pullback {c : ℂ → Matrix ι ι ℂ}
    {s : FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ)}
    (hc : HasFPowerSeriesAt c s 0) (A : PowerSeries (Matrix ι ι ℂ))
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n A)
    (p : ℕ) (hp : 0 < p) (k : ℂ) (e : ℕ) :
    HasFPowerSeriesAt (fun z => (k * z ^ e) • c (z ^ p))
      (monomialF k e (expandF p s)) 0 ∧
    (∀ n, (monomialF k e (expandF p s)).coeff n = PowerSeries.coeff n
      (k • (PowerSeries.X ^ e * WasowGlobalFormalRegular.expandSeries p A))) := by
  exact ⟨hasFPowerSeriesAt_monomial (hasFPowerSeriesAt_pow hc p hp) k e,
    coeff_monomialF_matrix k e _ _ (coeff_expandF_matrix p s A hcoeff)⟩

end Matrix

#print axioms coeff_expandF
#print axioms hasSum_expandF
#print axioms hasFPowerSeriesAt_pow
#print axioms coeff_expandF_scalar
#print axioms coeff_expandF_matrix
#print axioms analytic_formal_power_pullback
#print axioms coeff_monomialF
#print axioms hasSum_monomialF
#print axioms hasFPowerSeriesAt_monomial
#print axioms coeff_monomialF_matrix
#print axioms analytic_formal_cleared_pullback
end WasowAnalyticPowerPullback
