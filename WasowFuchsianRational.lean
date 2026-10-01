import WasowGaugeAssembly
import WasowRational

/-! Proper rational matrix coefficients have a genuine uniform Fuchsian
bound on every ray, with continuity and pole exclusion derived from their
actual numerators and denominators. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators Matrix.Norms.Operator
namespace WasowFuchsianRational
open CRGNormalFormGoal WasowRational
variable {m : ℕ}

/-- A convenient finite-entry upper bound for the actual operator norm. -/
theorem norm_le_sum_entries (M : Matrix (Fin m) (Fin m) ℂ) :
    ‖M‖ ≤ ∑ i, ∑ j, ‖M i j‖ := by
  have h : ‖M‖₊ ≤ ∑ i, ∑ j, ‖M i j‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.sup_le fun i _ => Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖₊) (fun _ _ => by positivity)
      (Finset.mem_univ i)
  have hh := (NNReal.coe_le_coe).mpr h
  simpa only [NNReal.coe_sum, coe_nnnorm] using hh

/-- Zero polynomial part is the rational, algebraic regular-singular condition
at infinity. It automatically supplies continuous actual ray coefficients,
a common pole-free tail, and a uniform `K/r` operator norm bound. -/
theorem exists_proper_ray_bound (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (hproper : ∀ i j, polynomialPart (A i j) = 0) :
    ∃ K : ℝ, 0 < K ∧ ∃ R : ℝ, 1 ≤ R ∧ ∀ θ : ℝ,
      ContinuousOn (coefficientOnRay A θ) (Ici R) ∧
      ∀ r : ℝ, R ≤ r →
        (∀ i j, (A i j).denom.eval (ray θ r) ≠ 0) ∧
        ‖coefficientOnRay A θ r‖ ≤ K / r := by
  classical
  choose C hC S hS ht using fun i j => exists_ray_polynomial_part (A i j)
  let R : ℝ := 1 + ∑ i, ∑ j, S i j
  let K : ℝ := 1 + ∑ i, ∑ j, C i j
  have hSn (i j : Fin m) : 0 ≤ S i j := zero_le_one.trans (hS i j)
  have hCn (i j : Fin m) : 0 ≤ C i j := (hC i j).le
  have hR : 1 ≤ R := by
    have hh : 0 ≤ ∑ i, ∑ j, S i j := Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hSn i j
    dsimp [R]; linarith
  have hK : 0 < K := by
    have hh : 0 ≤ ∑ i, ∑ j, C i j := Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hCn i j
    dsimp [K]; linarith
  have hSR (i j : Fin m) : S i j ≤ R := by
    have h1 := Finset.single_le_sum (s := Finset.univ) (f := fun j => S i j)
      (fun j _ => hSn i j) (Finset.mem_univ j)
    have h2 := Finset.single_le_sum (s := Finset.univ) (f := fun i => ∑ j, S i j)
      (fun i _ => Finset.sum_nonneg (fun j _ => hSn i j)) (Finset.mem_univ i)
    dsimp [R]; linarith
  have heq (θ r : ℝ) (hr : R ≤ r) (i j : Fin m) :
      coefficientOnRay A θ r i j = residualOnRay (A i j) θ r := by
    have hh := ((ht i j θ).2 r ((hSR i j).trans hr)).2.1
    simpa [coefficientOnRay, hproper i j] using hh
  refine ⟨K, hK, R, hR, fun θ => ⟨?_, ?_⟩⟩
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    apply (((ht i j θ).1).mono (fun _ hr => (hSR i j).trans hr)).congr
    intro r hr
    exact heq θ r hr i j
  · intro r hr
    have hrpos : 0 < r := zero_lt_one.trans_le (hR.trans hr)
    refine ⟨fun i j => ((ht i j θ).2 r ((hSR i j).trans hr)).1, ?_⟩
    calc
      ‖coefficientOnRay A θ r‖ ≤ ∑ i, ∑ j, ‖coefficientOnRay A θ r i j‖ :=
        norm_le_sum_entries _
      _ ≤ ∑ i, ∑ j, C i j / r := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        rw [heq θ r hr i j]
        exact ((ht i j θ).2 r ((hSR i j).trans hr)).2.2
      _ = (∑ i, ∑ j, C i j) / r := by simp_rw [← Finset.sum_div]
      _ ≤ K / r := by dsimp [K]; gcongr; linarith

#print axioms norm_le_sum_entries
#print axioms exists_proper_ray_bound
end WasowFuchsianRational
