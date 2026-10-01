import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Checked auxiliary steps for the CRG ray argument

This file does NOT state or prove the entire-function CRG theorem.
Gundersen's theorem, rational formal reduction, the concrete mixed integral
operator and its differentiation, Phragmen--Lindelof, and subharmonic compactness
are not formalized here. The hypotheses below are explicit; none is an axiom.
-/

open scoped BigOperators Topology
open Filter MeasureTheory

namespace CRGRay

/-- The exact quotient identity obtained from the normalized original ODE. -/
theorem residual_identity {ι : Type*} (s : Finset ι)
    (u v : ℂ) (w h : ι → ℂ)
    (heq : v + ∑ i ∈ s, w i * h i = 0) :
    v / u = - ∑ i ∈ s, w i * (h i / u) := by
  have hv : v = - ∑ i ∈ s, w i * h i := eq_neg_of_add_eq_zero_left heq
  rw [hv, neg_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mul_div_assoc]

/-- Dividing by a nonzero value of f yields an exact reduced equation. -/
theorem exact_reduced_equation (u v : ℂ) (hu : u ≠ 0) :
    v - (v / u) * u = 0 := by
  rw [div_mul_cancel₀ v hu, sub_self]

/-- Finite sums preserve exponential suppression when the quotient terms
    are bounded by the common scalar B. The hypotheses are pointwise. -/
theorem residual_bound {ι : Type*} (s : Finset ι)
    (epsilon : ℂ) (phase term : ι → ℂ) (b B : ℝ)
    (heq : epsilon = - ∑ i ∈ s, Complex.exp (phase i) * term i)
    (hphase : ∀ i ∈ s, (phase i).re ≤ -b)
    (hterm : ∀ i ∈ s, ‖term i‖ ≤ B) :
    ‖epsilon‖ ≤ (s.card : ℝ) * (Real.exp (-b) * B) := by
  rw [heq, norm_neg]
  calc
    ‖∑ i ∈ s, Complex.exp (phase i) * term i‖
        ≤ ∑ i ∈ s, ‖Complex.exp (phase i) * term i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, Real.exp (-b) * B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_exp]
      exact mul_le_mul (Real.exp_le_exp.mpr (hphase i hi)) (hterm i hi)
        (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by simp

/-- Polynomial weights cannot prevent exponential decay. -/
theorem polynomial_exp_decay (K c C : ℝ) (hc : 0 < c) :
    Tendsto (fun r : ℝ => C * (r ^ K * Real.exp (-c * r)))
      atTop (𝓝 0) := by
  simpa using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero K c hc).const_mul C

/-- The precise logarithmic loss in transferring a polynomially comparable
    jet norm back to the scalar modulus. -/
theorem logarithmic_comparison {a b r K : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hab : a ≤ b) (hba : b ≤ r ^ K * a) :
    0 ≤ Real.log b - Real.log a ∧
    Real.log b - Real.log a ≤ K * Real.log r := by
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log ha hab)
  · have hlog := Real.log_le_log (ha.trans_le hab) hba
    rw [Real.log_mul (Real.rpow_pos_of_pos hr K).ne' ha.ne', Real.log_rpow hr] at hlog
    linarith

/-- Monotonicity of the real phase in the chosen integration direction
    bounds the actual complex exponential kernel by one. -/
theorem exponential_kernel_bound (a b : ℂ) (h : a.re ≤ b.re) :
    ‖Complex.exp (a - b)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  simpa using Real.exp_le_one_iff.mpr (sub_nonpos.mpr h)

/-- A concrete integral-kernel estimate, valid on any restricted measure
    (hence both forward and backward intervals). Row sums of the matrix
    give the scalar majorant b * M when this is applied componentwise.
    Measurability and integrability of the input are explicit hypotheses. -/
theorem integral_kernel_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (k h : α → ℂ) (b : α → ℝ) (M : ℝ)
    (hb : Integrable b μ) (hh : AEStronglyMeasurable (fun s => k s * h s) μ)
    (hk : ∀ᵐ s ∂μ, ‖k s‖ ≤ 1)
    (hbound : ∀ᵐ s ∂μ, ‖h s‖ ≤ b s * M) :
    Integrable (fun s => k s * h s) μ ∧
    ‖∫ s, k s * h s ∂μ‖ ≤ (∫ s, b s ∂μ) * M := by
  have hmajor : ∀ᵐ s ∂μ, ‖k s * h s‖ ≤ b s * M := by
    filter_upwards [hk, hbound] with s hks hhs
    calc
      ‖k s * h s‖ = ‖k s‖ * ‖h s‖ := norm_mul _ _
      _ ≤ 1 * ‖h s‖ := mul_le_mul_of_nonneg_right hks (norm_nonneg _)
      _ ≤ b s * M := by simpa using hhs
  have hbi : Integrable (fun s => b s * M) μ := hb.mul_const M
  refine ⟨hbi.mono' hh hmajor, ?_⟩
  calc
    ‖∫ s, k s * h s ∂μ‖ ≤ ∫ s, b s * M ∂μ := norm_integral_le_of_norm_le hbi hmajor
    _ = _ := integral_mul_const M b

/-- The dominated-convergence step for a varying kernel. An interval cutoff
    can be included in k; measurability, the uniform bound and the pointwise
    kernel limit must still be established for that particular cutoff. -/
theorem vanishing_kernel_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (k : ℝ → α → ℂ) (h : α → ℂ) (b : α → ℝ)
    (hb : Integrable b μ)
    (hmeas : ∀ᶠ t in (atTop : Filter ℝ), AEStronglyMeasurable (fun s => k t s * h s) μ)
    (hbound : ∀ᶠ t in (atTop : Filter ℝ), ∀ᵐ s ∂μ, ‖k t s * h s‖ ≤ b s)
    (hzero : ∀ᵐ s ∂μ, Tendsto (fun t => k t s) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ s, k t s * h s ∂μ) atTop (𝓝 0) := by
  have hpoint : ∀ᵐ s ∂μ, Tendsto (fun t => k t s * h s) atTop (𝓝 (0 : ℂ)) := by
    filter_upwards [hzero] with s hs
    simpa using hs.mul_const (h s)
  simpa using tendsto_integral_filter_of_dominated_convergence b hmeas hbound hb hpoint

/-- A selected phase with nonzero normalized leading term cannot have degree
    above a two-sided logarithmic growth bound. This uses real exponents and
    excludes both positive and negative leading coefficients. -/
theorem phase_degree_le {u : ℝ → ℝ} {s d a C : ℝ}
    (hbound : ∀ᶠ r in atTop, |u r| ≤ C * r ^ s)
    (hlead : Tendsto (fun r => u r / r ^ d) atTop (𝓝 a))
    (ha : a ≠ 0) : d ≤ s := by
  by_contra h
  have hsd : s < d := lt_of_not_ge h
  have hzero : Tendsto (fun r : ℝ => r ^ (s - d)) atTop (𝓝 0) := by
    have hexp : s - d = -(d - s) := by ring
    simpa only [hexp] using tendsto_rpow_neg_atTop (sub_pos.mpr hsd)
  have hupper : Tendsto (fun r : ℝ => C * r ^ (s - d)) atTop (𝓝 0) := by
    simpa using hzero.const_mul C
  have hquot : ∀ᶠ r : ℝ in atTop, |u r / r ^ d| ≤ C * r ^ (s - d) := by
    filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with r hr hrpos
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hrpos d),
      Real.rpow_sub hrpos, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hr (Real.rpow_pos_of_pos hrpos d).le
  have habs : Tendsto (fun r : ℝ => |u r / r ^ d|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => abs_nonneg _) hquot
  have hlim : |a| = 0 := tendsto_nhds_unique hlead.abs habs
  exact ha (abs_eq_zero.mp hlim)

/-- Using bounds for every s > rho excludes every selected degree d > rho. -/
theorem phase_degree_le_order {u : ℝ → ℝ} {rho d a : ℝ}
    (hbound : ∀ s > rho, ∃ C : ℝ, ∀ᶠ r in atTop, |u r| ≤ C * r ^ s)
    (hlead : Tendsto (fun r => u r / r ^ d) atTop (𝓝 a))
    (ha : a ≠ 0) : d ≤ rho := by
  by_contra h
  have hd : rho < d := lt_of_not_ge h
  obtain ⟨s, hrs, hsd⟩ := exists_between hd
  obtain ⟨C, hC⟩ := hbound s hrs
  exact (not_le.mpr hsd) (phase_degree_le hC hlead ha)

/-- The exact companion residual changes only its last row and first column.
    The input is a derivative vector with the original residual already known. -/
theorem companion_correction {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (X dX : Fin (m + 1) → ℂ) (epsilon : ℂ)
    (hderiv : dX = A.mulVec X +
      Pi.single (Fin.last m) (epsilon * X 0)) :
    dX = (A + Matrix.of (fun i j =>
      if i = Fin.last m ∧ j = 0 then epsilon else 0)).mulVec X := by
  rw [hderiv, Matrix.add_mulVec]
  congr 1
  ext i
  by_cases hi : i = Fin.last m
  · subst i
    simp [Matrix.mulVec, dotProduct, Matrix.of_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.of_apply, hi]

/-- Once a concrete integral map has been shown to act on a complete normed
    space with this difference bound, Banach supplies its unique fixed point.
    The estimate itself for the mixed forward/backward integrals is NOT assumed
    to have been formally established by this theorem. -/
theorem fixed_point_of_norm_bound {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E]
    (F : E → E) (a : NNReal) (ha : a < 1)
    (hF : ∀ u v, ‖F u - F v‖ ≤ (a : ℝ) * ‖u - v‖) :
    ∃! u, F u = u := by
  have hcontract : ContractingWith a F := ⟨ha, LipschitzWith.of_dist_le_mul
    (by simpa only [dist_eq_norm] using hF)⟩
  refine ⟨ContractingWith.fixedPoint F hcontract, hcontract.fixedPoint_isFixedPt, ?_⟩
  intro u hu
  exact hcontract.fixedPoint_unique hu

/-- A.e. pointwise convergence identifies any limit in measure. -/
theorem measure_limit_unique {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (u : ℕ → α → ℝ) (v H : α → ℝ)
    (hmeasure : TendstoInMeasure μ u atTop v)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (H x))) :
    v =ᵐ[μ] H := by
  obtain ⟨ns, hns, hsub⟩ := hmeasure.exists_seq_tendsto_ae
  filter_upwards [hsub, hae] with x hx hy
  exact tendsto_nhds_unique hx (hy.comp hns.tendsto_atTop)

/-- In particular a pointwise a.e. limit identifies every L1 limit.
    The existence of L1 subsequences from subharmonic compactness is outside
    this formalization. -/
theorem l1_limit_unique {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (u : ℕ → α → ℝ) (v H : α → ℝ)
    (hu : ∀ n, AEStronglyMeasurable (u n) μ)
    (hv : AEStronglyMeasurable v μ)
    (hl1 : Tendsto (fun n => eLpNorm (u n - v) 1 μ) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (H x))) :
    v =ᵐ[μ] H := by
  exact measure_limit_unique μ u v H
    (tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (by norm_num) (by norm_num) hu hv hl1)
    hae

#print axioms residual_identity
#print axioms exact_reduced_equation
#print axioms residual_bound
#print axioms polynomial_exp_decay
#print axioms logarithmic_comparison
#print axioms exponential_kernel_bound
#print axioms integral_kernel_bound
#print axioms vanishing_kernel_integral
#print axioms phase_degree_le
#print axioms phase_degree_le_order
#print axioms companion_correction
#print axioms fixed_point_of_norm_bound
#print axioms measure_limit_unique
#print axioms l1_limit_unique

end CRGRay
