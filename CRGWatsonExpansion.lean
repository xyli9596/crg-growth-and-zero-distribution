import CRGWatsonDecay
import CRGWatsonComplexMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace CRGWatson
open CRGPolynomialKernel

def monomialIntegral (m j : ℕ) (s : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ j * Complex.exp (-s * (t : ℂ) ^ m)

def gammaMomentTerm (m j : ℕ) (s : ℂ) : ℂ :=
  s ^ (-((((j : ℝ) + 1) / (m : ℝ)) : ℂ)) *
    ((1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ)) : ℝ)

def taylorCoefficient (w : ℝ → ℂ) (j : ℕ) : ℂ :=
  iteratedDeriv j w 0 / (j.factorial : ℂ)

def decayingSum (w : ℝ → ℂ) (m N : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, taylorCoefficient w j * gammaMomentTerm m j s

/-- Integrating the Taylor polynomial produces the actual finite moments. -/
theorem integral_taylorPolynomial (w : ℝ → ℂ) (m N : ℕ) (s : ℂ) :
    laplaceIntegral (taylorPolynomial w N) (fun t => (t : ℂ) ^ m) (-s) =
      ∑ j ∈ Finset.range N, taylorCoefficient w j * monomialIntegral m j s := by
  unfold laplaceIntegral monomialIntegral
  have heq : (fun t : ℝ => taylorPolynomial w N t * Complex.exp (-s * (t : ℂ) ^ m)) =
      (fun t : ℝ => ∑ j ∈ Finset.range N,
        taylorCoefficient w j * ((t : ℂ) ^ j * Complex.exp (-s * (t : ℂ) ^ m))) := by
    funext t
    simp only [taylorPolynomial, Finset.sum_mul, Complex.real_smul, taylorCoefficient,
      Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul]
  · intro j _
    apply Continuous.intervalIntegrable
    fun_prop

/-- The full decaying endpoint expansion, with explicit all-orders Taylor and
exponential-tail errors and principal complex powers. -/
theorem analytic_decaying_expansion_bound {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (hwa : AnalyticAt ℝ w 0)
    {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 < s.re →
      ‖laplaceIntegral w (fun t => (t : ℂ) ^ m) (-s) - decayingSum w m N s‖ ≤
        C * (s.re ^ (-((N : ℝ) + 1) / (m : ℝ)) * (1 / (m : ℝ)) *
          Real.Gamma (((N : ℝ) + 1) / (m : ℝ))) +
        Real.exp (-s.re / 2) * ∑ j ∈ Finset.range N,
          ‖taylorCoefficient w j‖ * ((s.re / 2) ^ (-((j : ℝ) + 1) / (m : ℝ)) *
            (1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ))) := by
  obtain ⟨C, hC, hR⟩ := analytic_decay_remainder_bound hw hwa hm N
  refine ⟨C, hC, fun s hs => ?_⟩
  have hTaylor : ‖laplaceIntegral w (fun t => (t : ℂ) ^ m) (-s) -
      laplaceIntegral (taylorPolynomial w N) (fun t => (t : ℂ) ^ m) (-s)‖ ≤
      C * (s.re ^ (-((N : ℝ) + 1) / (m : ℝ)) * (1 / (m : ℝ)) *
        Real.Gamma (((N : ℝ) + 1) / (m : ℝ))) := by
    rw [← integral_taylor_remainder hw m N (-s)]
    simpa only [Complex.neg_re, neg_neg] using hR (-s) (by simpa using neg_neg_of_pos hs)
  have hMoments : ‖laplaceIntegral (taylorPolynomial w N) (fun t => (t : ℂ) ^ m) (-s) -
      decayingSum w m N s‖ ≤
      Real.exp (-s.re / 2) * ∑ j ∈ Finset.range N,
        ‖taylorCoefficient w j‖ * ((s.re / 2) ^ (-((j : ℝ) + 1) / (m : ℝ)) *
          (1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ))) := by
    rw [integral_taylorPolynomial, decayingSum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j ∈ Finset.range N, ‖taylorCoefficient w j * monomialIntegral m j s -
          taylorCoefficient w j * gammaMomentTerm m j s‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range N, Real.exp (-s.re / 2) *
          (‖taylorCoefficient w j‖ * ((s.re / 2) ^ (-((j : ℝ) + 1) / (m : ℝ)) *
            (1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ)))) := by
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, norm_mul]
        have h := mul_le_mul_of_nonneg_left (truncated_complexPowerMoment_bound hm j hs)
          (norm_nonneg (taylorCoefficient w j))
        simpa only [monomialIntegral, gammaMomentTerm, mul_assoc, mul_left_comm] using h
      _ = _ := by rw [Finset.mul_sum]
  calc
    _ ≤ ‖laplaceIntegral w (fun t => (t : ℂ) ^ m) (-s) -
          laplaceIntegral (taylorPolynomial w N) (fun t => (t : ℂ) ^ m) (-s)‖ +
        ‖laplaceIntegral (taylorPolynomial w N) (fun t => (t : ℂ) ^ m) (-s) -
          decayingSum w m N s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add hTaylor hMoments

/-- Every decreasing exponential is smaller than every prescribed real power
far out, with explicit quantified uniformity. -/
theorem exponential_flat_bound {a : ℝ} (ha : 0 < a) (r : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∃ R : ℝ, 1 ≤ R ∧ ∀ x : ℝ, R ≤ x →
      Real.exp (-a * x) ≤ M * x ^ r := by
  obtain ⟨M, hM, hbound⟩ := (isLittleO_exp_neg_mul_rpow_atTop ha r).isBigO.exists_pos
  obtain ⟨R, hR⟩ := eventually_atTop.mp hbound.bound
  refine ⟨M, hM, max R 1, le_max_right _ _, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := le_trans zero_le_one ((le_max_right R 1).trans hx)
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.rpow_nonneg hx0 r)] using hR x ((le_max_left R 1).trans hx)

/-- Watson's decaying endpoint expansion of every order is uniform on every
closed cone. This is the full error estimate in manuscript equation (5.8). -/
theorem analytic_decaying_uniform_expansion {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc 0 1)) (hwa : AnalyticAt ℝ w 0)
    {m : ℕ} (hm : 0 < m) (N : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ R : ℝ, 1 ≤ R ∧ ∀ s : ℂ,
      R ≤ ‖s‖ → c * ‖s‖ ≤ s.re →
      ‖laplaceIntegral w (fun t => (t : ℂ) ^ m) (-s) - decayingSum w m N s‖ ≤
        B * ‖s‖ ^ (-((N : ℝ) + 1) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let e : ℝ := -((N : ℝ) + 1) / (m : ℝ)
  have he : e ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by linarith [Nat.cast_nonneg (α := ℝ) N]) hmR.le
  have hG : 0 ≤ Real.Gamma (((N : ℝ) + 1) / (m : ℝ)) :=
    Real.Gamma_nonneg_of_nonneg (by positivity)
  obtain ⟨C, hC, hbound⟩ := analytic_decaying_expansion_bound hw hwa hm N
  let D : ℝ := ∑ j ∈ Finset.range N,
    ‖taylorCoefficient w j‖ * ((c / 2) ^ (-((j : ℝ) + 1) / (m : ℝ)) *
      (1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ)))
  have hD : 0 ≤ D := by
    apply Finset.sum_nonneg
    intro j _
    have hGamma : 0 ≤ Real.Gamma (((j : ℝ) + 1) / (m : ℝ)) :=
      Real.Gamma_nonneg_of_nonneg (by positivity)
    positivity
  obtain ⟨M, hM, R, hR, hflat⟩ := exponential_flat_bound (show 0 < c / 2 by positivity) e
  let B1 : ℝ := C * (c ^ e * (1 / (m : ℝ)) *
    Real.Gamma (((N : ℝ) + 1) / (m : ℝ)))
  refine ⟨B1 + M * D, by dsimp [B1]; positivity, R, hR, ?_⟩
  intro s hsR hscone
  have hsnorm : 1 ≤ ‖s‖ := hR.trans hsR
  have hsnorm0 : 0 < ‖s‖ := lt_of_lt_of_le zero_lt_one hsnorm
  have hs : 0 < s.re := lt_of_lt_of_le (mul_pos hc hsnorm0) hscone
  have hfirst : C * (s.re ^ e * (1 / (m : ℝ)) *
      Real.Gamma (((N : ℝ) + 1) / (m : ℝ))) ≤ B1 * ‖s‖ ^ e := by
    have hpow : s.re ^ e ≤ (c * ‖s‖) ^ e :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hc hsnorm0) hscone he
    calc
      _ ≤ C * ((c * ‖s‖) ^ e * (1 / (m : ℝ)) *
          Real.Gamma (((N : ℝ) + 1) / (m : ℝ))) := by gcongr
      _ = _ := by rw [Real.mul_rpow hc.le (norm_nonneg s)]; dsimp [B1]; ring
  have hsum : (∑ j ∈ Finset.range N,
      ‖taylorCoefficient w j‖ * ((s.re / 2) ^ (-((j : ℝ) + 1) / (m : ℝ)) *
        (1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ)))) ≤ D := by
    apply Finset.sum_le_sum
    intro j _
    have hj : -((j : ℝ) + 1) / (m : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (by linarith [Nat.cast_nonneg (α := ℝ) j]) hmR.le
    have hhalf : c / 2 ≤ s.re / 2 := by nlinarith
    have hpow := Real.rpow_le_rpow_of_nonpos (show 0 < c / 2 by positivity) hhalf hj
    have hGamma : 0 ≤ Real.Gamma (((j : ℝ) + 1) / (m : ℝ)) :=
      Real.Gamma_nonneg_of_nonneg (by positivity)
    gcongr
  have hExp : Real.exp (-s.re / 2) ≤ Real.exp (-(c / 2) * ‖s‖) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hsecond : Real.exp (-s.re / 2) *
      (∑ j ∈ Finset.range N,
        ‖taylorCoefficient w j‖ * ((s.re / 2) ^ (-((j : ℝ) + 1) / (m : ℝ)) *
          (1 / (m : ℝ)) * Real.Gamma (((j : ℝ) + 1) / (m : ℝ)))) ≤
      (M * D) * ‖s‖ ^ e := by
    calc
      _ ≤ Real.exp (-s.re / 2) * D := mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)
      _ ≤ Real.exp (-(c / 2) * ‖s‖) * D := mul_le_mul_of_nonneg_right hExp hD
      _ ≤ (M * ‖s‖ ^ e) * D := mul_le_mul_of_nonneg_right (hflat ‖s‖ hsR) hD
      _ = _ := by ring
  calc
    _ ≤ _ := hbound s hs
    _ ≤ B1 * ‖s‖ ^ e + (M * D) * ‖s‖ ^ e := add_le_add hfirst hsecond
    _ = _ := by ring

#print axioms integral_taylorPolynomial
#print axioms analytic_decaying_expansion_bound
#print axioms analytic_decaying_uniform_expansion
end CRGWatson
