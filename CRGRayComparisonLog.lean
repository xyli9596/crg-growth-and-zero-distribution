import CRGRayComparisonOrder
import WasowMatrixBounds
import WasowDiagonal

/-! Quantitative logarithmic comparison with the fixed dominant phase.
Both bounds use genuine inverse matrices; no cancellation assumption on the
scalar exponential sum is used, because the entire jet is compared first. -/
set_option autoImplicit false
noncomputable section
open Filter Matrix
open scoped Topology
namespace CRGRayComparisonLog
open CRGNormalFormGoal
variable {m : ℕ}

def exponentialVector (q : Fin m → ℂ) (c : Fin m → ℂ) : Fin m → ℂ :=
  fun i => Complex.exp (q i) * c i

theorem exponentialVector_bounds (q : Fin m → ℂ) (c : Fin m → ℂ)
    (j : Fin m) (hmax : ∀i, c i≠0 → (q i).re ≤ (q j).re) :
    Real.exp (q j).re * ‖c j‖ ≤ ‖exponentialVector q c‖ ∧
    ‖exponentialVector q c‖ ≤ Real.exp (q j).re * ‖c‖ := by
  constructor
  · simpa [exponentialVector, norm_mul, Complex.norm_exp] using
      norm_le_pi_norm (exponentialVector q c) j
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    by_cases hi : c i=0
    · simp only [exponentialVector,hi,mul_zero,norm_zero]
      positivity
    · simp only [exponentialVector,norm_mul,Complex.norm_exp]
      exact mul_le_mul (Real.exp_le_exp.mpr (hmax i hi)) (norm_le_pi_norm c i)
        (norm_nonneg _) (Real.exp_pos _).le

/-- Exponential upper and lower bounds with polynomial losses give the exact
logarithmic error needed by the ray lemma. -/
theorem log_of_polynomial_exponential_bounds
    (x q r B D K : ℝ) (hx : 0<x) (hr : 1≤r) (hB : 0<B) (hD : 0<D) (_hK : 0≤K)
    (hu : x ≤ B*r^K*Real.exp q) (hl : Real.exp q ≤ D*r^K*x) :
    |Real.log x-q| ≤ |Real.log B|+|Real.log D|+K*Real.log r := by
  have hrp : 0<r := zero_lt_one.trans_le hr
  have hpow : 0<r^K := Real.rpow_pos_of_pos hrp K
  have hlu := Real.log_le_log hx hu
  have hll := Real.log_le_log (Real.exp_pos q) hl
  rw [Real.log_mul (mul_pos hB hpow).ne' (Real.exp_pos q).ne',
    Real.log_mul hB.ne' hpow.ne', Real.log_rpow hrp, Real.log_exp] at hlu
  rw [Real.log_mul (mul_pos hD hpow).ne' hx.ne',
    Real.log_mul hD.ne' hpow.ne',Real.log_rpow hrp,Real.log_exp] at hll
  rw [abs_le]
  constructor
  · have := le_abs_self (Real.log D)
    have := abs_nonneg (Real.log B)
    linarith
  · have := le_abs_self (Real.log B)
    have := abs_nonneg (Real.log D)
    linarith

/-- Uniformly bounded corrections and polynomially bounded gauges preserve
precisely the exponential scale of the selected phase. -/
theorem represented_solution_exponential_bounds
    (T S U V : Matrix (Fin m) (Fin m) ℂ)
    (q c : Fin m → ℂ) (j : Fin m) (C B r K : ℝ)
    (hC : 0<C) (hB : 0<B) (hr : 0<r)
    (hST : S*T=1) (hVU : V*U=1)
    (hT : ∀v, ‖T.mulVec v‖ ≤ C*r^K*‖v‖)
    (hS : ∀v, ‖S.mulVec v‖ ≤ C*r^K*‖v‖)
    (hU : ∀v, ‖U.mulVec v‖ ≤ B*‖v‖)
    (hV : ∀v, ‖V.mulVec v‖ ≤ B*‖v‖)
    (hmax : ∀i,c i≠0→(q i).re≤(q j).re) :
    ‖T.mulVec (U.mulVec (exponentialVector q c))‖ ≤
      (C*B*‖c‖)*r^K*Real.exp (q j).re ∧
    Real.exp (q j).re*‖c j‖ ≤
      (B*C)*r^K*‖T.mulVec (U.mulVec (exponentialVector q c))‖ := by
  let v := exponentialVector q c
  have hp : 0≤r^K := (Real.rpow_pos_of_pos hr K).le
  obtain ⟨hlo,hup⟩ := exponentialVector_bounds q c j hmax
  constructor
  · calc
      ‖T.mulVec (U.mulVec v)‖ ≤ C*r^K*(B*‖v‖) :=
        (hT _).trans (mul_le_mul_of_nonneg_left (hU _) (by positivity))
      _ ≤ C*r^K*(B*(Real.exp (q j).re*‖c‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hup hB.le) (by positivity)
      _ = _ := by ring
  · have hinv : V.mulVec (S.mulVec (T.mulVec (U.mulVec v)))=v := by
      rw [Matrix.mulVec_mulVec (U.mulVec v) S T, hST, Matrix.one_mulVec,Matrix.mulVec_mulVec,hVU,
        Matrix.one_mulVec]
    calc
      Real.exp (q j).re*‖c j‖ ≤ ‖v‖ := hlo
      _ = ‖V.mulVec (S.mulVec (T.mulVec (U.mulVec v)))‖ := congrArg norm hinv.symm
      _ ≤ B*(C*r^K*‖T.mulVec (U.mulVec v)‖) :=
        (hV _).trans (mul_le_mul_of_nonneg_left (hS _) hB.le)
      _ = _ := by ring

/-- A scalar component polynomially comparable with its jet has the selected
phase plus a genuine O(log r) error. The constant vector and normalized
matrix are the ones furnished by the fundamental-solution construction. -/
theorem represented_scalar_log_comparison
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (p : ℕ) (hp : 0<p)
    (G : Fin m → Polynomial ℂ) (θ : ℝ) (ℓ : Fin p)
    (H : RayGaugeWitness A θ (fun i=>phaseOnRay p (G i) θ ℓ))
    (U : ℝ → Matrix (Fin m) (Fin m) ℂ) (hU : Tendsto U atTop (𝓝 1))
    (c : Fin m → ℂ) (hc : c≠0) (x : ℝ → Fin m → ℂ) (f : ℝ → ℂ)
    (hx : ∀ᶠr in atTop, x r = (H.T r).mulVec ((U r).mulVec
      (exponentialVector (fun i=>phaseOnRay p (G i) θ ℓ r) c)))
    (hf : ∀ᶠr in atTop, f r≠0)
    (D J : ℝ) (hD : 0<D) (hJ : 0≤J)
    (hjet : ∀ᶠr in atTop, ‖f r‖≤‖x r‖ ∧ ‖x r‖≤D*r^J*‖f r‖) :
    ∃j : Fin m, c j≠0 ∧ ∃M : ℝ, 0<M ∧ ∀ᶠr in atTop,
      |Real.log ‖f r‖-(phaseOnRay p (G j) θ ℓ r).re|≤M*Real.log r := by
  obtain ⟨j,hcj,hmax⟩ := CRGRayComparisonOrder.exists_dominant_phase p hp G θ ℓ c hc
  obtain ⟨B,hB,hbounds⟩ := WasowMatrixBounds.eventually_uniform_mulVec_bounds hU
  let Bu := H.C*B*‖c‖
  let Bl := B*H.C*D/‖c j‖
  let K := H.K+J
  have hC := H.C_pos
  have hcpos : 0<‖c‖ := norm_pos_iff.mpr hc
  have hcjpos : 0<‖c j‖ := norm_pos_iff.mpr hcj
  have hBu : 0<Bu := by dsimp [Bu]; positivity
  have hBl : 0<Bl := by dsimp [Bl]; positivity
  let M := |Real.log Bu|+|Real.log Bl|+K+1
  have hK : 0≤K := add_nonneg H.K_nonneg hJ
  refine ⟨j,hcj,M,by dsimp [M]; positivity,?_⟩
  have hlog : ∀ᶠr:ℝ in atTop, 1≤Real.log r :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hx,hf,hjet,hmax,hbounds,eventually_gt_atTop H.R,
    eventually_ge_atTop (1:ℝ),hlog] with r hxr hfr hjr hmr hbr hr hr1 hlr
  have hrp : 0<r := zero_lt_one.trans_le hr1
  obtain ⟨hu,hl⟩ := represented_solution_exponential_bounds
    (H.T r) (H.S r) (U r) ((U r)⁻¹)
    (fun i=>phaseOnRay p (G i) θ ℓ r) c j H.C B r H.K H.C_pos hB hrp
    (H.inverse_left r hr) hbr.1 (H.T_bound r hr) (H.S_bound r hr)
    hbr.2.2.1 hbr.2.2.2 hmr
  rw [←hxr] at hu hl
  have hpup : r^H.K ≤ r^K := Real.rpow_le_rpow_of_exponent_le hr1 (by dsimp [K]; linarith)
  have hu' : ‖f r‖ ≤ Bu*r^K*Real.exp (phaseOnRay p (G j) θ ℓ r).re :=
    hjr.1.trans (hu.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpup hBu.le) (Real.exp_pos _).le))
  have hl' : Real.exp (phaseOnRay p (G j) θ ℓ r).re ≤ Bl*r^K*‖f r‖ := by
    have hh := hl.trans (mul_le_mul_of_nonneg_left hjr.2 (by positivity : 0≤(B*H.C)*r^H.K))
    have he : (B*H.C)*r^H.K*(D*r^J*‖f r‖) =
        (Bl*r^K*‖f r‖)*‖c j‖ := by
      dsimp [Bl,K]
      rw [Real.rpow_add hrp]
      field_simp
    rw [he] at hh
    exact (mul_le_mul_iff_left₀ hcjpos).mp (by simpa only [mul_comm] using hh)
  have hh := log_of_polynomial_exponential_bounds ‖f r‖
    (phaseOnRay p (G j) θ ℓ r).re r Bu Bl K (norm_pos_iff.mpr hfr) hr1 hBu hBl hK hu' hl'
  refine hh.trans ?_
  have hc0 : 0≤|Real.log Bu|+|Real.log Bl| := by positivity
  have hh' := mul_le_mul_of_nonneg_left hlr hc0
  dsimp [M]
  nlinarith

#print axioms exponentialVector_bounds
#print axioms log_of_polynomial_exponential_bounds
#print axioms represented_solution_exponential_bounds
#print axioms represented_scalar_log_comparison
end CRGRayComparisonLog
