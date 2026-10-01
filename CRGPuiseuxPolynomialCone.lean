import CRGExponentialDominance
import CRGIndicatorAlternatives
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Topology.Order.Compact

/-! The strict leading sign gives a genuine polynomial phase cone on
each ray, together with escape to infinity. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial
open scoped Topology BigOperators
namespace CRGPuiseuxPolynomialCone
open CRGNormalFormGoal CRGPhaseDirections CRGPhaseAsymptotics CRGExponentialDominance

def coefficientBound (Q : Polynomial ℂ) : ℝ :=
  (∑k∈Finset.range (Q.natDegree+1),‖Q.coeff k‖)+1

theorem coefficientBound_pos (Q : Polynomial ℂ) : 0<coefficientBound Q := by
  have hs : 0≤∑k∈Finset.range (Q.natDegree+1),‖Q.coeff k‖ :=
    Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  dsimp [coefficientBound]
  linarith

theorem norm_eval_bound (Q : Polynomial ℂ) (z : ℂ) (hz : 1≤‖z‖) :
    ‖Q.eval z‖≤coefficientBound Q*‖z‖^Q.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    ‖∑k∈Finset.range (Q.natDegree+1),Q.coeff k*z^k‖
        ≤∑k∈Finset.range (Q.natDegree+1),‖Q.coeff k*z^k‖ := norm_sum_le _ _
    _ ≤∑k∈Finset.range (Q.natDegree+1),‖Q.coeff k‖*‖z‖^Q.natDegree := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [norm_mul,norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by
        have := Finset.mem_range.mp hk;omega)) (norm_nonneg _)
    _ =(∑k∈Finset.range (Q.natDegree+1),‖Q.coeff k‖)*‖z‖^Q.natDegree := by rw [Finset.sum_mul]
    _ ≤coefficientBound Q*‖z‖^Q.natDegree := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
      dsimp [coefficientBound]
      linarith

theorem norm_ray {θ r : ℝ} (hr : 0≤r) : ‖ray θ r‖=r := by
  simp [ray,norm_mul,Complex.norm_exp,Complex.mul_re,Real.norm_of_nonneg hr]

theorem positive_ray_cone (Q : Polynomial ℂ) (θ : ℝ)
    (hd : 0<Q.natDegree) (hL : 0<leadingReal Q.leadingCoeff Q.natDegree θ) :
    ∃c : ℝ,0<c ∧
      (∀ᶠr : ℝ in atTop,c*‖Q.eval (ray θ r)‖≤(Q.eval (ray θ r)).re) ∧
      Tendsto (fun r : ℝ=>‖Q.eval (ray θ r)‖) atTop atTop := by
  let L := leadingReal Q.leadingCoeff Q.natDegree θ
  have ht : Tendsto (fun r : ℝ=>(Q.eval (ray θ r)).re/r^Q.natDegree) atTop (𝓝 L) := by
    simpa only [ray,leading_coefficient_on_ray,L] using
      polynomial_normalized_limit Q (Complex.exp ((θ:ℂ)*Complex.I))
        (by rw [leading_coefficient_on_ray];exact hL.ne')
  have hlower : ∀ᶠr : ℝ in atTop,L/2*r^Q.natDegree≤(Q.eval (ray θ r)).re := by
    filter_upwards [ht.eventually (lt_mem_nhds (by dsimp [L];linarith : L/2<L)),
      eventually_gt_atTop (0:ℝ)] with r hr hrp
    exact (le_div_iff₀ (pow_pos hrp _)).mp hr.le
  let c := L/(2*coefficientBound Q)
  have hc : 0<c := div_pos hL (mul_pos (by norm_num) (coefficientBound_pos Q))
  refine ⟨c,hc,?_,?_⟩
  · filter_upwards [hlower,eventually_ge_atTop (1:ℝ)] with r hr hr1
    have hb := norm_eval_bound Q (ray θ r) (by rw [norm_ray (by linarith)];exact hr1)
    rw [norm_ray (by linarith)] at hb
    calc
      c*‖Q.eval (ray θ r)‖≤c*(coefficientBound Q*r^Q.natDegree) :=
        mul_le_mul_of_nonneg_left hb hc.le
      _ = L/2*r^Q.natDegree := by
        dsimp [c]
        field_simp [(coefficientBound_pos Q).ne']
      _ ≤(Q.eval (ray θ r)).re := hr
  · apply tendsto_atTop_mono' atTop
    · filter_upwards [hlower] with r hr
      exact hr.trans (Complex.re_le_norm _)
    · exact (tendsto_pow_atTop hd.ne').const_mul_atTop (by dsimp [L];linarith : 0<L/2)

theorem negative_ray_cone (Q : Polynomial ℂ) (θ : ℝ)
    (hd : 0<Q.natDegree) (hL : leadingReal Q.leadingCoeff Q.natDegree θ<0) :
    ∃c : ℝ,0<c ∧
      (∀ᶠr : ℝ in atTop,c*‖Q.eval (ray θ r)‖≤-(Q.eval (ray θ r)).re) ∧
      Tendsto (fun r : ℝ=>‖Q.eval (ray θ r)‖) atTop atTop := by
  have hneg : 0<leadingReal (-Q).leadingCoeff (-Q).natDegree θ := by
    simpa only [Polynomial.leadingCoeff_neg,Polynomial.natDegree_neg,leadingReal,
      neg_mul,Complex.neg_re] using neg_pos.mpr hL
  simpa only [Polynomial.natDegree_neg,Polynomial.eval_neg,norm_neg,Complex.neg_re] using
    positive_ray_cone (-Q) θ (by simpa only [Polynomial.natDegree_neg] using hd) hneg

theorem real_eval_lower_bound (Q : Polynomial ℂ) (θ r : ℝ) (hr : 1≤r) :
    leadingReal Q.leadingCoeff Q.natDegree θ*r^Q.natDegree-
      coefficientBound Q.eraseLead*r^(Q.natDegree-1)≤(Q.eval (ray θ r)).re := by
  have hb := norm_eval_bound Q.eraseLead (ray θ r) (by rw [norm_ray (by linarith)];exact hr)
  rw [norm_ray (by linarith)] at hb
  have hb' : ‖Q.eraseLead.eval (ray θ r)‖≤coefficientBound Q.eraseLead*r^(Q.natDegree-1) :=
    hb.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hr Q.eraseLead_natDegree_le) (coefficientBound_pos _).le)
  have heval := congrArg (fun P : Polynomial ℂ=>P.eval (ray θ r))
    (Q.eraseLead_add_C_mul_X_pow)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X] at heval
  have hlead : (Q.leadingCoeff*(ray θ r)^Q.natDegree).re=
      leadingReal Q.leadingCoeff Q.natDegree θ*r^Q.natDegree := by
    have he : Q.leadingCoeff*(ray θ r)^Q.natDegree=
        ((r^Q.natDegree:ℝ):ℂ)*(Q.leadingCoeff*(Complex.exp ((θ:ℂ)*Complex.I))^Q.natDegree) := by
      simp only [ray,mul_pow,Complex.ofReal_pow]
      ring
    rw [he]
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [leading_coefficient_on_ray,mul_comm]
  have hlow := neg_le_neg hb'
  have hre : -‖Q.eraseLead.eval (ray θ r)‖≤(Q.eraseLead.eval (ray θ r)).re :=
    neg_le_of_abs_le (Complex.abs_re_le_norm _)
  have hh := congrArg Complex.re heval
  simp only [Complex.add_re,hlead] at hh
  linarith

/-- On every compact angular subinterval with positive leading sign one
single ray tail lies in the right half-plane, uniformly in direction. -/
theorem uniform_positive_tail (Q : Polynomial ℂ) (hd : 0<Q.natDegree) (a b : ℝ)
    (hL : ∀θ∈uIcc a b,0<leadingReal Q.leadingCoeff Q.natDegree θ) :
    ∃R : ℝ,1≤R ∧ ∀θ∈uIcc a b,∀r>R,0<(Q.eval (ray θ r)).re := by
  obtain ⟨θ₀,hθ₀,hmin⟩ := isCompact_uIcc.exists_isMinOn
    (f:=leadingReal Q.leadingCoeff Q.natDegree) (nonempty_uIcc (a:=a) (b:=b))
    (CRGIndicatorAlternatives.continuous_leadingReal Q.leadingCoeff Q.natDegree).continuousOn
  let L := leadingReal Q.leadingCoeff Q.natDegree θ₀
  let B := coefficientBound Q.eraseLead
  have hLp : 0<L := hL θ₀ hθ₀
  let R := max 1 (2*B/L)
  refine ⟨R,le_max_left _ _,?_⟩
  intro θ hθ r hr
  have hr1 : 1≤r := (le_max_left _ _).trans hr.le
  have hrp : 0<r := zero_lt_one.trans_le hr1
  have hlarge : 2*B/L<r := (le_max_right _ _).trans_lt hr
  have hBr : B<L*r := by
    have hh := (div_lt_iff₀ hLp).mp hlarge
    have hB : 0<B := coefficientBound_pos Q.eraseLead
    nlinarith
  have hminθ : L≤leadingReal Q.leadingCoeff Q.natDegree θ := hmin hθ
  have hpow : r^Q.natDegree=r^(Q.natDegree-1)*r := by rw [←pow_succ];congr 1;omega
  have hpos : 0<L*r^Q.natDegree-B*r^(Q.natDegree-1) := by
    rw [hpow]
    nlinarith [pow_pos hrp (Q.natDegree-1)]
  have hb := real_eval_lower_bound Q θ r hr1
  have hh := mul_le_mul_of_nonneg_right hminθ (pow_nonneg hrp.le Q.natDegree)
  dsimp [B] at hpos
  linarith

#print axioms norm_eval_bound
#print axioms positive_ray_cone
#print axioms negative_ray_cone
#print axioms real_eval_lower_bound
#print axioms uniform_positive_tail
end CRGPuiseuxPolynomialCone
