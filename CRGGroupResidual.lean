import CRGExponentialDominance
import CRGCompanionComparison
import WasowRational

/-! Exact dominant-group residual and its exponential estimate, before
specializing the finite group values to polynomial differential operators. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial Matrix
open scoped Topology BigOperators
namespace CRGGroupResidual
open CRGNormalFormGoal

theorem normalized_group_equation {ι:Type*} [Fintype ι]
    (Q L:ι→ℂ) (j:ι) (h:∑i,Complex.exp (Q i)*L i=0) :
    ∑i,Complex.exp (Q i-Q j)*L i=0 := by
  calc
    _ = Complex.exp (-Q j)*(∑i,Complex.exp (Q i)*L i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [sub_eq_add_neg,Complex.exp_add]
      ring
    _ = 0 := by rw [h,mul_zero]

def epsilon {ι:Type*} (L:ι→ℂ) (j:ι) (d f:ℂ) : ℂ := L j/(d*f)

theorem epsilon_identity {ι:Type*} [Fintype ι] [DecidableEq ι]
    (Q L:ι→ℂ) (j:ι) (d f:ℂ) (h:∑i,Complex.exp (Q i)*L i=0) :
    epsilon L j d f = -∑i∈Finset.univ.erase j,
      Complex.exp (Q i-Q j)*(L i/(d*f)) := by
  have hh := normalized_group_equation Q L j h
  have he : L j+∑i∈Finset.univ.erase j,Complex.exp (Q i-Q j)*L i=0 := by
    have hs := Finset.sum_erase_add Finset.univ
      (fun i=>Complex.exp (Q i-Q j)*L i) (Finset.mem_univ j)
    rw [←hs] at hh
    simpa only [sub_self,Complex.exp_zero,one_mul,add_comm] using hh
  exact CRGRay.residual_identity (Finset.univ.erase j) (d*f) (L j)
    (fun i=>Complex.exp (Q i-Q j)) L he

theorem exact_reduced_equation {ι:Type*} (L:ι→ℂ) (j:ι) (d f:ℂ) (hf:f≠0) :
    L j/d=epsilon L j d f*f := by
  unfold epsilon
  rw [div_mul_eq_div_div,div_mul_cancel₀ _ hf]

/-- No bound on an assumed residual is used: its true group quotient is
bounded from the actual grouped equation and nondominant phase differences. -/
theorem epsilon_bound {ι:Type*} [Fintype ι] [DecidableEq ι]
    (Q L:ι→ℂ) (j:ι) (d f:ℂ) (b B:ℝ)
    (h:∑i,Complex.exp (Q i)*L i=0)
    (hQ:∀i,i≠j→(Q i-Q j).re≤-b)
    (hL:∀i,i≠j→‖L i/(d*f)‖≤B) :
    ‖epsilon L j d f‖≤((Finset.univ.erase j).card:ℝ)*(Real.exp (-b)*B) := by
  apply CRGRay.residual_bound (Finset.univ.erase j) (epsilon L j d f)
    (fun i=>Q i-Q j) (fun i=>L i/(d*f)) b B (epsilon_identity Q L j d f h)
  · intro i hi
    exact hQ i (Finset.mem_erase.mp hi).1
  · intro i hi
    exact hL i (Finset.mem_erase.mp hi).1

/-- A polynomial quotient has a genuine polynomial bound and is pole free
on one exterior disk. The estimate uses actual numerator and denominator. -/
theorem polynomial_quotient_bound (P D:Polynomial ℂ) (hD:D≠0) :
    ∃C:ℝ,0<C ∧ ∃R:ℝ,1≤R ∧ ∀z:ℂ,R<‖z‖→
      D.eval z≠0 ∧ ‖P.eval z/D.eval z‖≤C*‖z‖^P.natDegree := by
  have hdeg:P.degree≤(X^P.natDegree:Polynomial ℂ).degree := by
    rw [degree_X_pow]
    exact degree_le_natDegree
  obtain ⟨C,hC,R,hR,hb⟩ := WasowRational.polynomial_bound_of_degree_le hdeg
  obtain ⟨B,hB,S,hS,hd⟩ := WasowRational.polynomial_denominator_bound D hD
  refine ⟨C*B,mul_pos hC hB,max R S,hR.trans (le_max_left ..),?_⟩
  intro z hz
  obtain ⟨hdz,hdzbound⟩ := hd z ((le_max_right ..).trans_lt hz)
  refine ⟨hdz,?_⟩
  have hp:‖P.eval z‖≤C*‖z‖^P.natDegree := by
    simpa only [eval_pow,eval_X,norm_pow] using hb z ((le_max_left ..).trans_lt hz)
  rw [norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hdz)).mpr
  calc
    ‖P.eval z‖≤C*‖z‖^P.natDegree := hp
    _ ≤ (C*‖z‖^P.natDegree)*(B*‖D.eval z‖) :=
      le_mul_of_one_le_right (by positivity) hdzbound
    _ = _ := by ring

/-- A whole finite family has one common numerator-degree bound, constant,
and exterior radius. This will be applied to every coefficient of every group. -/
theorem finite_polynomial_quotient_bound {ι:Type*} [Fintype ι]
    (P:ι→Polynomial ℂ) (D:Polynomial ℂ) (hD:D≠0) :
    ∃C:ℝ,0<C ∧ ∃N:ℕ,∃R:ℝ,1≤R ∧ ∀z:ℂ,R<‖z‖→
      D.eval z≠0 ∧ ∀i,‖(P i).eval z/D.eval z‖≤C*‖z‖^N := by
  classical
  choose C hC R hR hb using fun i=>polynomial_quotient_bound (P i) D hD
  obtain ⟨B,_hB,S,hS,hd⟩ := WasowRational.polynomial_denominator_bound D hD
  let N:=∑i,(P i).natDegree
  let K:=1+∑i,C i
  let T:=max S (1+∑i,R i)
  have hK:0<K := by
    have hh : 0≤∑i,C i := Finset.sum_nonneg (fun i _=>(hC i).le)
    dsimp [K]; linarith
  have hT:1≤T := hS.trans (le_max_left ..)
  refine ⟨K,hK,N,T,hT,?_⟩
  intro z hz
  refine ⟨(hd z ((le_max_left ..).trans_lt hz)).1,?_⟩
  intro i
  have hRi:R i≤T := by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (f:=R)
      (fun j _=>(zero_le_one.trans (hR j))) (Finset.mem_univ i)
    dsimp [T]
    linarith [le_max_right S (1+∑i,R i)]
  have hCi:C i≤K := by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (f:=C)
      (fun j _=>(hC j).le) (Finset.mem_univ i)
    dsimp [K];linarith
  have hNi:(P i).natDegree≤N :=
    Finset.single_le_sum (f:=fun i=>(P i).natDegree) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  exact ((hb i z (hRi.trans_lt hz)).2).trans
    (mul_le_mul hCi (pow_le_pow_right₀ (hT.trans hz.le) hNi)
      (by positivity) hK.le)

/-- The actual polynomial differential group divided by d f has a polynomial
bound once each coefficient quotient and each derivative quotient does. -/
theorem differential_group_bound {n:ℕ}
    (a:Fin n→ℂ) (v:Fin n→ℂ) (d f:ℂ) (C B:ℝ)
    (hC:0≤C) (_hB:0≤B) (ha:∀k,‖a k/d‖≤C) (hv:∀k,‖v k/f‖≤B) :
    ‖(∑k,a k*v k)/(d*f)‖≤(n:ℝ)*(C*B) := by
  have he : (∑k,a k*v k)/(d*f)=∑k,(a k/d)*(v k/f) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    exact div_mul_div_comm .. |>.symm
  rw [he]
  calc
    _ ≤ ∑k,‖(a k/d)*(v k/f)‖ := norm_sum_le ..
    _ ≤ ∑_k:Fin n,C*B := Finset.sum_le_sum (fun k _=>by
      rw [norm_mul]
      exact mul_le_mul (ha k) (hv k) (norm_nonneg _) hC)
    _ = _ := by simp

theorem epsilon_tendsto_zero {ι:Type*} [Fintype ι] [DecidableEq ι]
    (Q L:ℝ→ι→ℂ) (j:ι) (d f:ℝ→ℂ) (B K c:ℝ) (hc:0<c)
    (heq:∀ᶠr in atTop,∑i,Complex.exp (Q r i)*L r i=0)
    (hQ:∀ᶠr in atTop,∀i,i≠j→(Q r i-Q r j).re≤-c*r)
    (hL:∀ᶠr in atTop,∀i,i≠j→‖L r i/(d r*f r)‖≤B*r^K) :
    Tendsto (fun r=>epsilon (L r) j (d r) (f r)) atTop (𝓝 0) := by
  have hb:∀ᶠr in atTop,‖epsilon (L r) j (d r) (f r)‖≤
      (((Finset.univ.erase j).card:ℝ)*B)*(r^K*Real.exp (-c*r)) := by
    filter_upwards [heq,hQ,hL] with r hr hqr hlr
    have hh := epsilon_bound (Q r) (L r) j (d r) (f r) (c*r) (B*r^K) hr
      (by simpa only [neg_mul] using hqr) hlr
    calc
      _ ≤ ((Finset.univ.erase j).card:ℝ)*(Real.exp (-(c*r))*(B*r^K)) := hh
      _ = _ := by rw [neg_mul]; ring
  exact squeeze_zero_norm' hb (CRGRay.polynomial_exp_decay K c _ hc)

theorem epsilon_eventually_ne_one {ι:Type*} [Fintype ι] [DecidableEq ι]
    (Q L:ℝ→ι→ℂ) (j:ι) (d f:ℝ→ℂ) (B K c:ℝ) (hc:0<c)
    (heq:∀ᶠr in atTop,∑i,Complex.exp (Q r i)*L r i=0)
    (hQ:∀ᶠr in atTop,∀i,i≠j→(Q r i-Q r j).re≤-c*r)
    (hL:∀ᶠr in atTop,∀i,i≠j→‖L r i/(d r*f r)‖≤B*r^K) :
    ∀ᶠr in atTop,epsilon (L r) j (d r) (f r)≠1 :=
  (epsilon_tendsto_zero Q L j d f B K c hc heq hQ hL).eventually_ne zero_ne_one

/-- All actual polynomial differential groups share one polynomial radial
bound after division by the selected nonzero leading coefficient. -/
theorem uniform_differential_group_ray_bound {ι:Type*} [Fintype ι] {n:ℕ}
    (a:ι→Fin n→Polynomial ℂ) (D:Polynomial ℂ) (hD:D≠0) (θ:ℝ) :
    ∃C:ℝ,0<C ∧ ∃N:ℕ,∃R:ℝ,1≤R ∧ ∀r:ℝ,R<r→
      D.eval (ray θ r)≠0 ∧ ∀B K:ℝ,0≤B→∀v:Fin n→ℂ,∀f:ℂ,
      (∀k,‖v k/f‖≤B*r^K) → ∀i:ι,
      ‖(∑k,(a i k).eval (ray θ r)*v k)/(D.eval (ray θ r)*f)‖≤
        C*B*r^((N:ℝ)+K) := by
  obtain ⟨C,hC,N,R,hR,hb⟩ := finite_polynomial_quotient_bound
    (fun ik:ι×Fin n=>a ik.1 ik.2) D hD
  refine ⟨((n:ℝ)+1)*C,mul_pos (by positivity) hC,N,R,hR,?_⟩
  intro r hr
  have hrp:0<r := (zero_lt_one.trans_le hR).trans hr
  have hz:‖ray θ r‖=r := WasowRational.norm_ray θ hrp.le
  obtain ⟨hd,hcoeff⟩ := hb (ray θ r) (by rwa [hz])
  refine ⟨hd,?_⟩
  intro B K hB v f hv i
  have hh := differential_group_bound
    (fun k=>(a i k).eval (ray θ r)) v (D.eval (ray θ r)) f
    (C*r^N) (B*r^K) (by positivity) (by positivity)
    (fun k=>by simpa only [hz] using hcoeff (i,k)) hv
  have he : (n:ℝ)*(C*r^N*(B*r^K))=(n:ℝ)*C*B*r^((N:ℝ)+K) := by
    rw [Real.rpow_add hrp,Real.rpow_natCast]
    ring
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : (n:ℝ)≤(n:ℝ)+1) hC.le) hB)
    (Real.rpow_nonneg hrp.le _))

/-- Continuity of the actual quotient residual requires only true nonzero
values of its two denominator factors. -/
theorem epsilon_continuousOn {ι:Type*} (L:ℝ→ι→ℂ) (j:ι) (d f:ℝ→ℂ) (s:Set ℝ)
    (hL:ContinuousOn (fun r=>L r j) s) (hd:ContinuousOn d s) (hf:ContinuousOn f s)
    (hd0:∀r∈s,d r≠0) (hf0:∀r∈s,f r≠0) :
    ContinuousOn (fun r=>epsilon (L r) j (d r) (f r)) s :=
  hL.div (hd.mul hf) (fun r hr=>mul_ne_zero (hd0 r hr) (hf0 r hr))

#print axioms normalized_group_equation
#print axioms epsilon_identity
#print axioms exact_reduced_equation
#print axioms epsilon_bound
#print axioms polynomial_quotient_bound
#print axioms finite_polynomial_quotient_bound
#print axioms differential_group_bound
#print axioms epsilon_tendsto_zero
#print axioms epsilon_eventually_ne_one
#print axioms uniform_differential_group_ray_bound
#print axioms epsilon_continuousOn
end CRGGroupResidual
