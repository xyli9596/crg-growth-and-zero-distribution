import CRGRayComparison
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! The scalar equation is connected to its actual derivative jet and rational
companion matrix, including the direction factor and the rank-one perturbation. -/
set_option autoImplicit false
noncomputable section
open Filter Set Matrix
open scoped Topology Matrix.Norms.Operator
namespace CRGCompanion
open CRGNormalFormGoal
variable {m : ℕ}

/-- Last-row coefficients are in solved form: f^(m+1) = Σ aⱼ f^(j)+εf. -/
def companion (a : Fin (m+1)→RatFunc ℂ) : Matrix (Fin (m+1)) (Fin (m+1)) (RatFunc ℂ) :=
  fun i=>Fin.lastCases a (fun k j=>if j=k.succ then 1 else 0) i

def jet (f : ℂ→ℂ) (θ r : ℝ) : Fin (m+1)→ℂ :=
  fun i=>iteratedDeriv i.val f (ray θ r)

def perturbation (θ : ℝ) (ε : ℝ→ℂ) (r : ℝ) : Matrix (Fin (m+1)) (Fin (m+1)) ℂ :=
  fun i j=>if i=Fin.last m ∧ j=0 then Complex.exp ((θ:ℂ)*Complex.I)*ε r else 0

theorem companion_mulVec_last (a : Fin (m+1)→RatFunc ℂ) (θ r : ℝ) (x : Fin (m+1)→ℂ) :
    (coefficientOnRay (companion a) θ r).mulVec x (Fin.last m)=
      Complex.exp ((θ:ℂ)*Complex.I)*∑j,RatFunc.eval (RingHom.id ℂ) (ray θ r) (a j)*x j := by
  simp [coefficientOnRay,companion,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]

theorem companion_mulVec_castSucc (a : Fin (m+1)→RatFunc ℂ) (θ r : ℝ)
    (x : Fin (m+1)→ℂ) (i : Fin m) :
    (coefficientOnRay (companion a) θ r).mulVec x i.castSucc=
      Complex.exp ((θ:ℂ)*Complex.I)*x i.succ := by
  simp [coefficientOnRay,companion,Matrix.mulVec,dotProduct,apply_ite]

theorem perturbation_mulVec (θ r : ℝ) (ε : ℝ→ℂ) (x : Fin (m+1)→ℂ) :
    (perturbation (m:=m) θ ε r).mulVec x=
      Pi.single (Fin.last m) (Complex.exp ((θ:ℂ)*Complex.I)*ε r*x 0) := by
  ext i
  by_cases hi : i=Fin.last m
  · subst i
    simp [perturbation,Matrix.mulVec,dotProduct]
  · simp [perturbation,Matrix.mulVec,dotProduct,hi]

theorem differentiable_iteratedDeriv (f : ℂ→ℂ) (hf : Differentiable ℂ f) (n:ℕ) :
    Differentiable ℂ (iteratedDeriv n f) := by
  induction n with
  | zero => simpa using hf
  | succ n hn => simpa only [iteratedDeriv_succ] using hn.deriv

theorem jet_component_hasDerivAt (f : ℂ→ℂ) (hf : Differentiable ℂ f)
    (θ r : ℝ) (i : Fin (m+1)) :
    HasDerivAt (fun t=>jet f θ t i)
      (Complex.exp ((θ:ℂ)*Complex.I)*iteratedDeriv (i.val+1) f (ray θ r)) r := by
  have hd := (differentiable_iteratedDeriv f hf i.val (ray θ r)).hasDerivAt
  have hh := (hd.comp (r:ℂ) ((hasDerivAt_id (r:ℂ)).mul_const
    (Complex.exp ((θ:ℂ)*Complex.I)))).comp_ofReal
  simpa only [jet,ray,iteratedDeriv_succ,Function.comp_apply,id_eq,one_mul,mul_one,mul_comm] using hh

theorem jet_hasDerivAt_of_scalar_equation
    (a : Fin (m+1)→RatFunc ℂ) (f : ℂ→ℂ) (hf : Differentiable ℂ f)
    (θ r : ℝ) (ε : ℝ→ℂ)
    (heq : iteratedDeriv (m+1) f (ray θ r)=
      (∑j:Fin (m+1),RatFunc.eval (RingHom.id ℂ) (ray θ r) (a j)*
        iteratedDeriv j.val f (ray θ r))+ε r*f (ray θ r)) :
    HasDerivAt (jet (m:=m) f θ)
      ((coefficientOnRay (companion a) θ r+perturbation θ ε r).mulVec (jet f θ r)) r := by
  apply hasDerivAt_pi.mpr
  intro i
  rw [Matrix.add_mulVec,perturbation_mulVec]
  induction i using Fin.lastCases with
  | last =>
    have hh := jet_component_hasDerivAt f hf θ r (Fin.last m)
    simpa only [Fin.val_last,heq,companion_mulVec_last,Pi.add_apply,
      Pi.single_eq_same,jet,Fin.val_zero,iteratedDeriv_zero,mul_add,mul_assoc] using hh
  | cast j =>
    have hh := jet_component_hasDerivAt f hf θ r j.castSucc
    have hj : j.val≠m := ne_of_lt j.isLt
    simpa [companion_mulVec_castSucc,Pi.single_apply,jet,Fin.ext_iff,hj] using hh

theorem perturbation_continuousOn (θ a : ℝ) (ε : ℝ→ℂ)
    (hε : ContinuousOn ε (Ioi a)) :
    ContinuousOn (perturbation (m:=m) θ ε) (Ioi a) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  unfold perturbation
  split_ifs
  · exact continuousOn_const.mul hε
  · exact continuousOn_const

theorem norm_perturbation_le (θ r : ℝ) (ε : ℝ→ℂ) :
    ‖perturbation (m:=m) θ ε r‖≤‖ε r‖ := by
  rw [←WasowGaugeAssembly.norm_toOperator]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖(perturbation (m:=m) θ ε r).mulVec x‖≤‖ε r‖*‖x‖
  rw [perturbation_mulVec]
  have hn : ‖Complex.exp ((θ:ℂ)*Complex.I)‖=1 := by
    simp [Complex.norm_exp,Complex.mul_re]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  by_cases hi : i=Fin.last m
  · subst i
    simpa only [Pi.single_eq_same,norm_mul,hn,one_mul] using
      mul_le_mul_of_nonneg_left (norm_le_pi_norm x 0) (norm_nonneg (ε r))
  · simp only [Pi.single_apply,hi,ite_false,norm_zero]
    positivity

theorem jet_polynomial_comparison (f : ℂ→ℂ) (θ r C K : ℝ)
    (hr : 1≤r) (hC : 0<C) (hK : 0≤K) (hf : f (ray θ r)≠0)
    (hb : ∀k:ℕ,1≤k→k<m+1→
      ‖iteratedDeriv k f (ray θ r)/f (ray θ r)‖≤C*r^K) :
    ‖f (ray θ r)‖≤‖jet (m:=m) f θ r‖ ∧
    ‖jet (m:=m) f θ r‖≤(C+1)*r^K*‖f (ray θ r)‖ := by
  constructor
  · simpa only [jet,Fin.val_zero,iteratedDeriv_zero] using
      norm_le_pi_norm (jet (m:=m) f θ r) 0
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    change ‖iteratedDeriv i.val f (ray θ r)‖≤_
    by_cases hi : i.val=0
    · rw [hi,iteratedDeriv_zero]
      have hpow : 1≤r^K := Real.one_le_rpow hr hK
      have hp : 1≤(C+1)*r^K := one_le_mul_of_one_le_of_one_le (by linarith) hpow
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (f (ray θ r)))
    · have hh := hb i.val (by omega) i.isLt
      rw [norm_div] at hh
      have hh' := (div_le_iff₀ (norm_pos_iff.mpr hf)).mp hh
      exact hh'.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C≤C+1) (Real.rpow_nonneg (by linarith) _))
        (norm_nonneg _))

#print axioms companion_mulVec_last
#print axioms companion_mulVec_castSucc
#print axioms perturbation_mulVec
#print axioms differentiable_iteratedDeriv
#print axioms jet_component_hasDerivAt
#print axioms jet_hasDerivAt_of_scalar_equation
#print axioms perturbation_continuousOn
#print axioms norm_perturbation_le
#print axioms jet_polynomial_comparison
end CRGCompanion
