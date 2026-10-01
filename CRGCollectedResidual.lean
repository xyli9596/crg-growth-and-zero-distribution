import CRGGroupResidual
import CRGCollectedEquation
import GundersenJet

/-! Actual analytic residual of a collected exponential-polynomial equation.
Gundersen's ray estimate and exponential dominance are converted to one
continuous exponentially small scalar residual on a genuine ray tail. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial Matrix
open scoped Topology BigOperators
namespace CRGCollectedResidual
open CRGNormalFormGoal CRGCollectedEquation CRGGroupResidual
variable {n:ℕ} {f:ℂ→ℂ}

def groupValue (E:CollectedEquation n f) (θ r:ℝ) (q:E.exponents) : ℂ :=
  ∑j,(E.coeff q.val j).eval (ray θ r)*iteratedDeriv j.val f (ray θ r)

def residual (E:CollectedEquation n f) (ν:E.exponents) (D:Polynomial ℂ) (θ r:ℝ) : ℂ :=
  epsilon (groupValue E θ r) ν (D.eval (ray θ r)) (f (ray θ r))

theorem groupValue_continuous (E:CollectedEquation n f) (hf:Differentiable ℂ f)
    (θ:ℝ) (q:E.exponents) : Continuous (fun r=>groupValue E θ r q) := by
  have hr:Continuous (ray θ) := Complex.continuous_ofReal.mul continuous_const
  apply continuous_finsetSum
  intro j _
  exact ((E.coeff q.val j).continuous.comp hr).mul
    ((CRGCompanion.differentiable_iteratedDeriv f hf j.val).continuous.comp hr)

/-- The entire finite jet, including its zeroth entry, has a single exponent. -/
theorem common_jet_bound (θ ρ:ℝ) (hρ:0≤ρ)
    (hnon:∀ᶠr in atTop,f (ray θ r)≠0)
    (hjet:GundersenAngles.RayDerivativeBound f ρ n 1 θ) :
    ∀ᶠr in atTop,∀k:Fin (n+1),
      ‖iteratedDeriv k.val f (ray θ r)/f (ray θ r)‖≤r^((n:ℝ)*ρ) := by
  filter_upwards [hnon,hjet,eventually_ge_atTop (1:ℝ)] with r hfr hj hr
  intro k
  by_cases hk:k.val=0
  · simp only [hk,iteratedDeriv_zero,div_self hfr,norm_one]
    exact Real.one_le_rpow hr (mul_nonneg (Nat.cast_nonneg _) hρ)
  · have hkn:k.val≤n := Nat.le_of_lt_succ k.isLt
    have hh := hj k.val (by omega) hkn
    simp only [sub_add_cancel] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hr
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) hρ))

/-- Actual residual control, including continuity, nonzero denominators,
exponential decay, exact reduced equation, and exclusion of ε=1. -/
theorem exists_residual_control
    (E:CollectedEquation n f) (hf:Differentiable ℂ f)
    (θ ρ:ℝ) (hρ:0≤ρ) (ν:E.exponents) (D:Polynomial ℂ) (hD:D≠0)
    (c:ℝ) (hc:0<c)
    (hphase:∀ᶠr in atTop,∀q:E.exponents,q≠ν→
      ((q.val-ν.val).eval (ray θ r)).re≤-c*r)
    (hnon:∀ᶠr in atTop,f (ray θ r)≠0)
    (hjet:GundersenAngles.RayDerivativeBound f ρ n 1 θ) :
    ∃B:ℝ,0<B ∧ ∃J:ℝ,0≤J ∧ ∃R:ℝ,1≤R ∧
      ContinuousOn (residual E ν D θ) (Ioi R) ∧
      ∀r>R,D.eval (ray θ r)≠0 ∧ f (ray θ r)≠0 ∧
        ‖residual E ν D θ r‖≤B*(r^J*Real.exp (-c*r)) ∧
        groupValue E θ r ν/D.eval (ray θ r)=residual E ν D θ r*f (ray θ r) ∧
        residual E ν D θ r≠1 := by
  classical
  obtain ⟨C,hC,N,S,hS,hbound⟩ := uniform_differential_group_ray_bound
    (fun q:E.exponents=>E.coeff q.val) D hD θ
  let J:ℝ := (N:ℝ)+(n:ℝ)*ρ
  have hJ:0≤J := by dsimp [J];positivity
  let L:ℝ := ((Finset.univ.erase ν).card:ℝ)
  let B:ℝ := (L+1)*C
  have hL:0≤L := by dsimp [L];positivity
  have hB:0<B := by dsimp [B];positivity
  have hcommon := common_jet_bound θ ρ hρ hnon hjet
  obtain ⟨a,ha⟩ := eventually_atTop.mp
    (hnon.and (hcommon.and (hphase.and (eventually_gt_atTop S))))
  let R0:=max 1 a
  have hR0:1≤R0 := le_max_left ..
  have ht (r:ℝ) (hr:R0<r) :
      D.eval (ray θ r)≠0 ∧ f (ray θ r)≠0 ∧
      ‖residual E ν D θ r‖≤B*(r^J*Real.exp (-c*r)) := by
    have hr0 : 0≤r := zero_le_one.trans (hR0.trans hr.le)
    obtain ⟨hfr,hqr,hpr,hsr⟩ := ha r ((le_max_right ..).trans hr.le)
    obtain ⟨hdr,hbr⟩ := hbound r hsr
    have hgroup (q:E.exponents) :
        ‖groupValue E θ r q/(D.eval (ray θ r)*f (ray θ r))‖≤C*r^J := by
      simpa only [groupValue,one_mul,mul_one,J] using
        hbr 1 ((n:ℝ)*ρ) zero_le_one
          (fun j=>iteratedDeriv j.val f (ray θ r)) (f (ray θ r))
          (fun j=>by simpa using hqr j) q
    have heq : ∑q:E.exponents,Complex.exp (q.val.eval (ray θ r))*groupValue E θ r q=0 :=
      E.subtype_equation (ray θ r)
    have hh := epsilon_bound (fun q:E.exponents=>q.val.eval (ray θ r))
      (groupValue E θ r) ν (D.eval (ray θ r)) (f (ray θ r)) (c*r) (C*r^J) heq
      (fun q hq=>by simpa only [eval_sub,neg_mul] using hpr q hq)
      (fun q _=>hgroup q)
    refine ⟨hdr,hfr,?_⟩
    change ‖epsilon (groupValue E θ r) ν (D.eval (ray θ r)) (f (ray θ r))‖≤_
    calc
      _ ≤ L*(Real.exp (-(c*r))*(C*r^J)) := hh
      _ = (L*C)*(r^J*Real.exp (-c*r)) := by rw [neg_mul];ring
      _ ≤ B*(r^J*Real.exp (-c*r)) := mul_le_mul_of_nonneg_right
        (by dsimp [B];nlinarith) (by positivity)
  have hlim:Tendsto (residual E ν D θ) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ((eventually_gt_atTop R0).mono (fun r hr=>(ht r hr).2.2))
    exact CRGRay.polynomial_exp_decay J c B hc
  obtain ⟨S1,hS1⟩ := eventually_atTop.mp (hlim.eventually_ne zero_ne_one)
  let R:=max R0 S1
  have hR0R:R0≤R := le_max_left ..
  refine ⟨B,hB,J,hJ,R,hR0.trans hR0R,?_,?_⟩
  · apply epsilon_continuousOn
    · exact (groupValue_continuous E hf θ ν).continuousOn
    · exact (D.continuous.comp (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    · exact (hf.continuous.comp (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    · exact fun r hr=>(ht r (hR0R.trans_lt hr)).1
    · exact fun r hr=>(ht r (hR0R.trans_lt hr)).2.1
  · intro r hr
    obtain ⟨hdr,hfr,hbr⟩ := ht r (hR0R.trans_lt hr)
    exact ⟨hdr,hfr,hbr,exact_reduced_equation _ ν _ _ hfr,
      hS1 r ((le_max_right ..).trans hr.le)⟩

#print axioms groupValue_continuous
#print axioms common_jet_bound
#print axioms exists_residual_control
end CRGCollectedResidual
