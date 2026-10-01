import CRGPuiseuxCoordinates
import CRGCollectedResidual

/-! Transfer of the actual scalar equation and Gundersen jet bounds to
the inverse Puiseux coordinate. Every formally zero high coefficient stays
in a genuine flat forcing term. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set Asymptotics
open scoped Topology BigOperators
namespace CRGPuiseuxRayReduction
open CRGNormalFormGoal CRGPuiseuxCoordinates CRGPuiseuxScalarReduction
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientRayTail
open WasowLaurentRayEquation WasowGlobalRayData
variable {n : ℕ}

def localJet (f : ℂ → ℂ) (p : ℕ) (j : Fin (n+1)) (x : ℂ) : ℂ :=
  iteratedDeriv j.val f (originalPoint p x)/f (originalPoint p x)

def clearedCoefficients (a : Fin (n+1) → ℂ → ℂ) (p h : ℕ)
    (W : ℂ → ℂ) (j : Fin (n+1)) (x : ℂ) : ℂ :=
  x^h*a j (originalPoint p x)/W x

theorem norm_inverseRay (φ : ℝ) {s : ℝ} (hs : 0≤s) :
    ‖inverseRay (direction φ) s‖=s⁻¹ := by
  simp [inverseRay,norm_mul,direction_norm,Complex.norm_real,Real.norm_of_nonneg hs]

theorem localJet_power_bound {f : ℂ → ℂ} {p : ℕ} (hp : 0<p)
    (θ J : ℝ)
    (hjet : ∀ᶠ r : ℝ in atTop,∀j : Fin (n+1),
      ‖iteratedDeriv j.val f (ray θ r)/f (ray θ r)‖≤r^J) :
    ∀j : Fin (n+1),∃K : ℕ,
      localJet f p j =O[rayFilter (direction (θ/p))]
        (fun x : ℂ=>(‖x‖^K)⁻¹) := by
  obtain ⟨K,hK⟩ := exists_nat_ge ((p:ℝ)*J)
  intro j
  refine ⟨K,?_⟩
  rw [rayFilter,isBigO_map]
  apply IsBigO.of_bound 1
  have ht : Tendsto (fun s : ℝ=>s^p) atTop atTop := tendsto_pow_atTop hp.ne'
  filter_upwards [ht.eventually hjet,eventually_ge_atTop (1:ℝ)] with s hs hs1
  have hsp : 0<s := zero_lt_one.trans_le hs1
  have he : (s^p)^J=s^((p:ℝ)*J) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hsp.le]
  have hh : ‖iteratedDeriv j.val f (ray θ (s^p))/f (ray θ (s^p))‖≤s^(K:ℝ) :=
    (hs j).trans (by rw [he];exact Real.rpow_le_rpow_of_exponent_le hs1 hK)
  simpa only [Function.comp_apply,localJet,originalPoint_inverseRay p hp,
    norm_inverseRay _ hsp.le,inv_pow,inv_inv,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hsp.le K),one_mul,Real.rpow_natCast] using hh

theorem localJet_zero {f : ℂ → ℂ} {p : ℕ} (hp : 0<p) (θ : ℝ)
    (hnon : ∀ᶠr in atTop,f (ray θ r)≠0) :
    ∀ᶠx in rayFilter (direction (θ/p)),localJet (n:=n) f p 0 x=1 := by
  change ∀ᶠs : ℝ in atTop,localJet (n:=n) f p 0 (inverseRay (direction (θ/p)) s)=1
  filter_upwards [(tendsto_pow_atTop hp.ne').eventually hnon] with s hs
  simp [localJet,originalPoint_inverseRay p hp,hs]

theorem cleared_equation (a : Fin (n+1) → ℂ → ℂ) (f : ℂ → ℂ) (p h : ℕ)
    (W : ℂ → ℂ)
    (heq : ∀z : ℂ,∑j : Fin (n+1),a j z*iteratedDeriv j.val f z=0) (x : ℂ) :
    ∑j : Fin (n+1),clearedCoefficients a p h W j x*localJet f p j x=0 := by
  have ht (j : Fin (n+1)) :
      clearedCoefficients a p h W j x*localJet f p j x=
        (x^h/(W x*f (originalPoint p x)))*
          (a j (originalPoint p x)*iteratedDeriv j.val f (originalPoint p x)) := by
    simp only [clearedCoefficients,localJet,div_eq_mul_inv,mul_inv_rev]
    ring
  simp_rw [ht]
  rw [←Finset.mul_sum,heq,mul_zero]

theorem highest_positive_from_ray_bounds
    {a : Fin (n+1) → ℂ → ℂ} {f : ℂ → ℂ} {p h : ℕ} (hp : 0<p)
    {W : ℂ → ℂ} {A : Fin (n+1) → PowerSeries ℂ} (H : Highest A)
    (θ J : ℝ)
    (hC : ∀j,CompleteExpansion (rayFilter (direction (θ/p)))
      (clearedCoefficients a p h W j) (A j))
    (hnon : ∀ᶠr in atTop,f (ray θ r)≠0)
    (hjet : ∀ᶠr in atTop,∀j : Fin (n+1),
      ‖iteratedDeriv j.val f (ray θ r)/f (ray θ r)‖≤r^J)
    (heq : ∀z : ℂ,∑j : Fin (n+1),a j z*iteratedDeriv j.val f z=0) :
    0<H.index.val := by
  letI : NeBot (rayFilter (direction (θ/p))) := by unfold rayFilter;infer_instance
  exact highest_order_positive (rayFilter_le_punctured (direction_ne_zero _)) hC H
    (localJet f p) (localJet_power_bound hp θ J hjet) (localJet_zero hp θ hnon)
      (Eventually.of_forall (cleared_equation a f p h W heq))

theorem flat_residual_from_ray_bounds
    {a : Fin (n+1) → ℂ → ℂ} {f : ℂ → ℂ} {p h : ℕ} (hp : 0<p)
    {W : ℂ → ℂ} {A : Fin (n+1) → PowerSeries ℂ} (H : Highest A)
    (θ J : ℝ)
    (hC : ∀j,CompleteExpansion (rayFilter (direction (θ/p)))
      (clearedCoefficients a p h W j) (A j))
    (hjet : ∀ᶠr : ℝ in atTop,∀j : Fin (n+1),
      ‖iteratedDeriv j.val f (ray θ r)/f (ray θ r)‖≤r^J) :
    Flat (rayFilter (direction (θ/p)))
      (residual (clearedCoefficients a p h W) H.index (localJet f p)) :=
  residual_flat (rayFilter_le_punctured (direction_ne_zero _)) hC H
    (localJet f p) (localJet_power_bound hp θ J hjet)

theorem flat_on_physical_ray {p : ℕ} {F : ℂ → ℂ} {l : Filter ℂ}
    (hflat : Flat l F) (g : ℝ → ℂ) (ht : Tendsto g atTop l) (θ : ℝ)
    (hcoord : ∀ᶠr : ℝ in atTop,originalPoint p (g r)=ray θ r) :
    ∀N : ℕ,(fun r=>F (g r)) =O[atTop] (fun r : ℝ=>(r^N)⁻¹) := by
  intro N
  have he := (hflat (p*N)).comp_tendsto ht
  apply he.congr' EventuallyEq.rfl
  filter_upwards [hcoord,eventually_gt_atTop (0:ℝ)] with r hr hrp
  have hh := congrArg norm hr
  have hnormray : ‖ray θ r‖=r := by
    simp [ray,norm_mul,Complex.norm_exp,Complex.mul_re,Real.norm_of_nonneg hrp.le]
  simp only [originalPoint,zpow_neg,zpow_natCast,norm_inv,norm_pow,hnormray] at hh
  have hx : ‖g r‖^p=r⁻¹ := by
    have hi := congrArg Inv.inv hh
    simpa only [inv_inv] using hi
  simpa only [Function.comp_apply,pow_mul,hx,inv_pow]

#print axioms localJet_power_bound
#print axioms localJet_zero
#print axioms cleared_equation
#print axioms highest_positive_from_ray_bounds
#print axioms flat_residual_from_ray_bounds
#print axioms flat_on_physical_ray
end CRGPuiseuxRayReduction
