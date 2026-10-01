import CRGPuiseuxSector
import CRGAsymptoticCoefficientScalarAlgebra
import CRGExponentialDominance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Finite actual exponential groups with complete amplitude expansions
construct the coefficient sectors required by Proposition 5.1. Dominance is
proved outside a null set from the distinct normalized polynomials. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set Asymptotics Polynomial MeasureTheory
open scoped Topology BigOperators
namespace CRGExponentialExpansionSector
open CRGNormalFormGoal CRGPuiseuxCoordinates CRGPuiseuxRayReduction
open CRGPuiseuxSector CRGAsymptoticCoefficientQuotient
open CRGAsymptoticCoefficientRayTail CRGAsymptoticCoefficientScalarAlgebra
open WasowLaurentRayEquation WasowGlobalRayData
variable {n : ℕ}

theorem exponential_flat_on_local_ray {p : ℕ} (hp : 0<p) (θ : ℝ)
    (Q : Polynomial ℂ) {c : ℝ} (hc : 0<c)
    (hneg : ∀ᶠr : ℝ in atTop,(Q.eval (ray θ r)).re≤-c*r) :
    Flat (rayFilter (direction (θ/p))) (fun x=>Complex.exp (Q.eval (originalPoint p x))) := by
  intro N
  rw [rayFilter,isBigO_map]
  have ht : Tendsto (fun s : ℝ=>s^p) atTop atTop := tendsto_pow_atTop hp.ne'
  have he : (fun s : ℝ=>Complex.exp (Q.eval (originalPoint p (inverseRay (direction (θ/p)) s))))
      =O[atTop] (fun s : ℝ=>Real.exp (-c*s)) := by
    apply IsBigO.of_bound 1
    filter_upwards [ht.eventually hneg,eventually_ge_atTop (1:ℝ)] with s hs hs1
    have hsp : s≤s^p := by
      simpa only [pow_one] using pow_le_pow_right₀ hs1 (show 1≤p from hp)
    rw [Complex.norm_exp,originalPoint_inverseRay p hp]
    simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul]
    exact Real.exp_le_exp.mpr (hs.trans (mul_le_mul_of_nonpos_left hsp (by linarith)))
  have hexp := isLittleO_exp_neg_mul_rpow_atTop hc (-(N:ℝ)) |>.isBigO
  apply (he.trans hexp).congr' EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
  simp only [Function.comp_apply,norm_inverseRay _ hs,inv_pow,
    Real.rpow_neg hs,Real.rpow_natCast]

/-- A complete (even divergent) expansion is polynomially bounded after
clearing, so an exponentially smaller group has zero formal expansion. -/
theorem flat_times_expansion {l : Filter ℂ} (hl : l≤𝓝 (0:ℂ))
    {f g : ℂ → ℂ} {A : PowerSeries ℂ} (hf : Flat l f)
    (hg : CompleteExpansion l g A) : Flat l (fun x=>f x*g x) := by
  have hb : g =O[l] (fun _ : ℂ=>(1:ℝ)) :=
    isBigO_const_of_tendsto (tendsto_of_completeExpansion hl hg) (by norm_num)
  intro N
  simpa only [mul_one] using (hf N).mul hb

structure Groups (a : Fin (n+1) → ℂ → ℂ) where
  denominator : ℕ
  positive : 0<denominator
  clearing : ℕ
  angles : Set ℝ
  count : ℕ
  count_positive : 0<count
  phase : Fin count → Polynomial ℂ
  phase_normalized : ∀q,(phase q).coeff 0=0
  phase_injective : Function.Injective phase
  amplitude : Fin count → Fin (n+1) → ℂ → ℂ
  series : Fin count → Fin (n+1) → PowerSeries ℂ
  some_nonzero : ∀q,∃j,series q j≠0
  representation : ∀θ∈angles,∀j,∀ᶠx in rayFilter (direction (θ/denominator)),
    a j (originalPoint denominator x)=∑q,amplitude q j x*Complex.exp ((phase q).eval (originalPoint denominator x))
  expansion : ∀θ∈angles,∀q j,CompleteExpansion (rayFilter (direction (θ/denominator)))
    (fun x=>x^clearing*amplitude q j x) (series q j)

def Groups.dominates {a : Fin (n+1) → ℂ → ℂ} (D : Groups a)
    (ν : Fin D.count) (θ : ℝ) : Prop :=
  ∃c : ℝ,0<c ∧ ∀ᶠr in atTop,∀q : Fin D.count,q≠ν→
    ((D.phase q-D.phase ν).eval (ray θ r)).re≤-c*r

theorem Groups.normalized_expansion {a : Fin (n+1) → ℂ → ℂ}
    (D : Groups a) (ν : Fin D.count) (θ : ℝ) (hθ : θ∈D.angles)
    (hdom : D.dominates ν θ) (j : Fin (n+1)) :
    CompleteExpansion (rayFilter (direction (θ/D.denominator)))
      (clearedCoefficients a D.denominator D.clearing
        (fun x=>Complex.exp ((D.phase ν).eval (originalPoint D.denominator x))) j)
      (D.series ν j) := by
  classical
  obtain ⟨c,hc,hneg⟩ := hdom
  let l := rayFilter (direction (θ/D.denominator))
  have hl : l≤𝓝 (0:ℂ) := (rayFilter_le_punctured (direction_ne_zero _)).trans nhdsWithin_le_nhds
  let F : Fin D.count → ℂ → ℂ := fun q x=>
    Complex.exp ((D.phase q-D.phase ν).eval (originalPoint D.denominator x))*
      (x^D.clearing*D.amplitude q j x)
  let B : Fin D.count → PowerSeries ℂ := fun q=>if q=ν then D.series ν j else 0
  have hb : ∀q,CompleteExpansion l (F q) (B q) := by
    intro q
    by_cases hq : q=ν
    · subst q
      simpa only [F,B,if_pos rfl,sub_self,eval_zero,Complex.exp_zero,one_mul] using D.expansion θ hθ ν j
    · have hf := exponential_flat_on_local_ray D.positive θ (D.phase q-D.phase ν) hc
        (hneg.mono (fun r hr=>hr q hq))
      simpa only [F,B,if_neg hq] using (flat_iff_zero_expansion _ _).mp
        (flat_times_expansion hl hf (D.expansion θ hθ q j))
  have hsum := completeExpansion_sum Finset.univ (fun q _=>hb q)
  have hB : (∑q,B q)=D.series ν j := by simp [B]
  rw [hB] at hsum
  intro N
  apply (hsum N).congr' ?_ EventuallyEq.rfl
  filter_upwards [D.representation θ hθ j] with x hx
  change (∑q,F q x)-(PowerSeries.trunc N (D.series ν j)).eval x=_
  congr 1
  unfold clearedCoefficients
  rw [hx,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  simp only [F,eval_sub,Complex.exp_sub,div_eq_mul_inv]
  ring

def Groups.sector {a : Fin (n+1) → ℂ → ℂ} (D : Groups a)
    (ν : Fin D.count) : Sector a where
  denominator := D.denominator
  positive := D.positive
  clearing := D.clearing
  angles := {θ | θ∈D.angles ∧ D.dominates ν θ}
  multiplier := fun x=>Complex.exp ((D.phase ν).eval (originalPoint D.denominator x))
  series := D.series ν
  some_nonzero := D.some_nonzero ν
  multiplier_continuous := by
    intro θ _hθ
    have hne : ∀ᶠx : ℂ in 𝓝[≠] (0:ℂ),x≠0 := self_mem_nhdsWithin
    filter_upwards [hne.filter_mono (rayFilter_le_punctured (direction_ne_zero _))] with x hx
    exact Complex.continuous_exp.continuousAt.comp
      ((D.phase ν).continuous.continuousAt.comp (continuousAt_id.zpow₀ _ (Or.inl hx)))
  multiplier_nonzero := fun _ _=>Eventually.of_forall (fun _=>Complex.exp_ne_zero _)
  expansion := fun θ hθ j=>D.normalized_expansion ν θ hθ.1 hθ.2 j

/-- Sector dominance is established from the fixed normalized phases. -/
theorem Groups.ae_sector_cover {a : Fin (n+1) → ℂ → ℂ} (D : Groups a) :
    ∀ᵐθ : ℝ,θ∈D.angles → ∃ν : Fin D.count,θ∈(D.sector ν).angles := by
  letI : Nonempty (Fin D.count) := ⟨⟨0,D.count_positive⟩⟩
  filter_upwards [CRGExponentialDominance.ae_exists_dominant_group
    D.phase D.phase_normalized D.phase_injective] with θ hθ
  intro hm
  obtain ⟨ν,c,hc,hneg⟩ := hθ
  exact ⟨ν,hm,c,hc,hneg⟩

#print axioms exponential_flat_on_local_ray
#print axioms flat_times_expansion
#print axioms Groups.normalized_expansion
#print axioms Groups.sector
#print axioms Groups.ae_sector_cover
end CRGExponentialExpansionSector
