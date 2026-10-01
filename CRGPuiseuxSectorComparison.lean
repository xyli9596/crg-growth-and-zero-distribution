import CRGPuiseuxSector
import CRGPuiseuxCompanionComparison

/-! Ray comparison from the coefficient-only sector packet. The entire
solution and its polynomial jet estimates generate the actual flat forcing,
its continuity, and the positive reduced order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology BigOperators Matrix.Norms.Operator
open Filter Set Asymptotics
namespace CRGPuiseuxSectorComparison
open CRGNormalFormGoal CRGPuiseuxSector CRGPuiseuxRayReduction
open CRGPuiseuxScalarReduction CRGPuiseuxCoordinates
open CRGPuiseuxCompanionNormalForm CRGPuiseuxCompanionExpansion
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientRayTail
open WasowGlobalRayData WasowLaurentRayEquation WasowRamifiedGauge
variable {n : ℕ}

theorem localOnRay_continuousAt {A : Fin (n+1) → PowerSeries ℂ}
    (H : Highest A) (p : ℕ) (W : FormalData H p) (θ : ℝ) {r : ℝ} (hr : 0<r) :
    ContinuousAt (localOnRay H p W θ) r := by
  have hroot := (rootRadius_hasDerivAt (denominator H p W) hr).continuousAt
  have hinv := (inverseRay_hasDerivAt (direction (θ/denominator H p W))
    (rootRadius_pos (denominator H p W) hr).ne').continuousAt
  exact (hinv.comp hroot).pow W.denominator

theorem localJet_continuousAt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (p : ℕ) (j : Fin (n+1)) {x : ℂ} (hx : x≠0)
    (hnon : f (originalPoint p x)≠0) : ContinuousAt (localJet f p j) x := by
  have hp : ContinuousAt (originalPoint p) x :=
    continuousAt_id.zpow₀ (-(p:ℤ)) (Or.inl hx)
  exact ((CRGCompanion.differentiable_iteratedDeriv f hf j.val _).continuousAt.comp hp).div
    (hf.continuous.continuousAt.comp hp) hnon

theorem residual_continuousAt (C : Fin (n+1) → ℂ → ℂ) (m : Fin (n+1))
    (v : Fin (n+1) → ℂ → ℂ) {x : ℂ}
    (hC : ∀j,ContinuousAt (C j) x) (hden : C m x≠0)
    (hv : ∀j,ContinuousAt (v j) x) : ContinuousAt (residual C m v) x := by
  unfold CRGPuiseuxScalarReduction.residual
  apply ContinuousAt.neg
  apply tendsto_finsetSum Finset.univ
  intro j _hj
  change ContinuousAt (fun z : ℂ=>if m.val<j.val then C j z/C m z*v j z else 0) x
  by_cases h : m.val<j.val
  · have hh := ((hC j).div (hC m) hden).mul (hv j)
    change ContinuousAt (fun z=>C j z/C m z*v j z) x at hh
    simpa only [if_pos h] using hh
  · simpa only [if_neg h] using (continuousAt_const : ContinuousAt (fun _ : ℂ=> (0:ℂ)) x)

theorem companion_continuousAt {A : Fin (n+1) → PowerSeries ℂ}
    (C : Fin (n+1) → ℂ → ℂ) (H : Highest A) {x : ℂ}
    (hC : ∀j,ContinuousAt (C j) x) (hden : C H.index x≠0) :
    ContinuousAt (companion C H) x := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  unfold companion
  split_ifs
  · exact ((hC _).div (hC _) hden).neg
  · exact continuousAt_const
  · exact continuousAt_const

theorem reduced_physical_equation
    (a : Fin (n+1) → ℂ → ℂ) (S : Sector a) (f : ℂ → ℂ)
    (heq : ∀z : ℂ,∑j : Fin (n+1),a j z*iteratedDeriv j.val f z=0)
    (θ : ℝ) {r : ℝ} (hr : 0<r) (hnon : f (ray θ r)≠0)
    (hden : S.coefficients S.highest.index (localOnRay S.highest S.denominator S.formal θ r)≠0) :
    iteratedDeriv S.highest.index.val f (ray θ r)=
      (∑j : Fin S.highest.index.val,
        -(S.coefficients (CRGGroupHighest.lowerIndex S.highest.index j)
            (localOnRay S.highest S.denominator S.formal θ r)/
          S.coefficients S.highest.index (localOnRay S.highest S.denominator S.formal θ r))*
          iteratedDeriv j.val f (ray θ r))+
      residual S.coefficients S.highest.index (localJet f S.denominator)
        (localOnRay S.highest S.denominator S.formal θ r)*f (ray θ r) := by
  let x := localOnRay S.highest S.denominator S.formal θ r
  have hcoord : originalPoint S.denominator x=ray θ r :=
    originalPoint_localOnRay S.highest S.denominator S.positive S.formal θ hr.le
  have hred := reduced_equation S.coefficients S.highest.index (localJet f S.denominator) x hden
    (cleared_equation a f S.denominator S.clearing S.multiplier heq x)
  have hm := congrArg (fun z : ℂ=>z*f (ray θ r)) hred
  simp only [add_mul,Finset.sum_mul,localJet,hcoord,div_mul_cancel₀ _ hnon,
    mul_assoc,CRGGroupHighest.lowerIndex] at hm
  have hsum : (∑j : Fin S.highest.index.val,
      -(S.coefficients (CRGGroupHighest.lowerIndex S.highest.index j) x/S.coefficients S.highest.index x)*
        iteratedDeriv j.val f (ray θ r))=
      -(∑j : Fin S.highest.index.val,
      (S.coefficients (CRGGroupHighest.lowerIndex S.highest.index j) x/S.coefficients S.highest.index x)*
        iteratedDeriv j.val f (ray θ r)) := by simp only [neg_mul,Finset.sum_neg_distrib]
  rw [hsum]
  simpa only [CRGGroupHighest.lowerIndex,sub_eq_add_neg,add_comm] using eq_sub_of_add_eq hm

/-- The finite phase family is fixed by S before the solution or direction
is chosen. Every comparison hypothesis follows from source expansions and
the actual scalar equation with the ray jet bounds. -/
theorem Sector.ray_comparison
    {a : Fin (n+1) → ℂ → ℂ} (S : Sector a)
    (ha : ∀j,Differentiable ℂ (a j)) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (heq : ∀z : ℂ,∑j : Fin (n+1),a j z*iteratedDeriv j.val f z=0)
    (θ : ℝ) (hθ : θ∈S.angles)
    (hnon : ∀ᶠr : ℝ in atTop,f (ray θ r)≠0)
    (J : ℝ) (hJ : 0≤J)
    (hjet : ∀ᶠr : ℝ in atTop,∀j : Fin (n+1),
      ‖iteratedDeriv j.val f (ray θ r)/f (ray θ r)‖≤r^J) :
    ∃j : Fin S.highest.index.val,∃M : ℝ,0<M ∧ ∀ᶠr : ℝ in atTop,
      |Real.log ‖f (ray θ r)‖-(phaseOnRay (denominator S.highest S.denominator S.formal)
        (S.formal.normal.phase j) θ ⟨0,Nat.mul_pos S.formal.positive S.positive⟩ r).re|
          ≤M*Real.log r := by
  have hm := highest_positive_from_ray_bounds S.positive S.highest θ J (S.expansion θ hθ)
    hnon hjet heq
  let g := localOnRay S.highest S.denominator S.formal θ
  let ε := fun r : ℝ=>residual S.coefficients S.highest.index (localJet f S.denominator) (g r)
  have ht : Tendsto g atTop (rayFilter (direction (θ/S.denominator))) := S.localOnRay_tendsto θ
  have hcoord : ∀ᶠr : ℝ in atTop,originalPoint S.denominator (g r)=ray θ r := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact originalPoint_localOnRay S.highest S.denominator S.positive S.formal θ hr.le
  have hflat : ∀N : ℕ,ε =O[atTop] (fun r : ℝ=>(r^N)⁻¹) :=
    flat_on_physical_ray (flat_residual_from_ray_bounds S.positive S.highest θ J (S.expansion θ hθ) hjet)
      g ht θ hcoord
  have hC := ht.eventually (eventually_all.mpr (S.coefficients_continuous ha θ hθ))
  have hden := ht.eventually (eventually_ne_zero_of_nonzero_series
    (rayFilter_le_punctured (direction_ne_zero _)) (S.expansion θ hθ S.highest.index) S.highest.nonzero)
  have hzero : ∀ᶠx : ℂ in 𝓝[≠] (0:ℂ),x≠0 := self_mem_nhdsWithin
  have hx : ∀ᶠr : ℝ in atTop,g r≠0 := ht.eventually
    (hzero.filter_mono (rayFilter_le_punctured (direction_ne_zero _)))
  have htail : ∀ᶠr : ℝ in atTop,
      ContinuousAt ε r ∧ ContinuousAt (physicalCoefficient S.coefficients S.highest S.denominator S.formal θ) r ∧
      iteratedDeriv S.highest.index.val f (ray θ r)=
        (∑j : Fin S.highest.index.val,
          -(S.coefficients (CRGGroupHighest.lowerIndex S.highest.index j) (g r)/
            S.coefficients S.highest.index (g r))*iteratedDeriv j.val f (ray θ r))+ε r*f (ray θ r) := by
    filter_upwards [hC,hden,hx,hnon,hcoord,eventually_gt_atTop (0:ℝ)] with r hc hd hx hn hco hr
    have hg : ContinuousAt g r := localOnRay_continuousAt _ _ _ θ hr
    have hv : ∀j : Fin (n+1),ContinuousAt (localJet f S.denominator j) (g r) := by
      intro j
      exact localJet_continuousAt hf _ j hx (by simpa only [hco] using hn)
    refine ⟨(residual_continuousAt _ _ _ hc hd hv).comp hg,?_,?_⟩
    · have hcphys := ((companion_continuousAt _ _ hc hd).comp hg).const_smul
        (Complex.exp ((θ:ℂ)*Complex.I))
      change ContinuousAt (fun r=>Complex.exp ((θ:ℂ)*Complex.I) • companion S.coefficients S.highest (g r)) r at hcphys
      exact hcphys
    · exact reduced_physical_equation a S f heq θ hr hn hd
  obtain ⟨R,hR⟩ := eventually_atTop.mp htail
  apply CRGPuiseuxCompanionComparison.scalar_ray_comparison S.coefficients S.highest hm
    S.denominator S.positive S.formal θ (S.expansion θ hθ) (S.coefficients_continuous ha θ hθ)
    f hf ε R
    (fun r hr=>(hR r hr.le).1.continuousWithinAt) hflat
    (fun r hr=>(hR r hr.le).2.1.continuousWithinAt)
    (fun r hr=>(hR r hr.le).2.2) hnon 1 J zero_lt_one hJ
  filter_upwards [hjet] with r hr
  intro k hk hkm
  have hkn : k<n+1 := hkm.trans S.highest.index.isLt
  simpa only [one_mul] using hr ⟨k,hkn⟩

#print axioms localOnRay_continuousAt
#print axioms localJet_continuousAt
#print axioms residual_continuousAt
#print axioms companion_continuousAt
#print axioms reduced_physical_equation
#print axioms Sector.ray_comparison
end CRGPuiseuxSectorComparison
