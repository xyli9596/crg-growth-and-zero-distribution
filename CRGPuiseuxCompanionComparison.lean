import CRGPuiseuxCoordinates
import CRGGeneralRayComparison
import CRGGeneralRayFlatTail
import CRGCompanion

/-! Scalar logarithmic comparison for the actual nonrational Puiseux
companion. The complete coefficient expansions construct the exact gauge;
the actual flat forcing supplies the perturbation tail. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology BigOperators Matrix.Norms.Operator
open Filter Set Asymptotics
namespace CRGPuiseuxCompanionComparison
open CRGNormalFormGoal CRGPuiseuxScalarReduction CRGPuiseuxCompanionExpansion
open CRGPuiseuxCompanionNormalForm CRGPuiseuxCoordinates
variable {n : ℕ} {A : Fin (n+1) → PowerSeries ℂ}

def zeroIndex {m : ℕ} (hm : 0<m) : Fin m := ⟨0,hm⟩
def lastIndex {m : ℕ} (hm : 0<m) : Fin m := ⟨m-1,by omega⟩

def jet {m : ℕ} (f : ℂ → ℂ) (θ r : ℝ) : Fin m → ℂ :=
  fun i => iteratedDeriv i.val f (ray θ r)

def perturbation {m : ℕ} (hm : 0<m) (θ : ℝ) (ε : ℝ → ℂ) (r : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if i=lastIndex hm ∧ j=zeroIndex hm then Complex.exp ((θ:ℂ)*Complex.I)*ε r else 0

theorem perturbation_mulVec {m : ℕ} (hm : 0<m) (θ r : ℝ) (ε : ℝ → ℂ) (x : Fin m → ℂ) :
    (perturbation hm θ ε r).mulVec x=
      Pi.single (lastIndex hm) (Complex.exp ((θ:ℂ)*Complex.I)*ε r*x (zeroIndex hm)) := by
  ext i
  by_cases hi : i=lastIndex hm
  · subst i
    simp [perturbation,Matrix.mulVec,dotProduct]
  · simp [perturbation,Matrix.mulVec,dotProduct,hi]

theorem norm_perturbation_le {m : ℕ} (hm : 0<m) (θ r : ℝ) (ε : ℝ → ℂ) :
    ‖perturbation hm θ ε r‖≤‖ε r‖ := by
  rw [←WasowGaugeAssembly.norm_toOperator]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖(perturbation hm θ ε r).mulVec x‖≤‖ε r‖*‖x‖
  rw [perturbation_mulVec]
  have hn : ‖Complex.exp ((θ:ℂ)*Complex.I)‖=1 := by simp [Complex.norm_exp,Complex.mul_re]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  by_cases hi : i=lastIndex hm
  · subst i
    simpa only [Pi.single_eq_same,norm_mul,hn,one_mul] using
      mul_le_mul_of_nonneg_left (norm_le_pi_norm x (zeroIndex hm)) (norm_nonneg (ε r))
  · simp only [Pi.single_apply,hi,ite_false,norm_zero]
    positivity

theorem perturbation_continuousOn {m : ℕ} (hm : 0<m) (θ R : ℝ) (ε : ℝ → ℂ)
    (hε : ContinuousOn ε (Ioi R)) : ContinuousOn (perturbation hm θ ε) (Ioi R) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  unfold perturbation
  split_ifs
  · exact continuousOn_const.mul hε
  · exact continuousOn_const

theorem perturbation_flat {m : ℕ} (hm : 0<m) (θ : ℝ) (ε : ℝ → ℂ)
    (hε : ∀N : ℕ,ε =O[atTop] (fun r : ℝ => (r^N)⁻¹)) :
    ∀N : ℕ,perturbation hm θ ε =O[atTop] (fun r : ℝ => (r^N)⁻¹) := by
  intro N
  have hP : perturbation hm θ ε =O[atTop] ε := by
    apply IsBigO.of_bound 1
    exact Filter.Eventually.of_forall (fun r => by
      simpa only [one_mul] using norm_perturbation_le hm θ r ε)
  exact hP.trans (hε N)

theorem companion_mulVec_last (C : Fin (n+1) → ℂ → ℂ) (H : Highest A)
    (hm : 0<H.index.val) (z : ℂ) (x : Fin H.index.val → ℂ) :
    (companion C H z).mulVec x (lastIndex hm)=
      ∑j:Fin H.index.val,-(C (CRGGroupHighest.lowerIndex H.index j) z/C H.index z)*x j := by
  have hi : (lastIndex hm).val+1=H.index.val := by dsimp [lastIndex];omega
  simp [companion,Matrix.mulVec,dotProduct,hi]

theorem companion_mulVec_not_last (C : Fin (n+1) → ℂ → ℂ) (H : Highest A)
    (z : ℂ) (x : Fin H.index.val → ℂ) (i : Fin H.index.val)
    (hi : i.val+1<H.index.val) :
    (companion C H z).mulVec x i=x ⟨i.val+1,hi⟩ := by
  let k : Fin H.index.val := ⟨i.val+1,hi⟩
  have hlast : i.val+1≠H.index.val := ne_of_lt hi
  have he : ∀j : Fin H.index.val,(i.val+1=j.val) ↔ j=k := by
    intro j
    constructor
    · intro h;exact Fin.ext h.symm
    · intro h;subst j;rfl
  simp [companion,Matrix.mulVec,dotProduct,hlast,he,k]

/-- The entire scalar solution's actual derivative jet solves the perturbed
nonrational companion with the exact physical direction factor. -/
theorem jet_hasDerivAt_of_scalar_equation
    (C : Fin (n+1) → ℂ → ℂ) (H : Highest A) (hm : 0<H.index.val)
    (p : ℕ) (W : FormalData H p) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (θ r : ℝ) (ε : ℝ → ℂ)
    (heq : iteratedDeriv H.index.val f (ray θ r)=
      (∑j:Fin H.index.val,-(C (CRGGroupHighest.lowerIndex H.index j) (localOnRay H p W θ r)/
        C H.index (localOnRay H p W θ r))*iteratedDeriv j.val f (ray θ r))+ε r*f (ray θ r)) :
    HasDerivAt (jet (m:=H.index.val) f θ)
      ((physicalCoefficient C H p W θ r+perturbation hm θ ε r).mulVec (jet f θ r)) r := by
  apply hasDerivAt_pi.mpr
  intro i
  have hd := (CRGCompanion.differentiable_iteratedDeriv f hf i.val (ray θ r)).hasDerivAt
  have hh := (hd.comp (r:ℂ) ((hasDerivAt_id (r:ℂ)).mul_const
    (Complex.exp ((θ:ℂ)*Complex.I)))).comp_ofReal
  have hd' : HasDerivAt (fun t => jet f θ t i)
      (Complex.exp ((θ:ℂ)*Complex.I)*iteratedDeriv (i.val+1) f (ray θ r)) r := by
    simpa only [jet,ray,iteratedDeriv_succ,Function.comp_apply,id_eq,one_mul,mul_one,mul_comm] using hh
  rw [Matrix.add_mulVec,perturbation_mulVec]
  by_cases hi : i.val+1=H.index.val
  · have hilast : i=lastIndex hm := Fin.ext (by dsimp [lastIndex];omega)
    have hlastval : (lastIndex hm).val+1=H.index.val := by dsimp [lastIndex];omega
    rw [hilast] at hd'
    rw [hilast,Pi.add_apply,Pi.single_eq_same]
    simp only [physicalCoefficient,Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul,
      companion_mulVec_last,jet,zeroIndex,iteratedDeriv_zero]
    simpa only [jet,hlastval,heq,mul_add,mul_assoc] using hd'
  · have hilt : i.val+1<H.index.val := by omega
    have hilast : i≠lastIndex hm := by
      intro h
      apply hi
      rw [h]
      dsimp [lastIndex]
      omega
    simp only [physicalCoefficient,Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul,Pi.add_apply,
      Pi.single_apply,hilast,ite_false,add_zero,companion_mulVec_not_last C H _ _ i hilt,jet]
    exact hd'

theorem jet_polynomial_comparison {m : ℕ} (hm : 0<m) (f : ℂ → ℂ) (θ r C K : ℝ)
    (hr : 1≤r) (hC : 0<C) (hK : 0≤K) (hf : f (ray θ r)≠0)
    (hb : ∀k : ℕ,1≤k→k<m→‖iteratedDeriv k f (ray θ r)/f (ray θ r)‖≤C*r^K) :
    ‖f (ray θ r)‖≤‖jet (m:=m) f θ r‖ ∧
    ‖jet (m:=m) f θ r‖≤(C+1)*r^K*‖f (ray θ r)‖ := by
  constructor
  · simpa only [jet,zeroIndex,iteratedDeriv_zero] using
      norm_le_pi_norm (jet (m:=m) f θ r) (zeroIndex hm)
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

/-- Actual scalar ray comparison with flat forcing. The finite family is
fixed by the coefficient data W before f, epsilon, or the ray is chosen. -/
theorem scalar_ray_comparison
    (C : Fin (n+1) → ℂ → ℂ) (H : Highest A) (hm : 0<H.index.val)
    (p : ℕ) (hp : 0<p) (W : FormalData H p) (θ : ℝ)
    (hC : ∀j,CRGAsymptoticCoefficientQuotient.CompleteExpansion
      (CRGAsymptoticCoefficientRayTail.rayFilter (WasowGlobalRayData.direction (θ/p))) (C j) (A j))
    (hcont : ∀j,∀ᶠ x in
      CRGAsymptoticCoefficientRayTail.rayFilter (WasowGlobalRayData.direction (θ/p)),ContinuousAt (C j) x)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (ε : ℝ → ℂ) (R : ℝ)
    (hε : ContinuousOn ε (Ioi R))
    (hflat : ∀N : ℕ,ε =O[atTop] (fun r : ℝ => (r^N)⁻¹))
    (hcoef : ContinuousOn (physicalCoefficient C H p W θ) (Ioi R))
    (heq : ∀r>R,iteratedDeriv H.index.val f (ray θ r)=
      (∑j:Fin H.index.val,-(C (CRGGroupHighest.lowerIndex H.index j) (localOnRay H p W θ r)/
        C H.index (localOnRay H p W θ r))*iteratedDeriv j.val f (ray θ r))+ε r*f (ray θ r))
    (hnon : ∀ᶠr in atTop,f (ray θ r)≠0)
    (D K : ℝ) (hD : 0<D) (hK : 0≤K)
    (hquot : ∀ᶠr in atTop,∀k : ℕ,1≤k→k<H.index.val→
      ‖iteratedDeriv k f (ray θ r)/f (ray θ r)‖≤D*r^K) :
    ∃j : Fin H.index.val,∃M : ℝ,0<M ∧ ∀ᶠr in atTop,
      |Real.log ‖f (ray θ r)‖-(phaseOnRay (denominator H p W) (W.normal.phase j) θ
        ⟨0,Nat.mul_pos W.positive hp⟩ r).re|≤M*Real.log r := by
  have hlocal := CRGAsymptoticCoefficientRayTail.rayFilter_le_punctured
    (WasowGlobalRayData.direction_ne_zero (θ/p))
  have ht := lifted_tendsto_local_ray W.denominator p W.positive hp θ
  obtain ⟨G⟩ := physical_ray_normal_form hlocal hC H p hp hcont W θ (by
    simpa only [denominator,Nat.cast_mul] using ht)
  have hP := perturbation_continuousOn hm θ R ε hε
  have hsmall := CRGGeneralRayFlatTail.smallConjugatedTails_of_flat_inverse_powers
    (physicalCoefficient C H p W θ) _ G (perturbation hm θ ε) R hP (perturbation_flat hm θ ε hflat)
  apply CRGGeneralRayComparison.ray_comparison (physicalCoefficient C H p W θ)
    (denominator H p W) (Nat.mul_pos W.positive hp) W.normal.phase θ ⟨0,Nat.mul_pos W.positive hp⟩ G
    (perturbation hm θ ε) hsmall R (hcoef.add hP) (jet f θ) (fun r => f (ray θ r))
    (fun r hr => jet_hasDerivAt_of_scalar_equation C H hm p W f hf θ r ε (heq r hr))
    hnon (D+1) K (by linarith) hK
  filter_upwards [hnon,hquot,eventually_ge_atTop (1:ℝ)] with r hfr hqr hr
  exact jet_polynomial_comparison hm f θ r D K hr hD hK hfr hqr

#print axioms perturbation_mulVec
#print axioms norm_perturbation_le
#print axioms perturbation_continuousOn
#print axioms perturbation_flat
#print axioms companion_mulVec_last
#print axioms companion_mulVec_not_last
#print axioms jet_hasDerivAt_of_scalar_equation
#print axioms jet_polynomial_comparison
#print axioms scalar_ray_comparison
end CRGPuiseuxCompanionComparison
