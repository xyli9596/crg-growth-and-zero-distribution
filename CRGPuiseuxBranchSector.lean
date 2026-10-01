import CRGPuiseuxPolynomialCone
import CRGPuiseuxCoordinates
import CRGPolynomialKernelPuiseux

/-! Connected inverse-coordinate sectors and one fixed analytic Puiseux
root factor across an open angular cell. Compact angular subintervals
are patched through their common base ray. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace CRGPuiseuxBranchSector
open CRGNormalFormGoal CRGPhaseDirections CRGPuiseuxPolynomialCone
open CRGPuiseuxCoordinates WasowGlobalRayData WasowLaurentRayEquation
open CRGPolynomialKernel

def angularInverse (p : ℕ) (t : ℝ×ℝ) : ℂ := inverseRay (direction (t.1/p)) t.2

theorem angularInverse_continuousOn (p : ℕ) (a b R : ℝ) (hR : 1≤R) :
    ContinuousOn (angularInverse p) (uIcc a b ×ˢ Ioi R) := by
  have hdir : Continuous (fun t : ℝ×ℝ=>direction (t.1/p)) := by
    unfold direction
    fun_prop
  have hsnd : Continuous (fun t : ℝ×ℝ=>(t.2:ℂ)) := by fun_prop
  exact hdir.continuousOn.mul (hsnd.continuousOn.inv₀ (by
    intro t ht
    have hp : 0<t.2 := zero_lt_one.trans_le (hR.trans ht.2.le)
    exact_mod_cast hp.ne'))

/-- Any two directions with the same strict leading sign have a common
connected inverse-coordinate tail inside any prescribed analytic germ. -/
theorem exists_connected_tail_sector (Q : Polynomial ℂ) (hd : 0<Q.natDegree)
    (p : ℕ) (hp : 0<p) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0) (a b : ℝ)
    (hL : ∀θ∈uIcc a b,0<leadingReal Q.leadingCoeff Q.natDegree θ) :
    ∃R : ℝ,1≤R ∧ ∃S : Set ℂ,IsPreconnected S ∧
      (∀θ∈uIcc a b,∀s>R,inverseRay (direction (θ/p)) s∈S) ∧
      (∀x∈S,x≠0) ∧ (∀x∈S,0<(Q.eval (originalPoint p x)).re) ∧ ContinuousOn g S := by
  obtain ⟨Rq,hRq,hphase⟩ := uniform_positive_tail Q hd a b hL
  obtain ⟨δ,hδ,hgδ⟩ := hg.exists_ball_analyticOnNhd
  let R := max Rq (max 1 δ⁻¹)
  have hR : 1≤R := (le_max_left 1 δ⁻¹).trans (le_max_right _ _)
  let D := uIcc a b ×ˢ Ioi R
  let S := angularInverse p '' D
  have hS : IsPreconnected S := (isPreconnected_uIcc.prod isPreconnected_Ioi).image _
    (angularInverse_continuousOn p a b R hR)
  have hprops : ∀x∈S,x≠0 ∧ 0<(Q.eval (originalPoint p x)).re ∧ x∈Metric.ball 0 δ := by
    rintro x ⟨⟨θ,s⟩,ht,rfl⟩
    have hs1 : 1≤s := hR.trans ht.2.le
    have hsp : 0<s := zero_lt_one.trans_le hs1
    have hsR : Rq<s := (le_max_left _ _).trans_lt ht.2
    have hss : s≤s^p := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (by omega : 1≤p)
    have hsδ : δ⁻¹<s := (le_max_right 1 δ⁻¹).trans_lt ((le_max_right _ _).trans_lt ht.2)
    have hnorm : ‖angularInverse p (θ,s)‖=s⁻¹ := by
      simp [angularInverse,inverseRay,norm_mul,direction_norm,Complex.norm_real,Real.norm_of_nonneg hsp.le]
    have hsmall : s⁻¹<δ := (inv_lt_comm₀ hsp hδ).mpr hsδ
    refine ⟨mul_ne_zero (direction_ne_zero _) (inv_ne_zero (by exact_mod_cast hsp.ne')),?_,?_⟩
    · simpa only [angularInverse,originalPoint_inverseRay p hp] using
        hphase θ ht.1 (s^p) (hsR.trans_le hss)
    · simpa only [Metric.mem_ball,dist_zero_right,hnorm] using hsmall
  refine ⟨R,hR,S,hS,?_,?_,?_,?_⟩
  · intro θ hθ s hs
    exact ⟨(θ,s),⟨hθ,hs⟩,rfl⟩
  · exact fun x hx=>(hprops x hx).1
  · exact fun x hx=>(hprops x hx).2.1
  · exact hgδ.continuousOn.mono (fun x hx=>(hprops x hx).2.2)

/-- A single branch coefficient works for every ray of an open sign cell.
The required radius may depend on the direction, while the coefficient and
the analytic germ remain fixed throughout the cell. -/
theorem exists_fixed_principal_root_factor
    (Q : Polynomial ℂ) (hQ : Q≠0) (hd : 0<Q.natDegree)
    (p m : ℕ) (hp : 0<p) (hm : 0<m) (hdiv : m∣p*Q.natDegree)
    (a b : ℝ) (hab : a<b)
    (hL : ∀θ∈Ioo a b,0<leadingReal Q.leadingCoeff Q.natDegree θ) :
    ∃η : ℂ,η≠0 ∧ ∀θ∈Ioo a b,∀ᶠs : ℝ in atTop,
      (Q.eval (originalPoint p (inverseRay (direction (θ/p)) s)))^(-(m:ℂ)⁻¹)=
        η*inversePhaseRoot Q p m (inverseRay (direction (θ/p)) s) := by
  let θ₀ := (a+b)/2
  have hθ₀ : θ₀∈Ioo a b := by dsimp [θ₀];constructor <;>linarith
  have hg := analyticAt_inversePhaseRoot hQ hp m
  obtain ⟨R₀,hR₀,S₀,hS₀,hcover₀,hx₀,hs₀,hg₀⟩ := exists_connected_tail_sector Q hd p hp _ hg θ₀ θ₀
    (fun θ hθ=>hL θ (by
      have he : θ=θ₀ := by simpa only [uIcc_self,mem_singleton_iff] using hθ
      simpa only [he] using hθ₀))
  let x₀ := inverseRay (direction (θ₀/p)) (R₀+1)
  have hx₀mem : x₀∈S₀ := hcover₀ θ₀ (by simp) (R₀+1) (by linarith)
  let η := (Q.eval (originalPoint p x₀))^(-(m:ℂ)⁻¹)/inversePhaseRoot Q p m x₀
  have hfne : (Q.eval (originalPoint p x₀))^(-(m:ℂ)⁻¹)≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by
      intro he
      have hh := hs₀ x₀ hx₀mem
      rw [he] at hh
      norm_num at hh))
  have hgne : inversePhaseRoot Q p m x₀≠0 := by
    intro he
    have hh := inversePhaseRoot_pow hQ hm hdiv x₀
    rw [he,zero_pow hm.ne',inversePhase_eq p (hx₀ x₀ hx₀mem)] at hh
    have hval : Q.eval (originalPoint p x₀)≠0 := by
      intro hzero;have hh := hs₀ x₀ hx₀mem;rw [hzero] at hh;norm_num at hh
    exact (inv_ne_zero hval) hh.symm
  refine ⟨η,div_ne_zero hfne hgne,?_⟩
  intro θ hθ
  have hinter : uIcc θ₀ θ ⊆ Ioo a b := by
    exact ordConnected_Ioo.uIcc_subset hθ₀ hθ
  obtain ⟨R,hR,S,hS,hcover,hx,hs,hgS⟩ := exists_connected_tail_sector Q hd p hp _ hg θ₀ θ
    (fun φ hφ=>hL φ (hinter hφ))
  let s₁ := max R R₀+1
  let x₁ := inverseRay (direction (θ₀/p)) s₁
  have hx₁ : x₁∈S := hcover θ₀ left_mem_uIcc s₁ (by dsimp [s₁];linarith [le_max_left R R₀])
  have hx₁₀ : x₁∈S₀ := hcover₀ θ₀ (by simp) s₁ (by dsimp [s₁];linarith [le_max_right R R₀])
  have hbase : (Q.eval (originalPoint p x₁))^(-(m:ℂ)⁻¹)=η*inversePhaseRoot Q p m x₁ :=
    principal_inverse_root_eq hQ hm hdiv hS₀ hx₀ hs₀ hg₀ x₀ hx₀mem x₁ hx₁₀
  have hg₁ : inversePhaseRoot Q p m x₁≠0 := by
    intro he
    have hh := inversePhaseRoot_pow hQ hm hdiv x₁
    rw [he,zero_pow hm.ne',inversePhase_eq p (hx x₁ hx₁)] at hh
    have hval : Q.eval (originalPoint p x₁)≠0 := by
      intro hz;have hh := hs x₁ hx₁;rw [hz] at hh;norm_num at hh
    exact (inv_ne_zero hval) hh.symm
  filter_upwards [eventually_gt_atTop R] with s hsR
  have hxθ := hcover θ right_mem_uIcc s hsR
  have he := principal_inverse_root_eq hQ hm hdiv hS hx hs hgS x₁ hx₁ _ hxθ
  change (Q.eval (originalPoint p (inverseRay (direction (θ/p)) s)))^(-(m:ℂ)⁻¹)=
    ((Q.eval (originalPoint p x₁))^(-(m:ℂ)⁻¹)/inversePhaseRoot Q p m x₁)*
      inversePhaseRoot Q p m (inverseRay (direction (θ/p)) s) at he
  simpa only [hbase,mul_div_cancel_right₀ η hg₁] using he

#print axioms angularInverse_continuousOn
#print axioms exists_connected_tail_sector
#print axioms exists_fixed_principal_root_factor
end CRGPuiseuxBranchSector
