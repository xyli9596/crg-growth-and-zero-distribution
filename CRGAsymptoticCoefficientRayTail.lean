import CRGPuiseuxFiniteRealization
import WasowLaurentChainTail

/-! Sectorial filters, instead of whole punctured neighborhoods, suffice for
continuous integrable and arbitrarily small conjugated ray remainders. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Filter Set Asymptotics MeasureTheory
namespace CRGAsymptoticCoefficientRayTail
open WasowLaurentRayEquation
variable {m : ℕ}

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin m → ℂ))
local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by simp_rw [Matrix.linfty_opNNNorm_def]; fun_prop

/-- The filter of one actual inverse ray; a sector expansion restricts to it. -/
def rayFilter (u : ℂ) : Filter ℂ := Filter.map (inverseRay u) atTop

theorem rayFilter_le_punctured {u : ℂ} (hu : u≠0) :
    rayFilter u ≤ 𝓝[≠] (0:ℂ) := WasowLaurentTail.ray_tendsto_punctured hu

theorem power_tendsto_rayFilter {l : Filter ℂ} (u : ℂ) (p : ℕ)
    (ht : Tendsto (fun r : ℝ => (inverseRay u r)^p) atTop l) :
    Tendsto (fun z : ℂ => z^p) (rayFilter u) l := by
  simpa only [Tendsto,rayFilter,Filter.map_map,Function.comp_def] using ht

/-- Pointwise continuity along one ray and an estimate on its mapped filter
produce the genuine finite-radius bound. -/
theorem exists_ray_tail_bound {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} {N : ℕ} {u : ℂ} (hu : ‖u‖=1)
    (hf : ∀ᶠ r : ℝ in atTop, ContinuousAt f (inverseRay u r))
    (hO : f =O[rayFilter u] (fun z : ℂ => ‖z‖^N)) :
    ∃ C : ℝ, 0<C ∧ ∃ R : ℝ, 1≤R ∧
      ContinuousOn (fun r : ℝ => f (inverseRay u r)) (Ici R) ∧
      ∀ r : ℝ, R≤r → ‖f (inverseRay u r)‖≤C/r^N := by
  obtain ⟨C,hC,hb⟩ := (hO.comp_tendsto (tendsto_map : Tendsto (inverseRay u) atTop (rayFilter u))).exists_pos
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hb.bound.and hf)
  refine ⟨C,hC,max 1 R,le_max_left _ _,?_,?_⟩
  · intro r hr
    have hrpos : 0<r := zero_lt_one.trans_le ((le_max_left 1 R).trans hr)
    exact ((hR r ((le_max_right 1 R).trans hr)).2.comp
      (inverseRay_hasDerivAt u hrpos.ne').continuousAt).continuousWithinAt
  · intro r hr
    have hrnonneg : 0≤r := zero_le_one.trans ((le_max_left 1 R).trans hr)
    have hb' := (hR r ((le_max_right 1 R).trans hr)).1
    simpa only [Function.comp_apply,onRay,inverseRay,norm_pow,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),abs_of_nonneg (pow_nonneg hrnonneg _),norm_mul,hu,one_mul,norm_inv,
      Complex.norm_real,Real.norm_of_nonneg hrnonneg,inv_pow,div_eq_mul_inv] using hb'

/-- Polynomial regular factors and the true inverse-ray Jacobian preserve
an inverse-square integrable majorant. -/
theorem exists_conjugated_bound
    (T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (L : ℕ)
    (h : WasowPolynomialTail.Control T S L)
    {f : ℂ → Matrix (Fin m) (Fin m) ℂ} {u : ℂ} (hu : ‖u‖=1)
    (hf : ∀ᶠ r : ℝ in atTop, ContinuousAt f (inverseRay u r))
    (hO : f =O[rayFilter u] (fun z : ℂ => ‖z‖^(2*L+2))) :
    ∃ C : ℝ, 0<C ∧ ∃ R : ℝ, 1≤R ∧
      ContinuousOn (WasowLaurentChainTail.conjugated T S f u) (Ici R) ∧
      ∀ r≥R, ‖WasowLaurentChainTail.conjugated T S f u r‖≤C/r^2 := by
  obtain ⟨C,hC,R₀,hR₀,hc,hb⟩ := exists_ray_tail_bound hu hf hO
  let R := max h.R R₀
  have hR : h.R≤R := le_max_left _ _
  have hR' : R₀≤R := le_max_right _ _
  refine ⟨h.C^2*C,mul_pos (sq_pos_of_pos h.C_pos) hC,R,h.R_one.trans hR,?_,?_⟩
  · unfold WasowLaurentChainTail.conjugated coefficientOnRay
    exact ((h.S_continuous.mono (Ici_subset_Ici.mpr hR)).mul
      ((WasowLaurentChainTail.chainFactor_continuousOn u (h.R_one.trans hR)).smul
        (hc.mono (Ici_subset_Ici.mpr hR')))).mul
      (h.T_continuous.mono (Ici_subset_Ici.mpr hR))
  · intro r hr
    have hrpos : 0<r := zero_lt_one.trans_le ((h.R_one.trans hR).trans hr)
    rw [WasowLaurentChainTail.conjugated_eq,norm_smul,chainFactor_norm hu hrpos]
    have hrr : 1≤r^2 := one_le_pow₀ ((h.R_one.trans hR).trans hr)
    have hcf : 1/r^2≤1 := (div_le_one (by positivity)).mpr hrr
    calc
      _ ≤ 1*‖WasowLaurentConjugatedTail.weighted T S f u 0 r‖ :=
        mul_le_mul_of_nonneg_right hcf (norm_nonneg _)
      _ ≤ h.C^2*‖(r:ℂ)^(2*L) • f (inverseRay u r)‖ := by
        simpa only [one_mul,zero_add,WasowLaurentConjugatedTail.weighted,inverseRay,pow_zero,one_smul] using
          WasowPolynomialTail.conjugation_norm_bound T S L 0 h (hR.trans hr) (f (inverseRay u r))
      _ = h.C^2*(r^(2*L)*‖f (inverseRay u r)‖) := by
        rw [norm_smul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hrpos.le]
      _ ≤ h.C^2*(r^(2*L)*(C/r^(2*L+2))) := by
        gcongr
        exact hb r (hR'.trans hr)
      _ = _ := by
        rw [pow_add]
        field_simp

/-- Arbitrarily small L1 tails hold along every compatible ray, including
when the coefficient expansions diverge. -/
theorem exists_small_conjugated_tail
    (T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (L : ℕ)
    (h : WasowPolynomialTail.Control T S L)
    {f : ℂ → Matrix (Fin m) (Fin m) ℂ} {u : ℂ} (hu : ‖u‖=1)
    (hf : ∀ᶠ r : ℝ in atTop, ContinuousAt f (inverseRay u r))
    (hO : f =O[rayFilter u] (fun z : ℂ => ‖z‖^(2*L+2)))
    (Rmin : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ R : ℝ, 1≤R ∧ Rmin≤R ∧
      ContinuousOn (WasowLaurentChainTail.conjugated T S f u) (Ici R) ∧
      IntegrableOn (WasowLaurentChainTail.conjugated T S f u) (Ici R) ∧
      (∫ r in Ici R,‖WasowLaurentChainTail.conjugated T S f u r‖)<ε := by
  obtain ⟨C,_,a,ha,hc,hb⟩ := exists_conjugated_bound T S L h hu hf hO
  have hi : IntegrableOn (WasowLaurentChainTail.conjugated T S f u) (Ici a) := by
    rw [IntegrableOn,←restrict_Ioi_eq_restrict_Ici]
    have hm : IntegrableOn (fun r : ℝ => C*r^(-2:ℝ)) (Ioi a) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) (zero_lt_one.trans_le ha)).const_mul C
    apply hm.mono' ((hc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [Real.rpow_neg (zero_le_one.trans (ha.trans hr.le)),
      Real.rpow_two,div_eq_mul_inv] using hb r hr.le
  let b := max a Rmin
  have hbi : IntegrableOn (WasowLaurentChainTail.conjugated T S f u) (Ioi b) :=
    hi.mono_set (by intro r hr;exact (le_max_left a Rmin).trans hr.le)
  obtain ⟨R,hR,hs⟩ := CRGProgress.exists_small_tail
    (WasowLaurentChainTail.conjugated T S f u) b ε hbi hε
  have haR : a≤R := (le_max_left _ _).trans hR
  refine ⟨R,ha.trans haR,(le_max_right _ _).trans hR,
    hc.mono (Ici_subset_Ici.mpr haR),hi.mono_set (Ici_subset_Ici.mpr haR),?_⟩
  rwa [integral_Ici_eq_integral_Ioi]

#print axioms rayFilter_le_punctured
#print axioms power_tendsto_rayFilter
#print axioms exists_ray_tail_bound
#print axioms exists_conjugated_bound
#print axioms exists_small_conjugated_tail
end CRGAsymptoticCoefficientRayTail
