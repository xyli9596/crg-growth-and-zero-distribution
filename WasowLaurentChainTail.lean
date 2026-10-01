import WasowLaurentConjugatedTail
import WasowLaurentRayEquation

/-! The genuine inverse-ray Jacobian is retained in the conjugated remainder.
Polynomial regular factors are paid for before choosing the finite truncation. -/
set_option autoImplicit false
noncomputable section
open Filter Set Asymptotics MeasureTheory
open scoped Topology Matrix.Norms.Operator
namespace WasowLaurentChainTail
open WasowLaurentRayEquation WasowLaurentConjugatedTail
variable {m : ℕ}
local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin m → ℂ))
local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by simp_rw [Matrix.linfty_opNNNorm_def]; fun_prop

def conjugated (T S : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (f : ℂ → Matrix (Fin m) (Fin m) ℂ) (u : ℂ) (r : ℝ) :=
  S r * coefficientOnRay f u r * T r

theorem conjugated_eq (T S : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (f : ℂ → Matrix (Fin m) (Fin m) ℂ) (u : ℂ) :
    conjugated T S f u = fun r => chainFactor u r • weighted T S f u 0 r := by
  funext r
  simp only [conjugated, coefficientOnRay, inverseRay, weighted, pow_zero, one_smul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem chainFactor_continuousOn (u : ℂ) {a : ℝ} (ha : 1 ≤ a) :
    ContinuousOn (chainFactor u) (Ici a) := by
  apply continuousOn_const.div (Complex.continuous_ofReal.pow 2).continuousOn
  intro r hr
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le (ha.trans hr))))

/-- Both actual regular factors and the actual Jacobian preserve a genuine
inverse-square majorant on a common tail. -/
theorem exists_bound (T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (L : ℕ)
    (h : WasowPolynomialTail.Control T S L)
    {f : ℂ → Matrix (Fin m) (Fin m) ℂ} {u : ℂ} (hu : ‖u‖=1)
    (hf : ∀ᶠ z in 𝓝[≠] (0:ℂ), ContinuousAt f z)
    (hO : f =O[𝓝[≠] (0:ℂ)] (fun z:ℂ => ‖z‖^(2*L+2))) :
    ∃ C : ℝ, 0<C ∧ ∃ R : ℝ, 1≤R ∧
      ContinuousOn (conjugated T S f u) (Ici R) ∧
      ∀ r≥R, ‖conjugated T S f u r‖ ≤ C/r^2 := by
  obtain ⟨C,hC,R,hR,hc,hb⟩ := WasowLaurentConjugatedTail.exists_bound T S 0 L h hu hf
    (by simpa only [zero_add] using hO)
  refine ⟨C,hC,R,hR,?_,?_⟩
  · rw [conjugated_eq]
    exact (chainFactor_continuousOn u hR).smul hc
  · intro r hr
    rw [conjugated_eq, norm_smul, chainFactor_norm hu (zero_lt_one.trans_le (hR.trans hr))]
    have hrr : 1 ≤ r^2 := one_le_pow₀ (hR.trans hr)
    have hcf : 1/r^2 ≤ 1 := (div_le_one (by positivity)).mpr hrr
    calc
      _ ≤ 1 * ‖weighted T S f u 0 r‖ := mul_le_mul_of_nonneg_right hcf (norm_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hb r hr

/-- Arbitrarily small tails of the actual conjugated ray-ODE remainder. -/
theorem exists_small_tail (T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (L : ℕ)
    (h : WasowPolynomialTail.Control T S L)
    {f : ℂ → Matrix (Fin m) (Fin m) ℂ} {u : ℂ} (hu : ‖u‖=1)
    (hf : ∀ᶠ z in 𝓝[≠] (0:ℂ), ContinuousAt f z)
    (hO : f =O[𝓝[≠] (0:ℂ)] (fun z:ℂ => ‖z‖^(2*L+2)))
    (Rmin : ℝ) {ε:ℝ} (hε:0<ε) :
    ∃ R:ℝ, 1≤R ∧ Rmin≤R ∧
      ContinuousOn (conjugated T S f u) (Ici R) ∧
      IntegrableOn (conjugated T S f u) (Ici R) ∧
      (∫ r in Ici R, ‖conjugated T S f u r‖)<ε := by
  obtain ⟨C,_,a,ha,hc,hb⟩ := exists_bound T S L h hu hf hO
  have hi : IntegrableOn (conjugated T S f u) (Ici a) := by
    rw [IntegrableOn, ← restrict_Ioi_eq_restrict_Ici]
    have hm : IntegrableOn (fun r:ℝ => C*r^(-2:ℝ)) (Ioi a) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1)
        (zero_lt_one.trans_le ha)).const_mul C
    apply hm.mono' ((hc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [Real.rpow_neg (zero_le_one.trans (ha.trans hr.le)),
      Real.rpow_two, div_eq_mul_inv] using hb r hr.le
  let b := max a Rmin
  have hbi : IntegrableOn (conjugated T S f u) (Ioi b) :=
    hi.mono_set (by intro r hr; exact (le_max_left a Rmin).trans hr.le)
  obtain ⟨R,hR,hs⟩ := CRGProgress.exists_small_tail (conjugated T S f u) b ε hbi hε
  have haR : a≤R := (le_max_left _ _).trans hR
  refine ⟨R,ha.trans haR,(le_max_right _ _).trans hR,
    hc.mono (Ici_subset_Ici.mpr haR),hi.mono_set (Ici_subset_Ici.mpr haR),?_⟩
  rwa [integral_Ici_eq_integral_Ioi]

#print axioms conjugated_eq
#print axioms chainFactor_continuousOn
#print axioms exists_bound
#print axioms exists_small_tail
end WasowLaurentChainTail
