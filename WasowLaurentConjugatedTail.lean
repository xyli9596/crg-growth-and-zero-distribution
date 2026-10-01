import WasowLaurentTail
import WasowPolynomialTail

/-! High-order Laurent residuals stay integrably small after arbitrary fixed
polynomial weights and polynomially bounded regular-block gauges. -/
set_option autoImplicit false
noncomputable section
open Filter Set Asymptotics MeasureTheory
open scoped Topology Matrix.Norms.Operator
namespace WasowLaurentConjugatedTail
variable {m : ℕ}
local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin m → ℂ))
local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by simp_rw [Matrix.linfty_opNNNorm_def]; fun_prop

def weighted (T S : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (f : ℂ → Matrix (Fin m) (Fin m) ℂ) (u : ℂ) (d : ℕ) (r : ℝ) :=
  S r * ((r : ℂ)^d • f (u*(r:ℂ)⁻¹)) * T r

/-- The precise truncation budget pays for the scalar weight and both regular
factors, leaving an inverse-square bound. -/
theorem exists_bound (T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (d L : ℕ)
    (h : WasowPolynomialTail.Control T S L)
    {f : ℂ → Matrix (Fin m) (Fin m) ℂ} {u : ℂ} (hu : ‖u‖=1)
    (hf : ∀ᶠ z in 𝓝[≠] (0:ℂ), ContinuousAt f z)
    (hO : f =O[𝓝[≠] (0:ℂ)] (fun z:ℂ => ‖z‖^(d+2*L+2))) :
    ∃ C : ℝ, 0<C ∧ ∃ R : ℝ, 1≤R ∧
      ContinuousOn (weighted T S f u d) (Ici R) ∧
      ∀ r≥R, ‖weighted T S f u d r‖ ≤ C/r^2 := by
  obtain ⟨C,hC,R₀,hR₀,hc,hb⟩ := WasowLaurentTail.exists_ray_tail_bound hu hf hO
  let R := max h.R R₀
  have hR : h.R≤R := le_max_left _ _
  have hR' : R₀≤R := le_max_right _ _
  refine ⟨h.C^2*C, mul_pos (sq_pos_of_pos h.C_pos) hC,R,h.R_one.trans hR,?_,?_⟩
  · exact ((h.S_continuous.mono (Ici_subset_Ici.mpr hR)).mul
      ((Complex.continuous_ofReal.pow d).continuousOn.smul
        (hc.mono (Ici_subset_Ici.mpr hR')))).mul
      (h.T_continuous.mono (Ici_subset_Ici.mpr hR))
  · intro r hr
    have hrpos : 0<r := zero_lt_one.trans_le ((h.R_one.trans hR).trans hr)
    calc
      _ ≤ h.C^2 * ‖(r:ℂ)^(d+2*L) • f (u*(r:ℂ)⁻¹)‖ :=
        WasowPolynomialTail.conjugation_norm_bound T S L d h (hR.trans hr) _
      _ = h.C^2 * (r^(d+2*L) * ‖f (u*(r:ℂ)⁻¹)‖) := by
        rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
      _ ≤ h.C^2 * (r^(d+2*L) * (C/r^(d+2*L+2))) := by
        gcongr
        exact hb r (hR'.trans hr)
      _ = _ := by
        rw [pow_add]
        field_simp
        simp only [pow_add]
        ring

/-- Any prescribed small integral tail survives the regular normalization,
without requiring the formal gauge or its inverse to converge. -/
theorem exists_small_tail (T S : ℝ → Matrix (Fin m) (Fin m) ℂ) (d L : ℕ)
    (h : WasowPolynomialTail.Control T S L)
    {f : ℂ → Matrix (Fin m) (Fin m) ℂ} {u : ℂ} (hu : ‖u‖=1)
    (hf : ∀ᶠ z in 𝓝[≠] (0:ℂ), ContinuousAt f z)
    (hO : f =O[𝓝[≠] (0:ℂ)] (fun z:ℂ => ‖z‖^(d+2*L+2)))
    (Rmin : ℝ) {ε:ℝ} (hε:0<ε) :
    ∃ R:ℝ, 1≤R ∧ Rmin≤R ∧
      ContinuousOn (weighted T S f u d) (Ici R) ∧
      IntegrableOn (weighted T S f u d) (Ici R) ∧
      (∫ r in Ici R, ‖weighted T S f u d r‖)<ε := by
  obtain ⟨C,_,a,ha,hc,hb⟩ := exists_bound T S d L h hu hf hO
  have hi : IntegrableOn (weighted T S f u d) (Ici a) := by
    rw [IntegrableOn, ← restrict_Ioi_eq_restrict_Ici]
    have hm : IntegrableOn (fun r:ℝ => C*r^(-2:ℝ)) (Ioi a) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1)
        (zero_lt_one.trans_le ha)).const_mul C
    apply hm.mono' ((hc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [Real.rpow_neg (zero_le_one.trans (ha.trans hr.le)),
      Real.rpow_two, div_eq_mul_inv] using hb r hr.le
  let b := max a Rmin
  have hbi : IntegrableOn (weighted T S f u d) (Ioi b) :=
    hi.mono_set (by intro r hr; exact (le_max_left a Rmin).trans hr.le)
  obtain ⟨R,hR,hs⟩ := CRGProgress.exists_small_tail (weighted T S f u d) b ε hbi hε
  have haR : a≤R := (le_max_left _ _).trans hR
  refine ⟨R,ha.trans haR,(le_max_right _ _).trans hR,
    hc.mono (Ici_subset_Ici.mpr haR),hi.mono_set (Ici_subset_Ici.mpr haR),?_⟩
  rwa [integral_Ici_eq_integral_Ioi]

#print axioms exists_bound
#print axioms exists_small_tail
end WasowLaurentConjugatedTail
