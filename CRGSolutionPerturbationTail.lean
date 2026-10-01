import WasowLaurentExactAssemblyData
import CRGProgress

/-! Exponential perturbations remain integrable after the actual two-sided
polynomial gauge. The small continuous tails are constructed, not assumed. -/
set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator
namespace CRGSolutionPerturbationTail
open CRGNormalFormGoal WasowLaurentExactAssembly WasowGaugeAssembly
variable {m : ℕ}

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin m → ℂ))

local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by
    simp_rw [Matrix.linfty_opNNNorm_def]
    fun_prop

theorem gauge_continuousOn (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ)
    (q : Fin m → ℝ → ℂ) (H : RayGaugeWitness A θ q) :
    ContinuousOn H.T (Ioi H.R) ∧ ContinuousOn H.S (Ioi H.R) := by
  have ht : ContinuousOn H.T (Ioi H.R) := by
    intro r hr
    exact (continuousAt_pi.mpr (fun i=>continuousAt_pi.mpr
      (fun j=>(H.T_derivative r hr i j).continuousAt))).continuousWithinAt
  refine ⟨ht,?_⟩
  have hi : ContinuousOn (fun r=>(H.T r)⁻¹) (Ioi H.R) := by
    intro r hr
    apply (continuousAt_matrix_inv (H.T r) ?_).comp_continuousWithinAt (ht r hr)
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (Matrix.det_ne_zero_of_left_inverse (H.inverse_left r hr))
  apply hi.congr
  intro r hr
  exact (Matrix.inv_eq_left_inv (H.inverse_left r hr)).symm

theorem gauge_operator_norm_bound (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ)
    (q : Fin m → ℝ → ℂ) (H : RayGaugeWitness A θ q) {r : ℝ} (hr : H.R<r) :
    ‖H.T r‖≤H.C*r^H.K ∧ ‖H.S r‖≤H.C*r^H.K := by
  have hnon : 0≤H.C*r^H.K := mul_nonneg H.C_pos.le
    (Real.rpow_nonneg (H.R_pos.trans hr).le _)
  constructor
  · rw [←norm_toOperator]
    exact ContinuousLinearMap.opNorm_le_bound _ hnon (H.T_bound r hr)
  · rw [←norm_toOperator]
    exact ContinuousLinearMap.opNorm_le_bound _ hnon (H.S_bound r hr)

/-- An actual continuous exponentially decreasing matrix perturbation supplies
all the analytic hypotheses of the mixed Volterra construction. -/
theorem smallConjugatedTails_of_exponential
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ)
    (q : Fin m → ℝ → ℂ) (H : RayGaugeWitness A θ q)
    (P : ℝ → Matrix (Fin m) (Fin m) ℂ) (a B J c : ℝ)
    (hP : ContinuousOn P (Ioi a)) (hB : 0<B) (hJ : 0≤J) (hc : 0<c)
    (hb : ∀r>a, ‖P r‖≤B*(r^J*Real.exp (-c*r))) :
    SmallConjugatedTails H.T H.S P := by
  obtain ⟨ht,hs⟩ := gauge_continuousOn A θ q H
  intro Rmin ε hε
  let d := max 1 (max (H.R+1) (max (a+1) Rmin))
  have hd1 : 1≤d := le_max_left ..
  have hdH : H.R<d := (lt_add_one H.R).trans_le ((le_max_left _ _).trans (le_max_right _ _))
  have hda : a<d := (lt_add_one a).trans_le
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hdmin : Rmin≤d := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hcont : ContinuousOn (fun r=>H.S r*P r*H.T r) (Ici d) :=
    ((hs.mono (fun _ hr=>hdH.trans_le hr)).mul
      (hP.mono (fun _ hr=>hda.trans_le hr))).mul (ht.mono (fun _ hr=>hdH.trans_le hr))
  let K := H.K+J+H.K
  let C := H.C*B*H.C
  have hK : -1<K := by dsimp [K]; have := H.K_nonneg; linarith
  have hbound (r:ℝ) (hr:d<r) :
      ‖H.S r*P r*H.T r‖≤C*(r^K*Real.exp (-c*r)) := by
    have hrp : 0<r := (zero_lt_one.trans_le hd1).trans hr
    have hHr : H.R<r := hdH.trans hr
    obtain ⟨htr,hsr⟩ := gauge_operator_norm_bound A θ q H hHr
    have hCr : 0≤H.C*r^H.K := mul_nonneg H.C_pos.le (Real.rpow_nonneg hrp.le _)
    calc
      _ ≤ (‖H.S r‖*‖P r‖)*‖H.T r‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ((H.C*r^H.K)*(B*(r^J*Real.exp (-c*r))))*(H.C*r^H.K) :=
        mul_le_mul (mul_le_mul hsr (hb r (hda.trans hr)) (norm_nonneg _) hCr)
          htr (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [C,K]; rw [Real.rpow_add hrp,Real.rpow_add hrp]; ring
  have hint : IntegrableOn (fun r=>H.S r*P r*H.T r) (Ioi d) := by
    apply CRGProgress.perturbation_integrable _ K c C d hK hc (by linarith) 
      ((hcont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun r hr=>hbound r hr)
  have hlim : Tendsto (fun b:ℝ=>∫r in Ici b,‖H.S r*P r*H.T r‖) atTop (𝓝 0) :=
    tendsto_integral_Ici_zero tendsto_id
  obtain ⟨e,he⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  let b := max d e
  have hdb : d≤b := le_max_left ..
  refine ⟨b,hd1.trans hdb,hdmin.trans hdb,hcont.mono (Ici_subset_Ici.mpr hdb),?_,
    he b (le_max_right ..)⟩
  rw [IntegrableOn, ←restrict_Ioi_eq_restrict_Ici]
  exact hint.mono_set (Ioi_subset_Ioi hdb)

#print axioms gauge_continuousOn
#print axioms gauge_operator_norm_bound
#print axioms smallConjugatedTails_of_exponential
end CRGSolutionPerturbationTail
