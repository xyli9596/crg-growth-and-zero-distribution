import CRGGeneralRayComparison

/-! Flat errors in an actual differential equation remain integrable after
conjugation by a gauge and its inverse with polynomial growth. -/
set_option autoImplicit false
noncomputable section
open Filter Set Matrix Asymptotics MeasureTheory
open scoped Topology Matrix.Norms.Operator
namespace CRGGeneralRayFlatTail
open WasowLaurentExactAssembly
variable {m : ℕ}

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin m → ℂ))
local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by simp_rw [Matrix.linfty_opNNNorm_def]; fun_prop

theorem smallConjugatedTails_of_power
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (q : Fin m → ℝ → ℂ)
    (H : CRGGeneralRayGauge.RayGaugeWitness A q)
    (P : ℝ → Matrix (Fin m) (Fin m) ℂ) (a B : ℝ)
    (hP : ContinuousOn P (Ioi a)) (hB : 0<B)
    (hb : ∀ᶠ r : ℝ in atTop, ‖P r‖≤B*r^(-2*H.K-2)) :
    SmallConjugatedTails H.T H.S P := by
  obtain ⟨ht,hs⟩ := CRGGeneralRayComparison.gauge_continuousOn A q H
  obtain ⟨e,he⟩ := eventually_atTop.mp hb
  let d := max 1 (max (H.R+1) (max (a+1) e))
  have hd1 : 1≤d := le_max_left ..
  have hdH : H.R<d := (lt_add_one H.R).trans_le
    ((le_max_left _ _).trans (le_max_right _ _))
  have hda : a<d := (lt_add_one a).trans_le
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hde : e≤d := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hcont : ContinuousOn (fun r=>H.S r*P r*H.T r) (Ici d) :=
    ((hs.mono (fun _ hr=>hdH.trans_le hr)).mul
      (hP.mono (fun _ hr=>hda.trans_le hr))).mul (ht.mono (fun _ hr=>hdH.trans_le hr))
  let C := H.C*B*H.C
  have hC : 0<C := mul_pos (mul_pos H.C_pos hB) H.C_pos
  have hbound (r : ℝ) (hr : d<r) :
      ‖H.S r*P r*H.T r‖≤C*r^(-2:ℝ) := by
    have hrp : 0<r := (zero_lt_one.trans_le hd1).trans hr
    obtain ⟨htr,hsr⟩ := CRGGeneralRayComparison.gauge_operator_norm_bound A q H (hdH.trans hr)
    have hCr : 0≤H.C*r^H.K := mul_nonneg H.C_pos.le (Real.rpow_nonneg hrp.le _)
    calc
      _ ≤ (‖H.S r‖*‖P r‖)*‖H.T r‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ((H.C*r^H.K)*(B*r^(-2*H.K-2)))*(H.C*r^H.K) :=
        mul_le_mul (mul_le_mul hsr (he r (hde.trans hr.le)) (norm_nonneg _) hCr)
          htr (norm_nonneg _) (by positivity)
      _ = C*(r^(H.K+(-2*H.K-2)+H.K)) := by
        dsimp [C]
        rw [Real.rpow_add hrp,Real.rpow_add hrp]
        ring
      _ = _ := by congr 2; ring
  have hint : IntegrableOn (fun r=>H.S r*P r*H.T r) (Ioi d) := by
    have hm : IntegrableOn (fun r : ℝ=>C*r^(-2:ℝ)) (Ioi d) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1)
        (zero_lt_one.trans_le hd1)).const_mul C
    apply hm.mono' ((hcont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [Real.norm_eq_abs,abs_of_nonneg
      (mul_nonneg hC.le (Real.rpow_nonneg (zero_lt_one.trans_le (hd1.trans hr.le)).le _))]
      using hbound r hr
  intro Rmin ε hε
  let b := max d Rmin
  have hbi : IntegrableOn (fun r=>H.S r*P r*H.T r) (Ioi b) :=
    hint.mono_set (Ioi_subset_Ioi (le_max_left _ _))
  obtain ⟨R,hR,hi⟩ := CRGProgress.exists_small_tail _ b ε hbi hε
  have hdR : d≤R := (le_max_left _ _).trans hR
  refine ⟨R,hd1.trans hdR,(le_max_right _ _).trans hR,
    hcont.mono (Ici_subset_Ici.mpr hdR),?_,?_⟩
  · rw [IntegrableOn,←restrict_Ioi_eq_restrict_Ici]
    exact hint.mono_set (Ioi_subset_Ioi hdR)
  · rwa [integral_Ici_eq_integral_Ioi]

/-- Only the actual coefficient error is assumed flat; the gauge and its
inverse need not be bounded. Their polynomial losses are paid explicitly. -/
theorem smallConjugatedTails_of_flat
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (q : Fin m → ℝ → ℂ)
    (H : CRGGeneralRayGauge.RayGaugeWitness A q)
    (P : ℝ → Matrix (Fin m) (Fin m) ℂ) (a : ℝ)
    (hP : ContinuousOn P (Ioi a))
    (hflat : ∀N : ℕ, P =O[atTop] (fun r : ℝ=>r^(-(N:ℝ)))) :
    SmallConjugatedTails H.T H.S P := by
  obtain ⟨N,hN⟩ := exists_nat_gt (2*H.K+2)
  obtain ⟨B,hB,hb⟩ := (hflat N).exists_pos
  apply smallConjugatedTails_of_power A q H P a B hP hB
  filter_upwards [hb.bound,eventually_ge_atTop (1:ℝ)] with r hr hr1
  have hrp : 0<r := zero_lt_one.trans_le hr1
  have hh : ‖P r‖≤B*r^(-(N:ℝ)) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hrp.le _)] using hr
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)) hB.le)

theorem smallConjugatedTails_of_flat_inverse_powers
    (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (q : Fin m → ℝ → ℂ)
    (H : CRGGeneralRayGauge.RayGaugeWitness A q)
    (P : ℝ → Matrix (Fin m) (Fin m) ℂ) (a : ℝ)
    (hP : ContinuousOn P (Ioi a))
    (hflat : ∀N : ℕ, P =O[atTop] (fun r : ℝ=>(r^N)⁻¹)) :
    SmallConjugatedTails H.T H.S P := by
  apply smallConjugatedTails_of_flat A q H P a hP
  intro N
  apply (hflat N).congr' EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  simp [Real.rpow_neg hr, Real.rpow_natCast]

#print axioms smallConjugatedTails_of_power
#print axioms smallConjugatedTails_of_flat
#print axioms smallConjugatedTails_of_flat_inverse_powers
end CRGGeneralRayFlatTail
