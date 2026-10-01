import CRGPuiseuxScalarReduction
import CRGAsymptoticCoefficientMatrixTransfer
import CRGPuiseuxNormalForm

/-! The actual reduced scalar companion has the full Laurent expansion
determined by the original coefficient series. Its pole-cleared source feeds
the automatically constructed general formal and analytic normal form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Filter Asymptotics
namespace CRGPuiseuxCompanionExpansion
open CRGPuiseuxScalarReduction CRGAsymptoticCoefficientQuotient
open CRGAsymptoticCoefficientMatrixTransfer
variable {n : ℕ}

/-- Solved scalar companion, in the original differential coordinate. -/
def companion {A : Fin (n+1) → PowerSeries ℂ}
    (C : Fin (n+1) → ℂ → ℂ) (H : Highest A) (z : ℂ) :
    Matrix (Fin H.index.val) (Fin H.index.val) ℂ := fun i j =>
  if i.val+1=H.index.val then -(C (CRGGroupHighest.lowerIndex H.index j) z/C H.index z)
  else if i.val+1=j.val then 1 else 0

/-- Its finite pole is precisely the formal order of the chosen denominator. -/
def clearedCompanion {A : Fin (n+1) → PowerSeries ℂ}
    (C : Fin (n+1) → ℂ → ℂ) (H : Highest A) (z : ℂ) :
    Matrix (Fin H.index.val) (Fin H.index.val) ℂ := fun i j =>
  if i.val+1=H.index.val then -(z^(A H.index).order.toNat*
    (C (CRGGroupHighest.lowerIndex H.index j) z/C H.index z))
  else if i.val+1=j.val then z^(A H.index).order.toNat else 0

/-- Every exact matrix entry of the fixed formal coefficient. -/
def entrySeries {A : Fin (n+1) → PowerSeries ℂ} (H : Highest A)
    (i j : Fin H.index.val) : PowerSeries ℂ :=
  if i.val+1=H.index.val then
    -(A (CRGGroupHighest.lowerIndex H.index j)*(A H.index).divXPowOrder⁻¹)
  else if i.val+1=j.val then PowerSeries.X^(A H.index).order.toNat else 0

def companionSeries {A : Fin (n+1) → PowerSeries ℂ} (H : Highest A) :
    PowerSeries (Matrix (Fin H.index.val) (Fin H.index.val) ℂ) :=
  PowerSeries.mk (fun k i j => PowerSeries.coeff k (entrySeries H i j))

theorem entry_companionSeries {A : Fin (n+1) → PowerSeries ℂ} (H : Highest A)
    (i j : Fin H.index.val) : WasowPowerSeries.entry (companionSeries H) i j=entrySeries H i j := by
  ext k
  simp [WasowPowerSeries.coeff_entry,companionSeries]

theorem clearedCompanion_eq {A : Fin (n+1) → PowerSeries ℂ}
    (C : Fin (n+1) → ℂ → ℂ) (H : Highest A) (z : ℂ) :
    clearedCompanion C H z = z^(A H.index).order.toNat • companion C H z := by
  ext i j
  simp only [clearedCompanion,companion,Matrix.smul_apply,smul_eq_mul]
  split_ifs <;> ring

/-- Actual division produces exactly the formal companion coefficients.
Neither a companion expansion nor its matrix norm bound is assumed. -/
theorem clearedCompanion_completeExpansion
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0:ℂ))
    {C : Fin (n+1) → ℂ → ℂ} {A : Fin (n+1) → PowerSeries ℂ}
    (hC : ∀j,CompleteExpansion l (C j) (A j)) (H : Highest A) :
    CRGAsymptoticCoefficientCompleteExpansion.CompleteExpansion l
      (clearedCompanion C H) (companionSeries H) := by
  apply completeExpansion_of_entries
  intro i j
  rw [entry_companionSeries]
  by_cases hi : i.val+1=H.index.val
  · simp only [clearedCompanion,entrySeries,if_pos hi]
    exact completeExpansion_neg
      (laurentExpansion_quotient hl (hC (CRGGroupHighest.lowerIndex H.index j))
        (hC H.index) H.nonzero)
  · by_cases hij : i.val+1=j.val
    · simp only [clearedCompanion,entrySeries,if_neg hi,if_pos hij]
      have hp := polynomial_completeExpansion (hl.trans nhdsWithin_le_nhds)
        ((Polynomial.X:Polynomial ℂ)^(A H.index).order.toNat)
      simpa only [Polynomial.eval_pow,Polynomial.eval_X,Polynomial.coe_pow,Polynomial.coe_X] using hp
    · simp only [clearedCompanion,entrySeries,if_neg hi,if_neg hij]
      exact (flat_iff_zero_expansion _ _).mp (fun N => isBigO_zero _ _)

/-- The true sectorial companion remains continuous once its leading
coefficient has become nonzero; its asymptotic unit need not extend to zero. -/
theorem clearedCompanion_eventually_continuousAt
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0:ℂ))
    {C : Fin (n+1) → ℂ → ℂ} {A : Fin (n+1) → PowerSeries ℂ}
    (hC : ∀j,CompleteExpansion l (C j) (A j)) (H : Highest A)
    (hcont : ∀j,∀ᶠ z in l,ContinuousAt (C j) z) :
    ∀ᶠ z in l,ContinuousAt (clearedCompanion C H) z := by
  have hc : ∀ᶠ z in l,∀j,ContinuousAt (C j) z := eventually_all.mpr hcont
  filter_upwards [hc,eventually_ne_zero_of_nonzero_series hl (hC H.index) H.nonzero] with z hz hden
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  unfold clearedCompanion
  split_ifs
  · exact ((continuousAt_id.pow _).mul ((hz _).div (hz _) hden)).neg
  · exact continuousAt_id.pow _
  · exact continuousAt_const

/-- The original Puiseux denominator multiplies the true differential
coefficient numerator after changing coordinate x=z^(-1/p). -/
def normalizedSource {A : Fin (n+1) → PowerSeries ℂ}
    (C : Fin (n+1) → ℂ → ℂ) (H : Highest A) (p : ℕ) :
    ℂ → Matrix (Fin H.index.val) (Fin H.index.val) ℂ :=
  fun z => (p:ℂ) • clearedCompanion C H z

def normalizedSeries {A : Fin (n+1) → PowerSeries ℂ} (H : Highest A) (p : ℕ) :=
  (p:ℂ) • companionSeries H

theorem normalizedSource_completeExpansion
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0:ℂ))
    {C : Fin (n+1) → ℂ → ℂ} {A : Fin (n+1) → PowerSeries ℂ}
    (hC : ∀j,CompleteExpansion l (C j) (A j)) (H : Highest A) (p : ℕ) :
    CRGAsymptoticCoefficientCompleteExpansion.CompleteExpansion l
      (normalizedSource C H p) (normalizedSeries H p) := by
  have he := CRGAsymptoticCoefficientPullback.completeExpansion_monomial
    (hl.trans nhdsWithin_le_nhds) (clearedCompanion_completeExpansion hl hC H) (p:ℂ) 0
  unfold normalizedSource normalizedSeries
  simpa only [pow_zero,mul_one,one_mul] using he

theorem normalizedSource_eventually_continuousAt
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0:ℂ))
    {C : Fin (n+1) → ℂ → ℂ} {A : Fin (n+1) → PowerSeries ℂ}
    (hC : ∀j,CompleteExpansion l (C j) (A j)) (H : Highest A) (p : ℕ)
    (hcont : ∀j,∀ᶠ z in l,ContinuousAt (C j) z) :
    ∀ᶠ z in l,ContinuousAt (normalizedSource C H p) z := by
  filter_upwards [clearedCompanion_eventually_continuousAt hl hC H hcont] with z hz
  exact (continuousAt_const : ContinuousAt (fun _ : ℂ => (p:ℂ)) z).smul hz

/-- The actual scalar coefficients alone construct a single fixed finite
formal phase family and an exact general gauge on each compatible lifted ray. -/
theorem exists_companion_normal_form
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0:ℂ))
    {C : Fin (n+1) → ℂ → ℂ} {A : Fin (n+1) → PowerSeries ℂ}
    (hC : ∀j,CompleteExpansion l (C j) (A j)) (H : Highest A)
    (p : ℕ) (_hp : 0<p) (hcont : ∀j,∀ᶠ z in l,ContinuousAt (C j) z) :
    ∃ W : WasowGlobalFormalSquare.SquareRealization
        (WasowLaurentGauge.differentialCoefficient (p+(A H.index).order.toNat-1) (normalizedSeries H p)),
      (∀i,(W.normal.phase i).coeff 0=0) ∧
      ∀φ : ℝ,
        Tendsto (fun r : ℝ =>
          (WasowLaurentRayEquation.inverseRay (WasowGlobalRayData.direction φ) r)^W.denominator) atTop l →
        Nonempty (CRGGeneralRayGauge.RayGaugeWitness
          (CRGPuiseuxRayData.liftedCoefficient (normalizedSource C H p) W φ)
          (fun i => CRGNormalFormGoal.phaseOnRay 1 (W.normal.phase i) φ 0)) := by
  exact CRGPuiseuxNormalForm.exists_fixed_lifted_phase_normal_form
    (normalizedSource_completeExpansion hl hC H p)
    (normalizedSource_eventually_continuousAt hl hC H p hcont) (p+(A H.index).order.toNat-1)

#print axioms entry_companionSeries
#print axioms clearedCompanion_eq
#print axioms clearedCompanion_completeExpansion
#print axioms clearedCompanion_eventually_continuousAt
#print axioms normalizedSource_completeExpansion
#print axioms normalizedSource_eventually_continuousAt
#print axioms exists_companion_normal_form
end CRGPuiseuxCompanionExpansion
