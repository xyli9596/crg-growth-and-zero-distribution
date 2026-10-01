import LevinGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-!
# Growth definitions used by the main theorem

`UpperOrder` is the usual eventual maximum-modulus upper order condition,
written without a maximum over circles. `IsOrder` says that this upper order
is minimal among nonnegative upper orders. `FinitePositiveType` records
finite exponential type and a positive type witnessed at arbitrarily large
points. These are definitions, not analytic conclusions.
-/

open Filter
open scoped Topology

namespace CRGOrder

/-- Every exponent strictly above `ρ` bounds the logarithmic growth. -/
def UpperOrder (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ z : ℂ,
    R ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (‖z‖ ^ (ρ + δ))

/-- Finite order, with a specified nonnegative upper exponent available. -/
def FiniteOrder (f : ℂ → ℂ) : Prop :=
  ∃ ρ : ℝ, 0 ≤ ρ ∧ UpperOrder f ρ

/-- The nonnegative order is the least nonnegative upper order. -/
def IsOrder (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ UpperOrder f ρ ∧
    ∀ σ : ℝ, 0 ≤ σ → UpperOrder f σ → ρ ≤ σ

/-- Increasing the upper order preserves the defining estimates. -/
theorem UpperOrder.mono {f : ℂ → ℂ} {ρ σ : ℝ}
    (h : UpperOrder f ρ) (hρσ : ρ ≤ σ) : UpperOrder f σ := by
  intro δ hδ
  obtain ⟨R, hR⟩ := h δ hδ
  refine ⟨max R 1, fun z hz => (hR z ((le_max_left _ _).trans hz)).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans hz)
    (by linarith)

/-- A fixed multiplicative type constant can be absorbed into any larger power. -/
theorem eventually_mul_rpow_le {ρ σ C : ℝ} (h : ρ < σ) :
    ∀ᶠ r : ℝ in atTop, C * r ^ ρ ≤ r ^ σ := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr h)).eventually (eventually_ge_atTop C)
  filter_upwards [ht, eventually_gt_atTop (0 : ℝ)] with r hr hrpos
  calc
    C * r ^ ρ ≤ r ^ (σ - ρ) * r ^ ρ :=
      mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hrpos.le _)
    _ = r ^ σ := by rw [← Real.rpow_add hrpos]; congr 1; ring

/-- A finite exponential type bound yields the corresponding upper order. -/
theorem upperOrder_of_finiteType {f : ℂ → ℂ} {ρ C R : ℝ}
    (h : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (C * ‖z‖ ^ ρ)) :
    UpperOrder f ρ := by
  intro δ hδ
  obtain ⟨S, hS⟩ := eventually_atTop.1 (eventually_mul_rpow_le (C := C)
    (show ρ < ρ + δ by linarith))
  refine ⟨max R S, fun z hz => (h z ((le_max_left _ _).trans hz)).trans ?_⟩
  exact Real.exp_le_exp.mpr (hS ‖z‖ ((le_max_right _ _).trans hz))

/-- Positive type precludes every smaller upper order. -/
theorem le_upperOrder_of_positiveType {f : ℂ → ℂ} {ρ σ : ℝ}
    (h : ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∃ z : ℂ,
      max R 1 ≤ ‖z‖ ∧ Real.exp (c * ‖z‖ ^ ρ) ≤ ‖f z‖)
    (hs : UpperOrder f σ) : ρ ≤ σ := by
  by_contra hle
  have hσρ : σ < ρ := lt_of_not_ge hle
  obtain ⟨c, hc, hlow⟩ := h
  obtain ⟨R, hR⟩ := hs ((ρ - σ) / 2) (by linarith)
  have hpow := eventually_mul_rpow_le (C := 2 / c)
    (show σ + (ρ - σ) / 2 < ρ by linarith)
  obtain ⟨S, hS⟩ := eventually_atTop.1 hpow
  obtain ⟨z, hz, hzl⟩ := hlow (max R S)
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hz)
  have hub := hR z ((le_max_left _ _).trans ((le_max_left _ _).trans hz))
  have hpow' := hS ‖z‖ ((le_max_right _ _).trans ((le_max_left _ _).trans hz))
  have hcompare := Real.exp_le_exp.mp (hzl.trans hub)
  have hmul := mul_le_mul_of_nonneg_left hpow' hc.le
  have htwo : c * (2 / c * ‖z‖ ^ (σ + (ρ - σ) / 2)) =
      2 * ‖z‖ ^ (σ + (ρ - σ) / 2) := by field_simp
  rw [htwo] at hmul
  have hp : 0 < ‖z‖ ^ (σ + (ρ - σ) / 2) := Real.rpow_pos_of_pos hzpos _
  linarith

/-- The growth notion already used by Levin has exactly the asserted order. -/
theorem finitePositiveType_isOrder {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : LevinGrowth.FinitePositiveType f ρ) : IsOrder f ρ := by
  obtain ⟨C, _, R, _, hR⟩ := h.1
  exact ⟨hρ, upperOrder_of_finiteType hR,
    fun _ _ hs => le_upperOrder_of_positiveType h.2 hs⟩

#print axioms UpperOrder.mono
#print axioms eventually_mul_rpow_le
#print axioms upperOrder_of_finiteType
#print axioms le_upperOrder_of_positiveType
#print axioms finitePositiveType_isOrder

end CRGOrder
