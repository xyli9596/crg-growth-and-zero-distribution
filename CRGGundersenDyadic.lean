import GundersenGrowth
import CRGAngularShadow
import Mathlib.Analysis.SpecificLimits.Normed

/-! Genuine angular logarithmic derivative estimates from the actual Cartan
disks at dyadic scales. The angular exception is Lebesgue null. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace CRGGundersenDyadic
open CRGNormalFormGoal

theorem rpow_near_bound {r R : ℝ} (hr : 0<r) (h1 : r≤R) (h2 : R≤2*r) (a : ℝ) :
    R^a ≤ 2^|a| * r^a := by
  by_cases ha : 0≤a
  · calc
      R^a ≤ (2*r)^a := Real.rpow_le_rpow (hr.le.trans h1) h2 ha
      _ = 2^|a| * r^a := by rw [Real.mul_rpow (by norm_num) hr.le, abs_of_nonneg ha]
  · have ha' : a≤0 := (not_le.mp ha).le
    calc
      R^a ≤ r^a := Real.rpow_le_rpow_of_nonpos hr h1 ha'
      _ ≤ 2^|a| * r^a := le_mul_of_one_le_left (Real.rpow_nonneg hr.le _)
        (Real.one_le_rpow (by norm_num) (abs_nonneg _))

theorem dyadic_budget_summable {A η : ℝ} (hA : 0<A) (hη : 0<η) :
    Summable (fun n : ℕ => (A*(2:ℝ)^(n+1))^(-η)) := by
  have hq0 : 0≤(2:ℝ)^(-η) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2:ℝ)^(-η)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hη)
  have hh := (summable_geometric_of_lt_one hq0 hq1).comp_injective Nat.succ_injective
  have hc := hh.mul_left (A^(-η))
  apply hc.congr
  intro n
  dsimp [Function.comp_def]
  rw [Real.mul_rpow hA.le (by positivity)]
  congr 1
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),
    mul_comm ((n+1:ℕ):ℝ), Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]

theorem ae_normalized_logDeriv_bound {f : ℂ→ℂ} {ρ δ : ℝ}
    (hf : Differentiable ℂ f) (hf0 : f 0=1) (hρ : 0≤ρ) (hδ : 0<δ)
    (ho : CRGOrder.UpperOrder f ρ) :
    ∀ᵐ θ : ℝ, ∀ᶠ r : ℝ in atTop,
      f (ray θ r)≠0 ∧ ‖logDeriv f (ray θ r)‖≤r^(ρ-1+δ) := by
  have hd := GundersenGrowth.eventually_disks_logDeriv_bound hf hf0 hρ
    (show 0<δ/2 by linarith) ho
  obtain ⟨B,hB⟩ := eventually_atTop.mp hd
  let A := max B 1
  have hA : 0<A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let R : ℕ→ℝ := fun n => A*(2:ℝ)^(n+1)
  let L : ℕ→ℝ := fun n => A*(2:ℝ)^n
  have hR (n : ℕ) : 0<R n := by dsimp [R]; positivity
  have hL (n : ℕ) : 0<L n := by dsimp [L]; positivity
  have hLR (n : ℕ) : R n=2*L n := by dsimp [R,L]; rw [pow_succ]; ring
  have hall (n : ℕ) := hB (R n) (show B≤R n from
    (le_max_left _ _).trans (by dsimp [R]; nlinarith [one_le_pow₀ (n := n+1) (by norm_num : (1:ℝ)≤2)]))
  choose m c s hs hsum hpoint using hall
  have hbudget : (∑' n, ENNReal.ofReal (4*Real.pi*(∑i,s n i)/L n))≠⊤ := by
    have hnum (n : ℕ) : 4*Real.pi*(∑i,s n i)/L n ≤
        (40*Real.pi)* (R n)^(-(δ/2/4)) := by
      calc
        _ ≤ 4*Real.pi*(5*(R n)^(1-δ/2/4))/L n :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hsum n) (by positivity)) (hL n).le
        _ = _ := by
          rw [Real.rpow_sub (hR n), Real.rpow_one,
            Real.rpow_neg (hR n).le, hLR n]
          field_simp [(hL n).ne']
          ring
    have hsumm := (dyadic_budget_summable hA (show 0<δ/2/4 by linarith)).mul_left
      (40*Real.pi)
    exact ne_top_of_le_ne_top hsumm.tsum_ofReal_ne_top
      (ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_le_ofReal (hnum n)))
  have hav := CRGAngularShadow.ae_eventually_avoid m c s L hL
    (fun n i => (hs n i).le) hbudget
  filter_upwards [hav] with θ hθ
  obtain ⟨N,hN⟩ := eventually_atTop.mp hθ
  have habs := CRGOrder.eventually_mul_rpow_le
    (C := (2:ℝ)^|ρ-1+δ/2|) (show ρ-1+δ/2<ρ-1+δ by linarith)
  filter_upwards [habs, eventually_ge_atTop (L (N+1))] with r hfin hr
  have h1 : (1:ℝ)≤r/A := by
    apply (le_div_iff₀ hA).mpr
    dsimp [L] at hr
    nlinarith [one_le_pow₀ (n := N+1) (by norm_num : (1:ℝ)≤2)]
  obtain ⟨n,hn1,hn2⟩ := exists_nat_pow_near h1 (show (1:ℝ)<2 by norm_num)
  have hnr : L n≤r := by
    dsimp [L]
    nlinarith [(le_div_iff₀ hA).mp hn1]
  have hrn : r<R n := by
    dsimp [R]
    nlinarith [(div_lt_iff₀ hA).mp hn2]
  have hnN : N≤n := by
    by_contra h
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show n+1≤N+1 by omega)
    dsimp [L,R] at *
    nlinarith
  have hr0 : 0<r := (hL n).trans_le hnr
  have hz : ray θ r∈closedBall 0 (R n) := by
    simp only [mem_closedBall_zero_iff]
    simpa [ray, Complex.norm_exp, Real.norm_of_nonneg hr0.le] using hrn.le
  obtain ⟨hnz,hval⟩ := hpoint n (ray θ r) hz (hN n hnN r hnr)
  refine ⟨hnz,hval.trans ((rpow_near_bound hr0 hrn.le ?_ _).trans hfin)⟩
  rw [hLR]
  linarith

#print axioms rpow_near_bound
#print axioms dyadic_budget_summable
#print axioms ae_normalized_logDeriv_bound
end CRGGundersenDyadic
