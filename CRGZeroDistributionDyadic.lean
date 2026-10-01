import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! A vanishing annular density gives a vanishing full radial density.
The recurrence counts every scale, including the bounded inner region. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology
namespace CRGZeroDistributionDyadic

theorem dyadic_bound {N A : ℝ → ℝ} {ρ R δ : ℝ}
    (hR : 0<R) (hδ : 0≤δ)
    (hrec : ∀r>0,N (2*r)≤N r+A r)
    (hA : ∀r≥R,A r≤δ*((2:ℝ)^ρ-1)*r^ρ) :
    ∀k : ℕ,N ((2:ℝ)^k*R)≤N R+δ*((2:ℝ)^k*R)^ρ := by
  intro k
  induction k with
  | zero => simpa using (le_add_of_nonneg_right (a:=N R)
      (mul_nonneg hδ (Real.rpow_nonneg hR.le ρ)))
  | succ k hk =>
    have hp : 0<(2:ℝ)^k*R := mul_pos (pow_pos (by norm_num) _) hR
    have hr : R≤(2:ℝ)^k*R := by
      simpa using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hR.le
    have he : (2:ℝ)^(k+1)*R=2*((2:ℝ)^k*R) := by rw [pow_succ]; ring
    rw [he]
    calc
      _ ≤ N ((2:ℝ)^k*R)+A ((2:ℝ)^k*R) := hrec _ hp
      _ ≤ N R+δ*((2:ℝ)^k*R)^ρ+δ*((2:ℝ)^ρ-1)*((2:ℝ)^k*R)^ρ :=
        add_le_add hk (hA _ hr)
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hp.le]; ring

/-- Monotonicity is needed only for positive radii. No boundedness or
zero-density conclusion is assumed for the counting function itself. -/
theorem radial_density_of_annular_density {N A : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0<ρ) (hN : ∀r>0,0≤N r) (hmono : MonotoneOn N (Ioi 0))
    (hrec : ∀r>0,N (2*r)≤N r+A r)
    (hsmall : Tendsto (fun r : ℝ=>A r/r^ρ) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ=>N r/r^ρ) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have htwo : 0<(2:ℝ)^ρ := Real.rpow_pos_of_pos (by norm_num) _
  have htwo1 : 1<(2:ℝ)^ρ := Real.one_lt_rpow (by norm_num) hρ
  let δ := ε/(2*(2:ℝ)^ρ)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hc : 0<δ*((2:ℝ)^ρ-1) := mul_pos hδ (sub_pos.mpr htwo1)
  obtain ⟨a,ha⟩ := eventually_atTop.mp (hsmall.eventually (gt_mem_nhds hc))
  let R := max 1 a
  have hR1 : 1≤R := le_max_left ..
  have hR : 0<R := zero_lt_one.trans_le hR1
  have hA : ∀r≥R,A r≤δ*((2:ℝ)^ρ-1)*r^ρ := by
    intro r hr
    have hrp : 0<r := hR.trans_le hr
    exact (div_lt_iff₀ (Real.rpow_pos_of_pos hrp ρ)).mp
      (ha r ((le_max_right _ _).trans hr)) |>.le
  have hlim : Tendsto (fun r : ℝ=>N R/r^ρ) atTop (𝓝 0) :=
    (tendsto_rpow_atTop hρ).const_div_atTop (N R)
  obtain ⟨b,hb⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2)))
  refine ⟨max R b,?_⟩
  intro r hr
  have hRr : R≤r := (le_max_left _ _).trans hr
  have hrp : 0<r := hR.trans_le hRr
  have hx : 1≤r/R := (le_div_iff₀ hR).mpr (by simpa using hRr)
  obtain ⟨k,hklo,hkhi⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  have hlo : (2:ℝ)^k*R≤r := (le_div_iff₀ hR).mp hklo
  have hhi : r<(2:ℝ)^(k+1)*R := (div_lt_iff₀ hR).mp hkhi
  have hu : (2:ℝ)^(k+1)*R≤2*r := by
    rw [pow_succ]
    nlinarith
  have hupper : ((2:ℝ)^(k+1)*R)^ρ≤(2:ℝ)^ρ*r^ρ := by
    rw [←Real.mul_rpow (by norm_num : (0:ℝ)≤2) hrp.le]
    exact Real.rpow_le_rpow (by positivity) hu hρ.le
  have hcount : N r≤N R+δ*((2:ℝ)^ρ*r^ρ) :=
    (hmono (show r∈Ioi 0 from hrp)
      (show (2:ℝ)^(k+1)*R∈Ioi 0 by change 0<(2:ℝ)^(k+1)*R; positivity) hhi.le).trans
      ((dyadic_bound hR hδ.le hrec hA (k+1)).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hupper hδ.le)))
  have hratio : N r/r^ρ≤N R/r^ρ+δ*(2:ℝ)^ρ := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hrp ρ)).mpr
    calc
      _ ≤ N R+δ*((2:ℝ)^ρ*r^ρ) := hcount
      _ = _ := by field_simp
  have hpos : 0≤N r/r^ρ := div_nonneg (hN r hrp) (Real.rpow_pos_of_pos hrp ρ).le
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hpos]
  have hb' := hb r ((le_max_right _ _).trans hr)
  have hd : δ*(2:ℝ)^ρ=ε/2 := by dsimp [δ]; field_simp
  rw [hd] at hratio
  linarith

#print axioms dyadic_bound
#print axioms radial_density_of_annular_density
end CRGZeroDistributionDyadic
