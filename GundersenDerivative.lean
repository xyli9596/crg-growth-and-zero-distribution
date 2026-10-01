import GundersenGrowth
import Mathlib.Analysis.Complex.Liouville

/-! Cauchy's actual derivative estimate preserves upper order, supplying the
successive functions to which the first Gundersen estimate is applied. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace GundersenDerivative

theorem entire_deriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (deriv f) :=
  fun z => (hf.analyticAt z).deriv.differentiableAt

theorem upperOrder_deriv {f : ℂ → ℂ} {ρ : ℝ} (hf : Differentiable ℂ f)
    (hρ : 0 ≤ ρ) (ho : CRGOrder.UpperOrder f ρ) :
    CRGOrder.UpperOrder (deriv f) ρ := by
  intro δ hδ
  obtain ⟨A, hA, hb⟩ := GundersenGrowth.scaled_exp_bound hf.continuous hρ
    (show 0 < δ/2 by linarith) ho
  obtain ⟨S, hS⟩ := eventually_atTop.mp (CRGOrder.eventually_mul_rpow_le (C := A)
    (show ρ+δ/2 < ρ+δ by linarith))
  refine ⟨max S 1, fun z hz => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
  have hz0 : 0 < ‖z‖ := by linarith
  have hcircle : ∀ w ∈ sphere z ‖z‖, ‖f w‖ ≤ Real.exp (A*‖z‖^(ρ+δ/2)) := by
    intro w hw
    apply hb ‖z‖ hz1 w
    have hwz : ‖w-z‖ = ‖z‖ := by simpa only [mem_sphere, dist_eq_norm] using hw
    have htri := norm_add_le (w-z) z
    rw [sub_add_cancel, hwz] at htri
    rw [mem_closedBall_zero_iff]
    linarith [norm_nonneg z]
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hz0 hf.diffContOnCl hcircle
  calc
    ‖deriv f z‖ ≤ Real.exp (A*‖z‖^(ρ+δ/2))/‖z‖ := hc
    _ ≤ Real.exp (A*‖z‖^(ρ+δ/2)) := div_le_self (Real.exp_pos _).le hz1
    _ ≤ _ := Real.exp_le_exp.mpr (hS ‖z‖ ((le_max_left _ _).trans hz))

theorem entire_iteratedDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact entire_deriv ih

theorem upperOrder_iteratedDeriv {f : ℂ → ℂ} {ρ : ℝ} (hf : Differentiable ℂ f)
    (hρ : 0 ≤ ρ) (ho : CRGOrder.UpperOrder f ρ) (n : ℕ) :
    CRGOrder.UpperOrder (iteratedDeriv n f) ρ := by
  induction n with
  | zero => simpa using ho
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact upperOrder_deriv (entire_iteratedDeriv hf n) hρ ih

#print axioms entire_deriv
#print axioms upperOrder_deriv
#print axioms entire_iteratedDeriv
#print axioms upperOrder_iteratedDeriv
end GundersenDerivative
