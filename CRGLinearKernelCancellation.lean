import CRGLinearKernelCoefficients
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Endpoint cancellation for analytic interval densities. Equality of all
jets gives an actual analytic gluing and an exact identity of integrals. -/
set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval
namespace CRGLinearKernelCancellation
open CRGLinearKernelIntegration

theorem analytic_germs_eq_of_jets_eq {v w : ℝ → ℂ} {b : ℝ}
    (hv : AnalyticAt ℝ v b) (hw : AnalyticAt ℝ w b)
    (hj : ∀j : ℕ, iteratedDeriv j v b = iteratedDeriv j w b) :
    v =ᶠ[𝓝 b] w := by
  have hsub : AnalyticAt ℝ (v-w) b := hv.sub hw
  have hzero (j : ℕ) : iteratedDeriv j (v-w) b=0 := by
    rw [iteratedDeriv_sub hv.contDiffAt hw.contDiffAt,hj j,sub_self]
  have ho : ∀ n : ℕ, (n:ℕ∞)≤analyticOrderAt (v-w) b := fun n =>
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hsub).mpr (fun j _=>hzero j)
  have htop : analyticOrderAt (v-w) b=⊤ :=
    ENat.eq_of_forall_natCast_le_iff (fun n=>by simp [ho n])
  filter_upwards [analyticOrderAt_eq_top.mp htop] with t ht
  exact sub_eq_zero.mp ht

theorem zero_on_interval_of_endpoint_jets_zero {v : ℝ → ℂ} {a b : ℝ}
    (hab : a≤b) (hv : AnalyticOnNhd ℝ v (Icc a b))
    (hj : ∀j : ℕ,iteratedDeriv j v b=0) : EqOn v 0 (Icc a b) := by
  have hvb := hv b ⟨hab,le_rfl⟩
  have ho : ∀n : ℕ,(n:ℕ∞)≤analyticOrderAt v b := fun n=>
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hvb).mpr (fun j _=>hj j)
  have htop : analyticOrderAt v b=⊤ :=
    ENat.eq_of_forall_natCast_le_iff (fun n=>by simp [ho n])
  exact hv.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Icc
    ⟨hab,le_rfl⟩ (analyticOrderAt_eq_top.mp htop)

def glue (b : ℝ) (v w : ℝ → ℂ) (t : ℝ) : ℂ := if t≤b then v t else w t

theorem analytic_glue {v w : ℝ → ℂ} {a b c : ℝ}
    (hab : a≤b) (hbc : b≤c)
    (hv : AnalyticOnNhd ℝ v (Icc a b)) (hw : AnalyticOnNhd ℝ w (Icc b c))
    (hj : ∀j : ℕ,iteratedDeriv j v b=iteratedDeriv j w b) :
    AnalyticOnNhd ℝ (glue b v w) (Icc a c) := by
  have he := analytic_germs_eq_of_jets_eq (hv b ⟨hab,le_rfl⟩)
    (hw b ⟨le_rfl,hbc⟩) hj
  intro t ht
  rcases lt_trichotomy t b with hlt|heq|hgt
  · apply (hv t ⟨ht.1,hlt.le⟩).congr
    filter_upwards [ge_mem_nhds hlt] with x hx
    simp [glue,hx]
  · subst t
    apply (hv b ⟨hab,le_rfl⟩).congr
    filter_upwards [he] with x hx
    simp only [glue]
    split_ifs with h
    · rfl
    · exact hx
  · apply (hw t ⟨hgt.le,ht.2⟩).congr
    filter_upwards [lt_mem_nhds hgt] with x hx
    simp [glue,not_le.mpr hx]

theorem kernel_glue {v w : ℝ → ℂ} {a b c : ℝ} (ζ : ℂ)
    (hab : a≤b) (hbc : b≤c)
    (hv : AnalyticOnNhd ℝ v (Icc a b)) (hw : AnalyticOnNhd ℝ w (Icc b c))
    (hj : ∀j : ℕ,iteratedDeriv j v b=iteratedDeriv j w b) :
    kernel v a b ζ+kernel w b c ζ=kernel (glue b v w) a c ζ := by
  have hg := (analytic_glue hab hbc hv hw hj).continuousOn
  have he : ContinuousOn (fun t : ℝ=>Complex.exp (ζ*(t:ℂ))) (Icc a c) := by fun_prop
  have hcont := hg.mul he
  have hiab : IntervalIntegrable (fun t=>glue b v w t*Complex.exp (ζ*(t:ℂ))) volume a b :=
    (hcont.mono (by intro t ht;exact ⟨ht.1,ht.2.trans hbc⟩)).intervalIntegrable_of_Icc hab
  have hibc : IntervalIntegrable (fun t=>glue b v w t*Complex.exp (ζ*(t:ℂ))) volume b c :=
    (hcont.mono (by intro t ht;exact ⟨hab.trans ht.1,ht.2⟩)).intervalIntegrable_of_Icc hbc
  have hl : kernel v a b ζ=kernel (glue b v w) a b ζ := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro t ht
    simp [glue,ht.2.le]
  have hr : kernel w b c ζ=kernel (glue b v w) b c ζ := by
    apply intervalIntegral.integral_congr_Ioo_of_le hbc
    intro t ht
    simp [glue,not_le.mpr ht.1]
  rw [hl,hr]
  exact intervalIntegral.integral_add_adjacent_intervals hiab hibc

theorem kernel_zero_of_endpoint_jets_zero {v : ℝ → ℂ} {a b : ℝ} (ζ : ℂ)
    (hab : a≤b) (hv : AnalyticOnNhd ℝ v (Icc a b))
    (hj : ∀j : ℕ,iteratedDeriv j v b=0) : kernel v a b ζ=0 := by
  have hz := zero_on_interval_of_endpoint_jets_zero hab hv hj
  have hi : kernel v a b ζ=∫t in a..b,(0:ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    simp [hz ht]
  rw [hi]
  simp

#print axioms analytic_germs_eq_of_jets_eq
#print axioms zero_on_interval_of_endpoint_jets_zero
#print axioms analytic_glue
#print axioms kernel_glue
#print axioms kernel_zero_of_endpoint_jets_zero
end CRGLinearKernelCancellation
