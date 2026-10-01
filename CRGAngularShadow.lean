import NormalFormGoal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! Angular shadows of actual disks on ray tails. Restricting to an argument
interval of length at most pi avoids any implicit choice of a global argument. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped Topology
namespace CRGAngularShadow
open CRGNormalFormGoal

def direction (θ : ℝ) : ℂ := Complex.exp ((θ:ℂ)*Complex.I)

theorem norm_direction (θ : ℝ) : ‖direction θ‖=1 := by
  simp [direction, Complex.norm_exp]

theorem normalized_distance (u v : ℂ) (hu : ‖u‖=1) (hv : ‖v‖=1)
    {r s : ℝ} (hr : 0≤r) (hs : 0≤s) :
    r*‖u-v‖ ≤ 2*‖(r:ℂ)*u-(s:ℂ)*v‖ := by
  have he : (r:ℂ)*(u-v) = ((r:ℂ)*u-(s:ℂ)*v)+((s-r:ℝ):ℂ)*v := by
    push_cast; ring
  have hn := norm_add_le ((r:ℂ)*u-(s:ℂ)*v) (((s-r:ℝ):ℂ)*v)
  rw [← he, norm_mul, norm_mul, hv, mul_one, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr] at hn
  have hd := abs_norm_sub_norm_le ((s:ℂ)*v) ((r:ℂ)*u)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hv, hu,
    abs_of_nonneg hr, abs_of_nonneg hs, mul_one, norm_sub_rev] at hd
  linarith

theorem direction_distance (θ φ : ℝ) :
    ‖direction θ-direction φ‖=2*|Real.sin ((θ-φ)/2)| := by
  have he : direction θ-direction φ =
      direction φ*(Complex.exp (Complex.I*((θ-φ:ℝ):ℂ))-1) := by
    unfold direction
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 1
    congr 1
    push_cast; ring
  rw [he, norm_mul, norm_direction, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  simp [Real.norm_eq_abs]

theorem angle_le_direction_distance {θ φ : ℝ} (h : |θ-φ|≤Real.pi) :
    |θ-φ|≤Real.pi/2*‖direction θ-direction φ‖ := by
  have hh := Real.mul_abs_le_abs_sin (x := (θ-φ)/2)
    (by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith)
  rw [direction_distance]
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  have hp := Real.pi_pos
  have hmul := mul_le_mul_of_nonneg_left hh hp.le
  field_simp at hmul
  nlinarith

def shadow (a b R : ℝ) (c : ℂ) (s : ℝ) : Set ℝ :=
  {θ | θ∈Icc a b ∧ ∃ r : ℝ, R≤r ∧ ray θ r∈ball c s}

theorem shadow_diameter {a b R s : ℝ} {c : ℂ}
    (hR : 0<R) (hw : b-a≤Real.pi)
    {θ φ : ℝ} (hθ : θ∈shadow a b R c s) (hφ : φ∈shadow a b R c s) :
    |θ-φ| < 2*Real.pi*s/R := by
  obtain ⟨hθ, r, hr, hzr⟩ := hθ
  obtain ⟨hφ, t, ht, hzt⟩ := hφ
  have hangle : |θ-φ|≤Real.pi := abs_le.mpr ⟨by linarith [hθ.1,hφ.2],
    by linarith [hθ.2,hφ.1]⟩
  have hdist : ‖ray θ r-ray φ t‖<2*s := by
    have hh := dist_triangle (ray θ r) c (ray φ t)
    have h1 : dist (ray θ r) c<s := hzr
    have h2 : dist c (ray φ t)<s := by simpa only [mem_ball, dist_comm] using hzt
    rw [dist_eq_norm] at hh
    linarith
  have hc := normalized_distance (direction θ) (direction φ)
    (norm_direction θ) (norm_direction φ) (hR.le.trans hr) (hR.le.trans ht)
  change r*‖direction θ-direction φ‖ ≤ 2*‖ray θ r-ray φ t‖ at hc
  have hsmall : R*‖direction θ-direction φ‖ < 4*s := by
    have hl := mul_le_mul_of_nonneg_right hr (norm_nonneg (direction θ-direction φ))
    linarith
  apply (lt_div_iff₀ hR).mpr
  have ha := angle_le_direction_distance hangle
  have hmul := mul_lt_mul_of_pos_left hsmall (show 0<Real.pi/2 by positivity)
  nlinarith

theorem shadow_volume_le {a b R s : ℝ} {c : ℂ}
    (hR : 0<R) (hw : b-a≤Real.pi) :
    volume (shadow a b R c s) ≤ ENNReal.ofReal (4*Real.pi*s/R) := by
  by_cases he : (shadow a b R c s).Nonempty
  · obtain ⟨φ,hφ⟩ := he
    have hsub : shadow a b R c s ⊆ Ioo (φ-2*Real.pi*s/R) (φ+2*Real.pi*s/R) := by
      intro θ hθ
      have hh := abs_lt.mp (shadow_diameter hR hw hθ hφ)
      constructor <;> linarith
    calc
      volume (shadow a b R c s) ≤ volume (Ioo (φ-2*Real.pi*s/R) (φ+2*Real.pi*s/R)) :=
        measure_mono hsub
      _ = ENNReal.ofReal (4*Real.pi*s/R) := by rw [Real.volume_Ioo]; congr 1; ring
  · rw [Set.not_nonempty_iff_eq_empty.mp he, measure_empty]
    exact bot_le

theorem family_shadow_volume_le {ι : Type*} [Fintype ι]
    {a b R : ℝ} (c : ι→ℂ) (s : ι→ℝ)
    (hR : 0<R) (hw : b-a≤Real.pi) (hs : ∀i,0≤s i) :
    volume (⋃i, shadow a b R (c i) (s i)) ≤
      ENNReal.ofReal (4*Real.pi*(∑i,s i)/R) := by
  calc
    volume (⋃i, shadow a b R (c i) (s i)) ≤
        ∑i,volume (shadow a b R (c i) (s i)) := measure_iUnion_fintype_le _ _
    _ ≤ ∑i,ENNReal.ofReal (4*Real.pi*s i/R) :=
      Finset.sum_le_sum (fun i _ => shadow_volume_le hR hw)
    _ = ENNReal.ofReal (4*Real.pi*(∑i,s i)/R) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (hs i)) hR.le)]
      congr 1
      rw [← Finset.sum_div, ← Finset.mul_sum]

theorem ae_eventually_avoid_on_interval (m : ℕ→ℕ)
    (c : (n : ℕ)→Fin (m n)→ℂ) (s : (n : ℕ)→Fin (m n)→ℝ)
    (R : ℕ→ℝ) (hR : ∀n,0<R n) (hs : ∀n i,0≤s n i)
    (hbudget : (∑' n, ENNReal.ofReal (4*Real.pi*(∑i,s n i)/R n))≠⊤)
    {a b : ℝ} (hw : b-a≤Real.pi) :
    ∀ᵐ θ : ℝ, θ∈Icc a b →
      ∀ᶠ n in Filter.atTop, ∀r : ℝ, R n≤r → ∀i, ray θ r∉ball (c n i) (s n i) := by
  have hb : (∑' n,volume (⋃i,shadow a b (R n) (c n i) (s n i)))≠⊤ :=
    ne_top_of_le_ne_top hbudget (ENNReal.tsum_le_tsum
      (fun n => family_shadow_volume_le (c n) (s n) (hR n) hw (hs n)))
  filter_upwards [ae_eventually_notMem hb] with θ hθ hmem
  filter_upwards [hθ] with n hn
  intro r hr i hi
  exact hn (mem_iUnion.mpr ⟨i,hmem,r,hr,hi⟩)

theorem ae_eventually_avoid (m : ℕ→ℕ)
    (c : (n : ℕ)→Fin (m n)→ℂ) (s : (n : ℕ)→Fin (m n)→ℝ)
    (R : ℕ→ℝ) (hR : ∀n,0<R n) (hs : ∀n i,0≤s n i)
    (hbudget : (∑' n, ENNReal.ofReal (4*Real.pi*(∑i,s n i)/R n))≠⊤) :
    ∀ᵐ θ : ℝ, ∀ᶠ n in Filter.atTop,
      ∀r : ℝ, R n≤r → ∀i, ray θ r∉ball (c n i) (s n i) := by
  have hinterval (k : ℤ) : ∀ᵐ θ : ℝ, θ∈Icc (k:ℝ) ((k:ℝ)+1) →
      ∀ᶠ n in Filter.atTop, ∀r : ℝ, R n≤r → ∀i, ray θ r∉ball (c n i) (s n i) :=
    ae_eventually_avoid_on_interval m c s R hR hs hbudget (by linarith [Real.one_le_pi_div_two])
  filter_upwards [ae_all_iff.mpr hinterval] with θ hθ
  exact hθ ⌊θ⌋ ⟨Int.floor_le θ, (Int.lt_floor_add_one θ).le⟩

#print axioms norm_direction
#print axioms normalized_distance
#print axioms direction_distance
#print axioms angle_le_direction_distance
#print axioms shadow_diameter
#print axioms shadow_volume_le
#print axioms family_shadow_volume_le
#print axioms ae_eventually_avoid_on_interval
#print axioms ae_eventually_avoid
end CRGAngularShadow
