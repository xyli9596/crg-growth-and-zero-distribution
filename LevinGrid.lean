import LevinIndicatorModulus

/-! An explicit quadratic-size complex grid. All centers retained for the
annular cover stay a fixed distance from the origin. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Metric Real Complex
open scoped Topology
namespace LevinGrid

/-- One-dimensional uniform grid on the interval `[-2,2]`. -/
def coordinate (n : ℕ) (i : Fin (4 * n + 1)) : ℝ := (i.val : ℝ) / n - 2

/-- The mesh contains at most `(4n+1)^2` points. -/
def point (n : ℕ) (i : Fin (4 * n + 1) × Fin (4 * n + 1)) : ℂ :=
  ⟨coordinate n i.1, coordinate n i.2⟩

theorem exists_coordinate {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : |x| ≤ 2) :
    ∃ i : Fin (4 * n + 1), |x - coordinate n i| ≤ 1 / n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let k : ℕ := ⌊(n : ℝ) * (x + 2)⌋₊
  have hxlo : 0 ≤ (n : ℝ) * (x + 2) := mul_nonneg hnR.le (by linarith [(abs_le.mp hx).1])
  have hkbound : k ≤ 4 * n := by
    apply Nat.floor_le_of_le
    push_cast
    nlinarith [(abs_le.mp hx).2]
  let i : Fin (4 * n + 1) := ⟨k, by omega⟩
  have hlow : (k : ℝ) ≤ (n : ℝ) * (x + 2) := Nat.floor_le hxlo
  have hhigh : (n : ℝ) * (x + 2) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨i, ?_⟩
  change |x - ((k : ℝ) / n - 2)| ≤ 1 / n
  rw [abs_le]
  constructor
  · have h : (k : ℝ) / n ≤ x + 2 := (div_le_iff₀ hnR).mpr (by nlinarith [hlow])
    linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hnR.le]
  · apply (le_div_iff₀ hnR).mpr
    have heq : (x - ((k : ℝ) / n - 2)) * n = (n : ℝ) * (x + 2) - k := by
      field_simp
      ring
    rw [heq]
    linarith

theorem exists_point {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ∃ i : Fin (4 * n + 1) × Fin (4 * n + 1), ‖z - point n i‖ ≤ 2 / n := by
  obtain ⟨i, hi⟩ := exists_coordinate hn ((abs_re_le_norm z).trans hz)
  obtain ⟨j, hj⟩ := exists_coordinate hn ((abs_im_le_norm z).trans hz)
  refine ⟨(i, j), ?_⟩
  have hb := norm_le_abs_re_add_abs_im (z - point n (i, j))
  change ‖z - point n (i, j)‖ ≤ |z.re - coordinate n i| + |z.im - coordinate n j| at hb
  calc
    _ ≤ _ := hb
    _ ≤ 1 / (n : ℝ) + 1 / n := add_le_add hi hj
    _ = _ := by ring

/-- Only the grid points close to the unit annulus are needed. -/
def annularGrid (n : ℕ) : Finset ℂ := by
  classical
  exact (Finset.univ.image (point n)).filter (fun z => 1 - 2 / (n : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 2 + 2 / (n : ℝ))

theorem annularGrid_card (n : ℕ) : (annularGrid n).card ≤ (4 * n + 1) ^ 2 := by
  classical
  unfold annularGrid
  exact Finset.card_filter_le _ _ |>.trans (Finset.card_image_le.trans (by simp [sq]))

theorem annularGrid_covers {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : ‖z‖ ∈ Icc (1 : ℝ) 2) :
    ∃ c ∈ annularGrid n, ‖z - c‖ ≤ 2 / n := by
  classical
  obtain ⟨i, hi⟩ := exists_point hn hz.2
  refine ⟨point n i, ?_, hi⟩
  simp only [annularGrid, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨⟨i, rfl⟩, ?_, ?_⟩
  · have hr := norm_sub_norm_le z (point n i)
    linarith [hz.1]
  · have hr := norm_sub_norm_le (point n i) z
    rw [norm_sub_rev] at hr
    linarith [hz.2]

theorem annularGrid_norm_bounds {n : ℕ} (hn : 8 ≤ n) {c : ℂ}
    (hc : c ∈ annularGrid n) : ‖c‖ ∈ Icc (3 / 4 : ℝ) (9 / 4) := by
  classical
  have hnR : 8 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hdiv : 2 / (n : ℝ) ≤ 1 / 4 := (div_le_iff₀ hn0).mpr (by linarith)
  have hc' := (Finset.mem_filter.mp hc).2
  exact ⟨by linarith [hc'.1], by linarith [hc'.2]⟩

/-- A concrete annular cover at every small real mesh size. Its quadratic
cardinality bound is uniform in the mesh size. -/
theorem exists_annular_cover {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ Γ : Finset ℂ, (Γ.card : ℝ) * δ ^ 2 ≤ 100 ∧
      (∀ c ∈ Γ, ‖c‖ ∈ Icc (3 / 4 : ℝ) (9 / 4)) ∧
      ∀ z : ℂ, ‖z‖ ∈ Icc (1 : ℝ) 2 → ∃ c ∈ Γ, ‖z - c‖ ≤ δ := by
  let n : ℕ := ⌈2 / δ⌉₊
  have hceil : 2 / δ ≤ (n : ℝ) := Nat.le_ceil _
  have hceil' : (n : ℝ) < 2 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hnR : 8 ≤ (n : ℝ) := by
    have hdiv : 8 ≤ 2 / δ := (le_div_iff₀ hδ).mpr (by linarith)
    exact hdiv.trans hceil
  have hn : 8 ≤ n := by exact_mod_cast hnR
  have hn0 : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by positivity
  have hmesh : 2 / (n : ℝ) ≤ δ := by
    apply (div_le_iff₀ hnpos).mpr
    have hb := (div_le_iff₀ hδ).mp hceil
    nlinarith
  have hnδ : (n : ℝ) * δ < 2 + δ := by
    have hb := mul_lt_mul_of_pos_right hceil' hδ
    have heq : (2 / δ + 1) * δ = 2 + δ := by field_simp
    rwa [heq] at hb
  have hwidth : (4 * (n : ℝ) + 1) * δ ≤ 10 := by nlinarith
  have hwidth0 : 0 ≤ (4 * (n : ℝ) + 1) * δ := by positivity
  have hcard : ((annularGrid n).card : ℝ) ≤ (4 * (n : ℝ) + 1) ^ 2 := by
    exact_mod_cast annularGrid_card n
  refine ⟨annularGrid n, ?_, fun c hc => annularGrid_norm_bounds hn hc, ?_⟩
  · have hb := mul_le_mul_of_nonneg_right hcard (sq_nonneg δ)
    have heq : (4 * (n : ℝ) + 1) ^ 2 * δ ^ 2 = ((4 * (n : ℝ) + 1) * δ) ^ 2 := by ring
    rw [heq] at hb
    nlinarith
  · intro z hz
    obtain ⟨c, hc, hdist⟩ := annularGrid_covers hn0 hz
    exact ⟨c, hc, hdist.trans hmesh⟩

/-- Zero radial density leaves a good radius in every mesh-length interval
throughout a whole enlarged annulus, at every sufficiently large scale. -/
theorem eventually_good_mesh_radii {E : Set ℝ} (hE : LevinDensity.ZeroRadialDensity E)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ s ∈ Icc (1 / 2 : ℝ) 3,
        ∃ r : ℝ, s * R < r ∧ r < (s + δ) * R ∧ r ∉ E := by
  obtain ⟨A, hA, hb⟩ := hE (δ / 8) (by positivity)
  refine ⟨max A 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro R hR s hs
  have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 < R := by linarith
  have hAR : A ≤ 4 * R := by linarith [(le_max_left A 1).trans hR]
  have hnot : ¬ Ioo (s * R) ((s + δ) * R) ⊆ E := by
    intro hsub
    have hsub' : Ioo (s * R) ((s + δ) * R) ⊆ E ∩ Icc 0 (4 * R) := by
      intro r hr
      refine ⟨hsub hr, ?_, ?_⟩
      · nlinarith [hs.1, hr.1]
      · nlinarith [hs.2, hr.2]
    have hm := (measure_mono hsub').trans (hb (4 * R) hAR)
    rw [Real.volume_Ioo] at hm
    have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ δ / 8 * (4 * R))).mp hm
    nlinarith [mul_pos hδ hR0]
  obtain ⟨r, hr, hrE⟩ := Set.not_subset.mp hnot
  exact ⟨r, hr.1, hr.2, hrE⟩

#print axioms exists_coordinate
#print axioms exists_point
#print axioms annularGrid_card
#print axioms annularGrid_covers
#print axioms annularGrid_norm_bounds
#print axioms exists_annular_cover
#print axioms eventually_good_mesh_radii
end LevinGrid
