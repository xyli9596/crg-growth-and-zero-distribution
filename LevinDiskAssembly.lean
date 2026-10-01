import LevinGeometry
import LevinDyadic
import LevinGrowth
import Mathlib.Data.Nat.Pairing

/-!
# Geometric assembly of shellwise exceptional disks

The geometry and diagonalization in this module do not assume or assert a
Cartan small-value theorem. Analytic shell certificates remain explicit inputs.
-/

noncomputable section
open Set Filter MeasureTheory Topology
open LevinGeometry LevinGrowth

namespace LevinDiskAssembly

/-- Enumerate the countable family of shellwise disk families by one natural index. -/
def flatten (D : ℕ → DiskFamily) : DiskFamily where
  center i := (D (Nat.unpair i).1).center (Nat.unpair i).2
  radius i := (D (Nat.unpair i).1).radius (Nat.unpair i).2
  radius_nonneg i := (D (Nat.unpair i).1).radius_nonneg (Nat.unpair i).2

/-- Flattening preserves the actual union of open disks. -/
theorem mem_disks_flatten (D : ℕ → DiskFamily) (z : ℂ) :
    z ∈ disks (flatten D) ↔ ∃ n : ℕ, z ∈ disks (D n) := by
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz
    exact ⟨(Nat.unpair i).1, mem_iUnion.2 ⟨(Nat.unpair i).2, hi⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨k, hk⟩ := mem_iUnion.1 hn
    apply mem_iUnion.2
    refine ⟨Nat.pair n k, ?_⟩
    simpa only [flatten, Nat.unpair_pair] using hk

/-- Flattening preserves the center-truncated sum of all radii. -/
theorem radiusMass_flatten (D : ℕ → DiskFamily) (R : ℝ) :
    radiusMass (flatten D) R = ∑' n, radiusMass (D n) R := by
  unfold radiusMass
  change (∑' i : ℕ, (fun p : ℕ × ℕ =>
    if ‖(D p.1).center p.2‖ ≤ R then ENNReal.ofReal ((D p.1).radius p.2) else 0)
      (Nat.pairEquiv.symm i)) = _
  exact (Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ =>
    if ‖(D p.1).center p.2‖ ≤ R then ENNReal.ofReal ((D p.1).radius p.2) else 0)).trans
      (ENNReal.tsum_prod (f := fun n k : ℕ =>
        if ‖(D n).center k‖ ≤ R then ENNReal.ofReal ((D n).radius k) else 0))

/-- A finite initial sum plus a geometric tail controls every weighted partial sum. -/
theorem weighted_partial_sum_le (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (htail : ∀ n, N ≤ n → b n ≤ δ) (K : ℕ) :
    (∑ n ∈ Finset.range K, b n * (2 : ℝ) ^ n) ≤
      (∑ n ∈ Finset.range N, b n * (2 : ℝ) ^ n) + δ * 2 ^ K := by
  classical
  have hprefix : (∑ n ∈ Finset.range K, if n < N then b n * (2 : ℝ) ^ n else 0) ≤
      ∑ n ∈ Finset.range N, b n * (2 : ℝ) ^ n := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_range.2 (Finset.mem_filter.1 hn).2
    · intro n _ _
      exact mul_nonneg (hb n) (by positivity)
  calc
    (∑ n ∈ Finset.range K, b n * (2 : ℝ) ^ n) ≤
        ∑ n ∈ Finset.range K, ((if n < N then b n * (2 : ℝ) ^ n else 0) + δ * 2 ^ n) := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : n < N
      · simp only [if_pos hn]
        exact le_add_of_nonneg_right (mul_nonneg hδ (by positivity))
      · simp only [if_neg hn, zero_add]
        exact mul_le_mul_of_nonneg_right (htail n (by omega)) (by positivity)
    _ = (∑ n ∈ Finset.range K, if n < N then b n * (2 : ℝ) ^ n else 0) +
        δ * ((2 : ℝ) ^ K - 1) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, LevinDyadic.sum_two_pow]
    _ ≤ (∑ n ∈ Finset.range N, b n * (2 : ℝ) ^ n) + δ * 2 ^ K := by
      nlinarith

/-- A shell contributes no radius mass below its center scale. Zero-radius
padding disks need not satisfy the center constraint. -/
theorem radiusMass_eq_zero_below_scale (D : DiskFamily) {s R : ℝ}
    (hcenter : ∀ k, D.radius k ≠ 0 → s ≤ ‖D.center k‖) (hR : R < s) :
    radiusMass D R = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro k
  by_cases hz : D.radius k = 0
  · simp only [hz, ENNReal.ofReal_zero, ite_self]
  · have hn : ¬ ‖D.center k‖ ≤ R := by linarith [hcenter k hz]
    simp only [if_neg hn]

/-- Center lower bounds turn the infinite flattened mass into a bounded
weighted partial sum of the shell budgets. -/
theorem radiusMass_le_partial_sum (D : ℕ → DiskFamily) {c R : ℝ}
    (hc : 0 < c) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hcenter : ∀ n k, (D n).radius k ≠ 0 → c * (2 : ℝ) ^ n ≤ ‖(D n).center k‖)
    (hrow : ∀ n, (∑' k, ENNReal.ofReal ((D n).radius k)) ≤ ENNReal.ofReal (b n * 2 ^ n))
    (K : ℕ) (hR : R < c * (2 : ℝ) ^ K) :
    radiusMass (flatten D) R ≤ ENNReal.ofReal (∑ n ∈ Finset.range K, b n * (2 : ℝ) ^ n) := by
  rw [radiusMass_flatten]
  have hz : ∀ n ∉ Finset.range K, radiusMass (D n) R = 0 := by
    intro n hn
    apply radiusMass_eq_zero_below_scale (D n) (hcenter n)
    exact hR.trans_le (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num) (by simpa using hn)) hc.le)
  rw [tsum_eq_sum hz, ENNReal.ofReal_sum_of_nonneg
    (fun n _ => mul_nonneg (hb n) (by positivity))]
  apply Finset.sum_le_sum
  intro n _
  apply le_trans _ (hrow n)
  apply ENNReal.tsum_le_tsum
  intro k
  split_ifs
  · exact le_rfl
  · exact bot_le

/-- Shellwise radius budgets tending to zero produce a genuine C₀ disk family.
The conclusion uses the specified center-truncated `radiusMass` definition. -/
theorem isC0_flatten (D : ℕ → DiskFamily) {c : ℝ} (hc : 0 < c)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hcenter : ∀ n k, (D n).radius k ≠ 0 → c * (2 : ℝ) ^ n ≤ ‖(D n).center k‖)
    (hrow : ∀ n, (∑' k, ENNReal.ofReal ((D n).radius k)) ≤ ENNReal.ofReal (b n * 2 ^ n)) :
    IsC0 (flatten D) := by
  intro ε hε
  let δ : ℝ := ε * c / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hblim).2 δ hδ)
  let A : ℝ := ∑ n ∈ Finset.range N, b n * (2 : ℝ) ^ n
  have hA : 0 ≤ A := Finset.sum_nonneg (fun n _ => mul_nonneg (hb n) (by positivity))
  refine ⟨max (max c 1) (2 * A / ε),
    (show (0 : ℝ) ≤ 1 by norm_num).trans ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  intro R hR
  have hcR : c ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hR)
  have hAR : A ≤ ε * R / 2 := by
    have hh := (div_le_iff₀ hε).1 ((le_max_right (max c 1) (2 * A / ε)).trans hR)
    nlinarith
  have hRc : 1 ≤ R / c := (le_div_iff₀ hc).2 (by simpa using hcR)
  obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near hRc (show (1 : ℝ) < 2 by norm_num)
  have hupper : R < c * (2 : ℝ) ^ (k + 1) := by
    have h := (div_lt_iff₀ hc).1 hk₂
    nlinarith
  have hpower : c * (2 : ℝ) ^ (k + 1) ≤ 2 * R := by
    have h := (le_div_iff₀ hc).1 hk₁
    rw [pow_succ]
    nlinarith
  apply (radiusMass_le_partial_sum D hc b hb hcenter hrow (k + 1) hupper).trans
  apply ENNReal.ofReal_le_ofReal
  have hsum := weighted_partial_sum_le b hb N hδ.le (fun n hn => (hN n hn).le) (k + 1)
  change (∑ n ∈ Finset.range (k + 1), b n * (2 : ℝ) ^ n) ≤ ε * R
  have htail : δ * (2 : ℝ) ^ (k + 1) ≤ ε * R / 2 := by
    dsimp [δ]
    nlinarith
  exact hsum.trans (by change A + δ * (2 : ℝ) ^ (k + 1) ≤ ε * R; linarith)

/-- Pad a finite family with radius-zero disks. -/
def ofFinite (N : ℕ) (center : Fin N → ℂ) (radius : Fin N → ℝ)
    (hnonneg : ∀ k, 0 ≤ radius k) : DiskFamily where
  center k := if hk : k < N then center ⟨k, hk⟩ else 0
  radius k := if hk : k < N then radius ⟨k, hk⟩ else 0
  radius_nonneg k := by split_ifs with hk; exact hnonneg _; exact le_rfl

theorem ofFinite_total_radius (N : ℕ) (center : Fin N → ℂ) (radius : Fin N → ℝ)
    (hnonneg : ∀ k, 0 ≤ radius k) :
    (∑' k, ENNReal.ofReal ((ofFinite N center radius hnonneg).radius k)) =
      ∑ k : Fin N, ENNReal.ofReal (radius k) := by
  rw [tsum_eq_sum (s := Finset.range N) (fun k hk => by
    have hk' : ¬ k < N := by simpa using hk
    simp only [ofFinite, dif_neg hk', ENNReal.ofReal_zero])]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [ofFinite, dif_pos (Finset.mem_range.1 hk)]

theorem mem_disks_ofFinite (N : ℕ) (center : Fin N → ℂ) (radius : Fin N → ℝ)
    (hnonneg : ∀ k, 0 ≤ radius k) (z : ℂ) :
    z ∈ disks (ofFinite N center radius hnonneg) ↔
      ∃ k : Fin N, z ∈ Metric.ball (center k) (radius k) := by
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    by_cases hkN : k < N
    · exact ⟨⟨k, hkN⟩, by simpa only [ofFinite, dif_pos hkN] using hk⟩
    · have hh : z ∈ Metric.ball (0 : ℂ) 0 := by
        simpa only [ofFinite, dif_neg hkN] using hk
      simp at hh
  · rintro ⟨k, hk⟩
    apply mem_iUnion.2
    exact ⟨k.val, by simpa only [ofFinite, dif_pos k.isLt] using hk⟩

/-- The finite-shell form: only a finite sum of real radii is required in each
shell, then zero padding and flattening produce the requested C₀ family. -/
theorem isC0_flatten_ofFinite (N : ℕ → ℕ) (center : ∀ n, Fin (N n) → ℂ)
    (radius : ∀ n, Fin (N n) → ℝ) (hnonneg : ∀ n k, 0 ≤ radius n k)
    {c : ℝ} (hc : 0 < c) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hblim : Tendsto b atTop (𝓝 0))
    (hcenter : ∀ n k, radius n k ≠ 0 → c * (2 : ℝ) ^ n ≤ ‖center n k‖)
    (hrow : ∀ n, (∑ k : Fin (N n), radius n k) ≤ b n * 2 ^ n) :
    IsC0 (flatten (fun n => ofFinite (N n) (center n) (radius n) (hnonneg n))) := by
  apply isC0_flatten _ hc b hb hblim
  · intro n k hk
    by_cases hkN : k < N n
    · simpa only [ofFinite, dif_pos hkN] using
        hcenter n ⟨k, hkN⟩ (by simpa only [ofFinite, dif_pos hkN] using hk)
    · simp only [ofFinite, dif_neg hkN, ne_eq, not_true_eq_false] at hk
  · intro n
    rw [ofFinite_total_radius, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => hnonneg n k)]
    exact ENNReal.ofReal_le_ofReal (hrow n)

/-- An explicit actual shell certificate. It includes nonvanishing, so the
real logarithm's convention at zero cannot certify a bad point. -/
def ShellCertificate (f : ℂ → ℂ) (ρ : ℝ) (h : Direction → ℝ)
    (n : ℕ) (D : DiskFamily) (error : ℝ) : Prop :=
  ∀ r : ℝ, r ∈ Icc ((2 : ℝ) ^ n) (2 ^ (n + 1)) → ∀ ζ : Direction,
    rayPoint r ζ ∉ disks D →
      f (rayPoint r ζ) ≠ 0 ∧ |normalizedLog f ρ r ζ - h ζ| ≤ error

/-- A certified family on all sufficiently late shells, with both errors and
radius budgets tending to zero, gives `DiskRegular`. The analytic certificate
is explicitly retained as an input. -/
theorem diskRegular_of_shell_certificates (f : ℂ → ℂ) (ρ : ℝ) (h : Direction → ℝ)
    (hh : Continuous h) (D : ℕ → DiskFamily) {c : ℝ} (hc : 0 < c)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hcenter : ∀ n k, (D n).radius k ≠ 0 → c * (2 : ℝ) ^ n ≤ ‖(D n).center k‖)
    (hrow : ∀ n, (∑' k, ENNReal.ofReal ((D n).radius k)) ≤ ENNReal.ofReal (b n * 2 ^ n))
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0))
    (hcert : ∀ᶠ n : ℕ in atTop, ShellCertificate f ρ h n (D n) (error n)) :
    DiskRegular f ρ h := by
  refine ⟨hh, flatten D, isC0_flatten D hc b hb hblim hcenter hrow, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hcert.and ((tendsto_order.1 herror).2 ε hε))
  refine ⟨(2 : ℝ) ^ N, by positivity, ?_⟩
  intro r hr ζ hz
  have hr1 : 1 ≤ r := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hr
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near hr1 (show (1 : ℝ) < 2 by norm_num)
  have hnN : N ≤ n := by
    by_contra hn
    have hp : (2 : ℝ) ^ (n + 1) ≤ 2 ^ N :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hpoint := (hN n hnN).1 r ⟨hn₁, hn₂.le⟩ ζ
    (fun hbad => hz ((mem_disks_flatten D _).2 ⟨n, hbad⟩))
  exact ⟨hpoint.1, hpoint.2.trans_lt (hN n hnN).2⟩

/-- A legal diagonal level: it tends to infinity, while every selected level
has already reached its own prescribed starting index. No growth rate of the
starting indices is assumed. -/
theorem exists_slow_index (T : ℕ → ℕ) :
    ∃ level : ℕ → ℕ, Tendsto level atTop atTop ∧
      ∀ n, T 0 ≤ n → T (level n) ≤ n := by
  classical
  let S : ℕ → Finset ℕ := fun n => (Finset.range (n + 1)).filter (fun k => T k ≤ n)
  have hS (n : ℕ) (hn : T 0 ≤ n) : (S n).Nonempty := by
    refine ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hn⟩⟩
  let level : ℕ → ℕ := fun n => if hn : T 0 ≤ n then (S n).max' (hS n hn) else 0
  refine ⟨level, ?_, ?_⟩
  · apply tendsto_atTop_atTop.2
    intro k
    refine ⟨max (T 0) (max k (T k)), ?_⟩
    intro n hn
    have hn0 : T 0 ≤ n := (le_max_left _ _).trans hn
    have hkn : k ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
    have hTkn : T k ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    dsimp [level]
    rw [dif_pos hn0]
    exact Finset.le_max' (S n) k (Finset.mem_filter.2
      ⟨Finset.mem_range.2 (by omega), hTkn⟩)
  · intro n hn
    dsimp [level]
    rw [dif_pos hn]
    exact (Finset.mem_filter.1 (Finset.max'_mem (S n) (hS n hn))).2

/-- Diagonalize shell certificates with arbitrarily delayed starting scales.
The analytic shell certificate and its radius/center estimates remain explicit. -/
theorem diskRegular_of_eventual_shell_certificates
    (f : ℂ → ℂ) (ρ : ℝ) (h : Direction → ℝ) (hh : Continuous h)
    {c : ℝ} (hc : 0 < c) (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hblim : Tendsto b atTop (𝓝 0)) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hlocal : ∀ j : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ D : DiskFamily,
      (∀ k, D.radius k ≠ 0 → c * (2 : ℝ) ^ n ≤ ‖D.center k‖) ∧
      (∑' k, ENNReal.ofReal (D.radius k)) ≤ ENNReal.ofReal (b j * 2 ^ n) ∧
      ShellCertificate f ρ h n D (error j)) :
    DiskRegular f ρ h := by
  classical
  choose T hT using hlocal
  obtain ⟨level, hlevel, hlegal⟩ := exists_slow_index T
  have hex : ∀ n : ℕ, ∃ D : DiskFamily,
      (∀ k, D.radius k ≠ 0 → c * (2 : ℝ) ^ n ≤ ‖D.center k‖) ∧
      (∑' k, ENNReal.ofReal (D.radius k)) ≤ ENNReal.ofReal (b (level n) * 2 ^ n) ∧
      (T 0 ≤ n → ShellCertificate f ρ h n D (error (level n))) := by
    intro n
    by_cases hn : T 0 ≤ n
    · obtain ⟨D, hDcenter, hDrow, hDcert⟩ := hT (level n) n (hlegal n hn)
      exact ⟨D, hDcenter, hDrow, fun _ => hDcert⟩
    · let D : DiskFamily := ⟨fun _ => 0, fun _ => 0, fun _ => le_rfl⟩
      refine ⟨D, ?_, ?_, fun h => False.elim (hn h)⟩
      · intro k hk
        exact False.elim (hk rfl)
      · simp only [D, ENNReal.ofReal_zero, tsum_zero]
        exact bot_le
  choose D hDcenter hDrow hDcert using hex
  apply diskRegular_of_shell_certificates f ρ h hh D hc
    (fun n => b (level n)) (fun n => hb (level n)) (hblim.comp hlevel)
    hDcenter hDrow (fun n => error (level n)) (herror.comp hlevel)
  filter_upwards [eventually_ge_atTop (T 0)] with n hn
  exact hDcert n hn

/-- Convenient interface with an independent positive error and radius budget.
It chooses both to tend geometrically to zero and then applies legal diagonalization. -/
theorem diskRegular_of_arbitrarily_small_shell_certificates
    (f : ℂ → ℂ) (ρ : ℝ) (h : Direction → ℝ) (hh : Continuous h)
    {c : ℝ} (hc : 0 < c)
    (hlocal : ∀ ε : ℝ, 0 < ε → ∀ b : ℝ, 0 < b →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ D : DiskFamily,
        (∀ k, D.radius k ≠ 0 → c * (2 : ℝ) ^ n ≤ ‖D.center k‖) ∧
        (∑' k, ENNReal.ofReal (D.radius k)) ≤ ENNReal.ofReal (b * 2 ^ n) ∧
        ShellCertificate f ρ h n D ε) : DiskRegular f ρ h := by
  let e : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ j
  have hepos (j : ℕ) : 0 < e j := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply diskRegular_of_eventual_shell_certificates f ρ h hh hc e
    (fun j => (hepos j).le) helim e helim
  intro j
  exact hlocal (e j) (hepos j) (e j) (hepos j)

/-- Real-scale finite shell interface for the forthcoming analytic Cartan
construction. The hypothesis explicitly supplies the actual finite disks and
pointwise shell estimate; this theorem only assembles and diagonalizes them. -/
theorem diskRegular_of_finite_shell_covers
    (f : ℂ → ℂ) (ρ : ℝ) (h : Direction → ℝ) (hh : Continuous h)
    {c : ℝ} (hc : 0 < c)
    (hlocal : ∀ ε : ℝ, 0 < ε → ∀ b : ℝ, 0 < b →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ m : ℕ, ∃ center : Fin m → ℂ, ∃ radius : Fin m → ℝ,
      ∃ _hnonneg : ∀ k, 0 ≤ radius k,
        (∀ k, radius k ≠ 0 → c * R ≤ ‖center k‖) ∧
        (∑ k : Fin m, radius k) ≤ b * R ∧
        ∀ r : ℝ, r ∈ Icc R (2 * R) → ∀ ζ : Direction,
          (∀ k : Fin m, rayPoint r ζ ∉ Metric.ball (center k) (radius k)) →
          f (rayPoint r ζ) ≠ 0 ∧ |normalizedLog f ρ r ζ - h ζ| ≤ ε) :
    DiskRegular f ρ h := by
  apply diskRegular_of_arbitrarily_small_shell_certificates f ρ h hh hc
  intro ε hε b hb
  obtain ⟨R₀, _, hR₀⟩ := hlocal ε hε b hb
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt R₀ (show (1 : ℝ) < 2 by norm_num)
  refine ⟨N, ?_⟩
  intro n hn
  have hRn : R₀ ≤ (2 : ℝ) ^ n := hN.le.trans (pow_le_pow_right₀ (by norm_num) hn)
  obtain ⟨m, center, radius, hnonneg, hcenter, hsum, hgood⟩ := hR₀ ((2 : ℝ) ^ n) hRn
  refine ⟨ofFinite m center radius hnonneg, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hkm : k < m
    · simpa only [ofFinite, dif_pos hkm] using
        hcenter ⟨k, hkm⟩ (by simpa only [ofFinite, dif_pos hkm] using hk)
    · simp only [ofFinite, dif_neg hkm, ne_eq, not_true_eq_false] at hk
  · rw [ofFinite_total_radius, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => hnonneg k)]
    exact ENNReal.ofReal_le_ofReal hsum
  · intro r hr ζ hz
    apply hgood r ⟨hr.1, by simpa only [pow_succ, mul_comm] using hr.2⟩ ζ
    intro k hk
    exact hz ((mem_disks_ofFinite m center radius hnonneg _).2 ⟨k, hk⟩)

end LevinDiskAssembly

#print axioms LevinDiskAssembly.mem_disks_flatten
#print axioms LevinDiskAssembly.radiusMass_flatten
#print axioms LevinDiskAssembly.weighted_partial_sum_le

#print axioms LevinDiskAssembly.radiusMass_eq_zero_below_scale
#print axioms LevinDiskAssembly.radiusMass_le_partial_sum
#print axioms LevinDiskAssembly.isC0_flatten

#print axioms LevinDiskAssembly.ofFinite_total_radius
#print axioms LevinDiskAssembly.mem_disks_ofFinite
#print axioms LevinDiskAssembly.isC0_flatten_ofFinite
#print axioms LevinDiskAssembly.diskRegular_of_shell_certificates

#print axioms LevinDiskAssembly.exists_slow_index
#print axioms LevinDiskAssembly.diskRegular_of_eventual_shell_certificates
#print axioms LevinDiskAssembly.diskRegular_of_arbitrarily_small_shell_certificates

#print axioms LevinDiskAssembly.diskRegular_of_finite_shell_covers
