import LevinCartan
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Calculus.LogDeriv

/-! The reciprocal-distance form of Cartan's finite-point covering. This is the
kernel estimate needed for logarithmic derivatives; a product lower bound alone
would lose an additional factor equal to the number of zeros. -/
noncomputable section
open Set Metric
open scoped BigOperators
namespace GundersenCartan

theorem reciprocal_sum_of_spread_fin {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ)
    {H : ℝ} (hH : 0 < H)
    (hspread : ∀ s : Finset (Fin n), s.Nonempty →
      ∃ i ∈ s, H * (s.card : ℝ) / n ≤ d i) :
    (∀ i, 0 < d i) ∧ ∑ i, (d i)⁻¹ ≤ (n : ℝ) / H * (1 + Real.log n) := by
  classical
  let σ := Tuple.sort d
  have hmono : Monotone (d ∘ σ) := Tuple.monotone_sort d
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hord (k : Fin n) : H * ((k.val : ℝ) + 1) / n ≤ d (σ k) := by
    let s := (Finset.Iic k).image σ
    have hs : s.Nonempty := ⟨σ k, Finset.mem_image.mpr ⟨k, Finset.mem_Iic.mpr le_rfl, rfl⟩⟩
    have hc : s.card = k.val + 1 := by
      rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iic]
    obtain ⟨i, hi, hb⟩ := hspread s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [hc, Nat.cast_add, Nat.cast_one] at hb
    exact hb.trans (hmono (Finset.mem_Iic.mp hj))
  have hpos (i : Fin n) : 0 < d i := by
    obtain ⟨k, rfl⟩ := σ.surjective i
    exact (div_pos (mul_pos hH (by positivity)) hnr).trans_le (hord k)
  refine ⟨hpos, ?_⟩
  have hsum : ∑ k : Fin n, (d (σ k))⁻¹ ≤
      ∑ k : Fin n, ((n : ℝ) / H) * (((k.val : ℝ) + 1)⁻¹) := by
    apply Finset.sum_le_sum
    intro k _
    calc
      (d (σ k))⁻¹ ≤ (H * ((k.val : ℝ) + 1) / n)⁻¹ :=
        inv_anti₀ (by positivity) (hord k)
      _ = _ := by field_simp
  rw [Equiv.sum_comp σ (fun i => (d i)⁻¹), ← Finset.mul_sum] at hsum
  have hh : (∑ k : Fin n, ((k.val : ℝ) + 1)⁻¹) = (harmonic n : ℝ) := by
    rw [show (∑ k : Fin n, ((k.val : ℝ) + 1)⁻¹) =
      ∑ k ∈ Finset.range n, ((k : ℝ) + 1)⁻¹ from
      Fin.sum_univ_eq_sum_range (fun k : ℕ => ((k : ℝ) + 1)⁻¹) n]
    simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hh] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) (by positivity))

theorem reciprocal_sum_of_spread {ι : Type*} [Fintype ι] (d : ι → ℝ)
    {H : ℝ} (hH : 0 < H) (hN : 0 < Fintype.card ι)
    (hspread : ∀ s : Finset ι, s.Nonempty →
      ∃ i ∈ s, H * (s.card : ℝ) / Fintype.card ι ≤ d i) :
    (∀ i, 0 < d i) ∧
      ∑ i, (d i)⁻¹ ≤ (Fintype.card ι : ℝ) / H * (1 + Real.log (Fintype.card ι)) := by
  classical
  let e := Fintype.equivFin ι
  have hs : ∀ s : Finset (Fin (Fintype.card ι)), s.Nonempty →
      ∃ i ∈ s, H * (s.card : ℝ) / Fintype.card ι ≤ d (e.symm i) := by
    intro s hs
    obtain ⟨i, hi, hb⟩ := hspread (s.image e.symm) (hs.image e.symm)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [Finset.card_image_of_injective _ e.symm.injective] at hb
    exact ⟨j, hj, hb⟩
  obtain ⟨hp, hb⟩ := reciprocal_sum_of_spread_fin hN (fun i => d (e.symm i)) hH hs
  refine ⟨fun i => ?_, ?_⟩
  · simpa using hp (e i)
  · simpa only [Equiv.sum_comp e.symm (fun i => (d i)⁻¹)] using hb

/-- Actual finite disks controlling the whole sum of inverse zero distances,
including multiplicity, with the sharp harmonic loss N log N / H. -/
theorem exists_disks_reciprocal_bound {ι : Type*} [Fintype ι] (a : ι → ℂ)
    {H : ℝ} (hH : 0 < H) :
    ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ r : Fin m → ℝ,
      (∀ j, 0 < r j) ∧ (∑ j, r j) ≤ 5 * H ∧
      ∀ z : ℂ, (∀ j, z ∉ ball (c j) (r j)) →
        (∀ i, z ≠ a i) ∧ ∑ i, ‖z - a i‖⁻¹ ≤
          (Fintype.card ι : ℝ) / H * (1 + Real.log (Fintype.card ι)) := by
  classical
  by_cases hzero : Fintype.card ι = 0
  · let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hzero
    refine ⟨0, Fin.elim0, Fin.elim0, (fun j => Fin.elim0 j), ?_, ?_⟩
    · simp; positivity
    · intro z _
      simp
  obtain ⟨m, c, r, hr, hsum, hs⟩ :=
    LevinCartan.exists_disks_distance_property a hH (Nat.pos_of_ne_zero hzero)
  refine ⟨m, c, r, hr, hsum, fun z hz => ?_⟩
  obtain ⟨hp, hb⟩ := reciprocal_sum_of_spread (fun i => ‖z - a i‖) hH
    (Nat.pos_of_ne_zero hzero) (by simpa only [dist_eq_norm] using hs z hz)
  exact ⟨fun i => sub_ne_zero.mp (norm_pos_iff.mp (hp i)), hb⟩

/-- The logarithmic derivative of a finite zero product is the actual sum of
simple-pole kernels. Repeated zero locations encode multiplicity. -/
theorem logDeriv_zero_product {ι : Type*} [Fintype ι] (a : ι → ℂ) {z : ℂ}
    (hz : ∀ i, z ≠ a i) :
    logDeriv (fun w : ℂ => ∏ i, (w - a i)) z = ∑ i, (z - a i)⁻¹ := by
  rw [logDeriv_prod (s := Finset.univ) (f := fun i => fun w : ℂ => w - a i)
    (fun i _ => sub_ne_zero.mpr (hz i))
    (fun i _ => differentiableAt_id.sub_const (a i))]
  apply Finset.sum_congr rfl
  intro i _
  simp [logDeriv]

/-- The analytic zero-product logarithmic derivative has the Cartan bound
outside disks with total radius at most 5H. -/
theorem exists_disks_logDeriv_product_bound {ι : Type*} [Fintype ι] (a : ι → ℂ)
    {H : ℝ} (hH : 0 < H) :
    ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ r : Fin m → ℝ,
      (∀ j, 0 < r j) ∧ (∑ j, r j) ≤ 5 * H ∧
      ∀ z : ℂ, (∀ j, z ∉ ball (c j) (r j)) →
        (∀ i, z ≠ a i) ∧
        ‖logDeriv (fun w : ℂ => ∏ i, (w - a i)) z‖ ≤
          (Fintype.card ι : ℝ) / H * (1 + Real.log (Fintype.card ι)) := by
  obtain ⟨m, c, r, hr, hs, hb⟩ := exists_disks_reciprocal_bound a hH
  refine ⟨m, c, r, hr, hs, fun z hz => ?_⟩
  obtain ⟨hnz, hbound⟩ := hb z hz
  refine ⟨hnz, ?_⟩
  rw [logDeriv_zero_product a hnz]
  exact (norm_sum_le _ _).trans (by simpa only [norm_inv] using hbound)

#print axioms reciprocal_sum_of_spread_fin
#print axioms reciprocal_sum_of_spread
#print axioms exists_disks_reciprocal_bound
#print axioms logDeriv_zero_product
#print axioms exists_disks_logDeriv_product_bound
end GundersenCartan
