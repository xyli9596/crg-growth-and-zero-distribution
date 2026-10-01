import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Finite-point Cartan covering

The proof uses the metric Vitali covering theorem with enlargement factor five.
Points are indexed, so repeated locations retain their multiplicities.
-/

noncomputable section
open Set Metric
open scoped BigOperators

namespace LevinCartan

/-- Disjoint selected balls account for disjoint, nonempty sets of point
indices. Their total radius is at most `H`, and fivefold enlargement covers
every ball containing too many indexed points for its radius. -/
theorem exists_selected_balls {ι : Type*} [Fintype ι] (a : ι → ℂ)
    {H : ℝ} (hH : 0 < H) (hN : 0 < Fintype.card ι) :
    ∃ D : Finset (ℂ × Finset ι),
      (∀ d ∈ D, d.2.Nonempty) ∧
      (∑ d ∈ D, H * (d.2.card : ℝ) / Fintype.card ι) ≤ H ∧
      ∀ z : ℂ, ∀ s : Finset ι, s.Nonempty →
        (∀ i ∈ s, dist z (a i) < H * (s.card : ℝ) / Fintype.card ι) →
        ∃ d ∈ D, z ∈ ball d.1 (5 * (H * (d.2.card : ℝ) / Fintype.card ι)) := by
  classical
  let r : ℂ × Finset ι → ℝ := fun d => H * (d.2.card : ℝ) / Fintype.card ι
  let T : Set (ℂ × Finset ι) :=
    {d | d.2.Nonempty ∧ ∀ i ∈ d.2, a i ∈ ball d.1 (r d)}
  have hNr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have hrpos (d : ℂ × Finset ι) (hd : d ∈ T) : 0 < r d := by
    have hs : (0 : ℝ) < d.2.card := by exact_mod_cast hd.1.card_pos
    exact div_pos (mul_pos hH hs) hNr
  have hrle (d : ℂ × Finset ι) (_hd : d ∈ T) : r d ≤ H := by
    apply (div_le_iff₀ hNr).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_univ d.2) hH.le
  obtain ⟨U, hUT, hUdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball T Prod.fst r H hrle
      5 (by norm_num)
  have hindexDisj : U.PairwiseDisjoint (fun d => d.2) := by
    intro d hd e he hde
    apply Finset.disjoint_left.mpr
    intro i hid hie
    exact Set.disjoint_left.mp (hUdisj hd he hde) ((hUT hd).2 i hid) ((hUT he).2 i hie)
  have hsinj : Set.InjOn Prod.snd U := by
    intro d hd e he hde
    by_contra hne
    obtain ⟨i, hi⟩ := (hUT hd).1
    exact Finset.disjoint_left.mp (hindexDisj hd he hne) hi (by simpa only [← hde] using hi)
  have hUf : U.Finite := (Set.toFinite (Prod.snd '' U)).of_finite_image hsinj
  let D := hUf.toFinset
  have hDU (d : ℂ × Finset ι) : d ∈ D ↔ d ∈ U := hUf.mem_toFinset
  have hDdisj : (D : Set (ℂ × Finset ι)).PairwiseDisjoint (fun d => d.2) := by
    intro d hd e he hde
    exact hindexDisj ((hDU d).mp hd) ((hDU e).mp he) hde
  have hcard : ∑ d ∈ D, d.2.card ≤ Fintype.card ι := by
    rw [← Finset.card_biUnion hDdisj]
    exact Finset.card_le_univ _
  have hcardr : ∑ d ∈ D, (d.2.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
  refine ⟨D, fun d hd => (hUT ((hDU d).mp hd)).1, ?_, ?_⟩
  · rw [← Finset.sum_div, ← Finset.mul_sum]
    exact (div_le_iff₀ hNr).mpr (mul_le_mul_of_nonneg_left hcardr hH.le)
  · intro z s hs hnear
    have hT : (z, s) ∈ T := by
      refine ⟨hs, fun i hi => ?_⟩
      simpa only [mem_ball, dist_comm, r] using hnear i hi
    obtain ⟨d, hd, hsub⟩ := hcover (z, s) hT
    exact ⟨d, (hDU d).mpr hd, hsub (mem_ball_self (hrpos (z, s) hT))⟩

/-- A finite disk family with controlled total radius and the indexed-distance
property underlying Cartan's product estimate. -/
theorem exists_disks_distance_property {ι : Type*} [Fintype ι] (a : ι → ℂ)
    {H : ℝ} (hH : 0 < H) (hN : 0 < Fintype.card ι) :
    ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ r : Fin m → ℝ,
      (∀ j, 0 < r j) ∧ (∑ j, r j) ≤ 5 * H ∧
      ∀ z : ℂ, (∀ j, z ∉ ball (c j) (r j)) →
        ∀ s : Finset ι, s.Nonempty →
          ∃ i ∈ s, H * (s.card : ℝ) / Fintype.card ι ≤ dist z (a i) := by
  classical
  obtain ⟨D, hDne, hDsum, hDcover⟩ := exists_selected_balls a hH hN
  let e := Fintype.equivFin D
  let c : Fin (Fintype.card D) → ℂ := fun j => (e.symm j).val.1
  let r : Fin (Fintype.card D) → ℝ := fun j =>
    5 * (H * ((e.symm j).val.2.card : ℝ) / Fintype.card ι)
  refine ⟨Fintype.card D, c, r, ?_, ?_, ?_⟩
  · intro j
    have hc : 0 < (e.symm j).val.2.card := (hDne _ (e.symm j).property).card_pos
    have hcr : (0 : ℝ) < (e.symm j).val.2.card := by exact_mod_cast hc
    have hNr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
    dsimp [r]
    positivity
  · have heq : (∑ j, r j) = ∑ d ∈ D, 5 * (H * (d.2.card : ℝ) / Fintype.card ι) := by
      rw [show (∑ j, r j) = ∑ d : D, 5 * (H * (d.val.2.card : ℝ) / Fintype.card ι) from
        e.symm.sum_comp (fun d : D => 5 * (H * (d.val.2.card : ℝ) / Fintype.card ι))]
      exact Finset.sum_coe_sort D
        (fun d : ℂ × Finset ι => 5 * (H * (d.2.card : ℝ) / Fintype.card ι))
    rw [heq, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hDsum (by norm_num)
  · intro z hz s hs
    by_contra hbad
    push Not at hbad
    obtain ⟨d, hd, hmem⟩ := hDcover z s hs hbad
    have he : e.symm (e ⟨d, hd⟩) = ⟨d, hd⟩ := e.symm_apply_apply _
    exact hz (e ⟨d, hd⟩) (by simpa only [c, r, he] using hmem)

/-- The elementary lower factorial estimate, with an exponential rather than
an `N log N` loss. -/
theorem factorial_lower (n : ℕ) : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
    apply Real.one_le_sqrt.mpr
    have hp := mul_le_mul_of_nonneg_left hn1 Real.pi_pos.le
    nlinarith [Real.one_le_pi_div_two]
  exact (le_mul_of_one_le_left (by positivity) hsqrt).trans (Stirling.le_factorial_stirling n)

/-- A finite tuple satisfying the indexed distance property has Cartan's
product lower bound. Sorting retains repeated values and their multiplicities. -/
theorem prod_lower_of_spread_fin {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ)
    {H : ℝ} (hH : 0 < H)
    (hspread : ∀ s : Finset (Fin n), s.Nonempty →
      ∃ i ∈ s, H * (s.card : ℝ) / n ≤ d i) :
    (H / Real.exp 1) ^ n ≤ ∏ i, d i := by
  classical
  let σ := Tuple.sort d
  have hmono : Monotone (d ∘ σ) := Tuple.monotone_sort d
  have hNr : (0 : ℝ) < n := by exact_mod_cast hn
  have hordered (k : Fin n) : H * ((k.val : ℝ) + 1) / n ≤ d (σ k) := by
    let s := (Finset.Iic k).image σ
    have hs : s.Nonempty := ⟨σ k, Finset.mem_image.mpr ⟨k, Finset.mem_Iic.mpr le_rfl, rfl⟩⟩
    have hcard : s.card = k.val + 1 := by
      rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iic]
    obtain ⟨i, hi, hbound⟩ := hspread s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hle : d (σ j) ≤ d (σ k) := hmono (Finset.mem_Iic.mp hj)
    rw [hcard, Nat.cast_add, Nat.cast_one] at hbound
    exact hbound.trans hle
  have hprod := Finset.prod_le_prod
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
      show 0 ≤ H * ((k.val : ℝ) + 1) / n by positivity)
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) => hordered k)
  have hfac : (∏ k : Fin n, ((k.val : ℝ) + 1)) = (n.factorial : ℝ) := by
    rw [show (∏ k : Fin n, ((k.val : ℝ) + 1)) = ∏ k ∈ Finset.range n, ((k : ℝ) + 1) from
      Fin.prod_univ_eq_prod_range (fun k : ℕ => (k : ℝ) + 1) n]
    exact_mod_cast Finset.prod_range_add_one_eq_factorial n
  have hprodEq : (∏ k : Fin n, H * ((k.val : ℝ) + 1) / n) =
      (H / n) ^ n * (n.factorial : ℝ) := by
    simp_rw [show ∀ k : Fin n, H * ((k.val : ℝ) + 1) / n =
      (H / n) * ((k.val : ℝ) + 1) by intro k; ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hfac]
  rw [hprodEq, Equiv.prod_comp σ d] at hprod
  calc
    (H / Real.exp 1) ^ n = (H / n) ^ n * ((n : ℝ) / Real.exp 1) ^ n := by
      rw [← mul_pow]
      congr 1
      field_simp
    _ ≤ (H / n) ^ n * (n.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left (factorial_lower n) (by positivity)
    _ ≤ _ := hprod

/-- The product estimate for any finite index type, including repeated values. -/
theorem prod_lower_of_spread {ι : Type*} [Fintype ι] (d : ι → ℝ)
    {H : ℝ} (hH : 0 < H) (hN : 0 < Fintype.card ι)
    (hspread : ∀ s : Finset ι, s.Nonempty →
      ∃ i ∈ s, H * (s.card : ℝ) / Fintype.card ι ≤ d i) :
    (H / Real.exp 1) ^ Fintype.card ι ≤ ∏ i, d i := by
  classical
  let e := Fintype.equivFin ι
  have hspreadFin : ∀ s : Finset (Fin (Fintype.card ι)), s.Nonempty →
      ∃ i ∈ s, H * (s.card : ℝ) / Fintype.card ι ≤ d (e.symm i) := by
    intro s hs
    have hs' : (s.image e.symm).Nonempty := hs.image e.symm
    obtain ⟨i, hi, hbound⟩ := hspread (s.image e.symm) hs'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [Finset.card_image_of_injective _ e.symm.injective] at hbound
    exact ⟨j, hj, hbound⟩
  have hp := prod_lower_of_spread_fin hN (fun i => d (e.symm i)) hH hspreadFin
  rwa [Equiv.prod_comp e.symm d] at hp

/-- Finite-point Cartan inequality with total exceptional radius at most `5H`.
There is no separation hypothesis, and repeated points encode multiplicities.
Outside the open disks every point distance is positive and the product is at
least `(H / exp 1)^N`, so the logarithmic loss is linear in the point count. -/
theorem exists_disks_product_bound {ι : Type*} [Fintype ι] (a : ι → ℂ)
    {H : ℝ} (hH : 0 < H) :
    ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ r : Fin m → ℝ,
      (∀ j, 0 < r j) ∧ (∑ j, r j) ≤ 5 * H ∧
      ∀ z : ℂ, (∀ j, z ∉ ball (c j) (r j)) →
        (∀ i, z ≠ a i) ∧ (H / Real.exp 1) ^ Fintype.card ι ≤ ∏ i, ‖z - a i‖ := by
  classical
  by_cases hzero : Fintype.card ι = 0
  · let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hzero
    refine ⟨0, (fun j => Fin.elim0 j), (fun j => Fin.elim0 j),
      (fun j => Fin.elim0 j), ?_, ?_⟩
    · simp only [Fin.sum_univ_zero]
      positivity
    · intro z _
      exact ⟨fun i => isEmptyElim i, by simp⟩
  have hN : 0 < Fintype.card ι := Nat.pos_of_ne_zero hzero
  have hNr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  obtain ⟨m, c, r, hrpos, hsum, hspread⟩ := exists_disks_distance_property a hH hN
  refine ⟨m, c, r, hrpos, hsum, ?_⟩
  intro z hz
  constructor
  · intro i
    obtain ⟨j, hj, hdist⟩ := hspread z hz {i} (Finset.singleton_nonempty i)
    have hji : j = i := Finset.mem_singleton.mp hj
    subst j
    have hdist' : H / Fintype.card ι ≤ dist z (a i) := by simpa using hdist
    exact dist_pos.mp ((div_pos hH hNr).trans_le hdist')
  · apply prod_lower_of_spread (fun i => ‖z - a i‖) hH hN
    intro s hs
    simpa only [dist_eq_norm] using hspread z hz s hs

#print axioms exists_selected_balls
#print axioms exists_disks_distance_property
#print axioms factorial_lower
#print axioms prod_lower_of_spread_fin
#print axioms prod_lower_of_spread
#print axioms exists_disks_product_bound

end LevinCartan
