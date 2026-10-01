import CRGLinearKernelCancellation
import Mathlib.Data.Finset.Sort

/-! Exact subdivision of finitely many real interval densities. The common
partition is constructed from their actual endpoints. Its cell densities
are sums of precisely the weights supported on that cell. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval BigOperators
namespace CRGLinearKernelSubdivision
open CRGLinearKernelIntegration CRGLinearKernelCancellation

structure Subdivision {ι : Type*} (a b : ι → ℝ) where
  count : ℕ
  node : ℕ → ℝ
  increasing : ∀ i j : ℕ, i < j → j ≤ count → node i < node j
  lower : ι → ℕ
  upper : ι → ℕ
  lower_lt_upper : ∀ ell, lower ell < upper ell
  upper_le_count : ∀ ell, upper ell ≤ count
  lower_node : ∀ ell, node (lower ell) = a ell
  upper_node : ∀ ell, node (upper ell) = b ell

theorem exists_subdivision {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (hab : ∀ ell, a ell < b ell) : Nonempty (Subdivision a b) := by
  classical
  let E : Finset ℝ := (Finset.univ.image a ∪ Finset.univ.image b) ∪ {0, 1}
  have hE0 : (0 : ℝ) ∈ E := by simp [E]
  have hEpos : 0 < E.card := Finset.card_pos.mpr ⟨0, hE0⟩
  let e : Fin E.card ≃o E := E.orderIsoOfFin rfl
  have ha (ell : ι) : a ell ∈ E := by simp [E]
  have hb (ell : ι) : b ell ∈ E := by simp [E]
  let l : ι → Fin E.card := fun ell => e.symm ⟨a ell, ha ell⟩
  let u : ι → Fin E.card := fun ell => e.symm ⟨b ell, hb ell⟩
  let node : ℕ → ℝ := fun i => if hi : i < E.card then (e ⟨i, hi⟩ : ℝ) else 0
  refine ⟨⟨E.card - 1, node, ?_, fun ell => (l ell).val,
    fun ell => (u ell).val, ?_, ?_, ?_, ?_⟩⟩
  · intro i j hij hj
    have hiE : i < E.card := by omega
    have hjE : j < E.card := by omega
    simp only [node, dif_pos hiE, dif_pos hjE]
    exact e.strictMono (show (⟨i, hiE⟩ : Fin E.card) < ⟨j, hjE⟩ from hij)
  · intro ell
    exact e.symm.strictMono (show (⟨a ell, ha ell⟩ : E) < ⟨b ell, hb ell⟩ from hab ell)
  · intro ell
    have hu := (u ell).isLt
    omega
  · intro ell
    simp only [node, dif_pos (l ell).isLt]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨a ell, ha ell⟩)
  · intro ell
    simp only [node, dif_pos (u ell).isLt]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨b ell, hb ell⟩)

variable {ι κ : Type*} [Fintype ι] {a b : ι → ℝ}

theorem Subdivision.node_le (S : Subdivision a b) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ S.count) : S.node i ≤ S.node j := by
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (S.increasing i j hlt hj).le

abbrev Subdivision.active (S : Subdivision a b) (ell : ι) (i : ℕ) : Prop :=
  S.lower ell ≤ i ∧ i < S.upper ell

def Subdivision.cellWeight (S : Subdivision a b) (v : κ → ι → ℝ → ℂ)
    (k : κ) (i : ℕ) (t : ℝ) : ℂ :=
  ∑ ell : ι, if S.active ell i then v k ell t else 0

theorem Subdivision.cell_subset (S : Subdivision a b) {ell : ι} {i : ℕ}
    (hi : S.active ell i) : Icc (S.node i) (S.node (i + 1)) ⊆ Icc (a ell) (b ell) := by
  intro t ht
  have hlow := S.node_le hi.1 ((Nat.le_of_lt hi.2).trans (S.upper_le_count ell))
  have hupp := S.node_le (Nat.succ_le_of_lt hi.2) (S.upper_le_count ell)
  rw [S.lower_node] at hlow
  rw [S.upper_node] at hupp
  exact ⟨hlow.trans ht.1, ht.2.trans hupp⟩

theorem Subdivision.cellWeight_analytic (S : Subdivision a b)
    (v : κ → ι → ℝ → ℂ)
    (hv : ∀ k ell, AnalyticOnNhd ℝ (v k ell) (Icc (a ell) (b ell)))
    (k : κ) (i : ℕ) :
    AnalyticOnNhd ℝ (S.cellWeight v k i) (Icc (S.node i) (S.node (i + 1))) := by
  classical
  unfold cellWeight
  apply Finset.univ.analyticOnNhd_fun_sum
  intro ell _
  by_cases hi : S.active ell i
  · simpa only [if_pos hi] using (hv k ell).mono (S.cell_subset hi)
  · simp only [if_neg hi]
    exact analyticOnNhd_const

theorem Subdivision.kernel_eq_cell_sum (S : Subdivision a b)
    (v : ι → ℝ → ℂ)
    (hv : ∀ ell, ContinuousOn (v ell) (Icc (a ell) (b ell))) (ell : ι) (ζ : ℂ) :
    kernel (v ell) (a ell) (b ell) ζ =
      ∑ i ∈ Finset.range S.count,
        if S.active ell i then kernel (v ell) (S.node i) (S.node (i + 1)) ζ else 0 := by
  classical
  have hi : ∀ i ∈ Finset.Ico (S.lower ell) (S.upper ell),
      IntervalIntegrable (fun t : ℝ => v ell t * Complex.exp (ζ * (t : ℂ))) volume
        (S.node i) (S.node (i + 1)) := by
    intro i hi
    have hactive : S.active ell i := by simpa only [active, Finset.mem_Ico] using hi
    have hcont := ((hv ell).mono (S.cell_subset hactive)).mul
      (show ContinuousOn (fun t : ℝ => Complex.exp (ζ * (t : ℂ)))
        (Icc (S.node i) (S.node (i + 1))) by fun_prop)
    exact hcont.intervalIntegrable_of_Icc
      ((S.increasing i (i + 1) (Nat.lt_succ_self i)
        ((Nat.succ_le_of_lt hactive.2).trans (S.upper_le_count ell))).le)
  have ht := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := S.node) (f := fun t : ℝ => v ell t * Complex.exp (ζ * (t : ℂ)))
    (S.lower_lt_upper ell).le (fun i hiSet => hi i (by simpa using hiSet))
  rw [S.lower_node, S.upper_node] at ht
  change (∑ i ∈ Finset.Ico (S.lower ell) (S.upper ell),
    kernel (v ell) (S.node i) (S.node (i+1)) ζ) = kernel (v ell) (a ell) (b ell) ζ at ht
  rw [← ht]
  symm
  calc
    (∑ i ∈ Finset.range S.count, if S.active ell i then
      kernel (v ell) (S.node i) (S.node (i + 1)) ζ else 0) =
      ∑ i ∈ (Finset.range S.count).filter (S.active ell),
        kernel (v ell) (S.node i) (S.node (i + 1)) ζ := by
          rw [Finset.sum_filter]
    _ = ∑ i ∈ Finset.Ico (S.lower ell) (S.upper ell),
        kernel (v ell) (S.node i) (S.node (i + 1)) ζ := by
          congr 1
          ext i
          simp only [Finset.mem_filter, Finset.mem_range, active, Finset.mem_Ico]
          constructor
          · exact fun h => h.2
          · intro h
            exact ⟨h.2.trans_le (S.upper_le_count ell), h⟩
    _ = _ := rfl

/-- The analytic densities on overlapping intervals are actually added,
and their cell integrals exactly equal the original finite sum. -/
theorem Subdivision.sum_kernels_eq_cellWeights (S : Subdivision a b)
    (v : κ → ι → ℝ → ℂ)
    (hv : ∀ k ell, AnalyticOnNhd ℝ (v k ell) (Icc (a ell) (b ell)))
    (k : κ) (ζ : ℂ) :
    (∑ ell : ι, kernel (v k ell) (a ell) (b ell) ζ) =
      ∑ i ∈ Finset.range S.count,
        kernel (S.cellWeight v k i) (S.node i) (S.node (i + 1)) ζ := by
  classical
  simp_rw [S.kernel_eq_cell_sum (v k) (fun ell => (hv k ell).continuousOn) _ ζ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hif (ell : ι) :
      (if S.active ell i then kernel (v k ell) (S.node i) (S.node (i + 1)) ζ else 0) =
      kernel (fun t => if S.active ell i then v k ell t else 0)
        (S.node i) (S.node (i + 1)) ζ := by
    by_cases ha : S.active ell i
    · simp only [if_pos ha]
    · simp only [if_neg ha, kernel, zero_mul, intervalIntegral.integral_zero]
  simp_rw [hif]
  unfold cellWeight kernel
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [Finset.sum_mul]
  · intro ell _
    by_cases ha : S.active ell i
    · simp only [if_pos ha]
      exact (((hv k ell).continuousOn.mono (S.cell_subset ha)).mul
        (show ContinuousOn (fun t : ℝ => Complex.exp (ζ * (t : ℂ)))
          (Icc (S.node i) (S.node (i + 1))) by fun_prop)).intervalIntegrable_of_Icc
        ((S.increasing i (i+1) (Nat.lt_succ_self i)
          (Nat.succ_le_of_lt (Finset.mem_range.mp hi))).le)
    · simp only [if_neg ha, zero_mul]
      exact intervalIntegrable_const

#print axioms exists_subdivision
#print axioms Subdivision.cellWeight_analytic
#print axioms Subdivision.kernel_eq_cell_sum
#print axioms Subdivision.sum_kernels_eq_cellWeights
end CRGLinearKernelSubdivision
