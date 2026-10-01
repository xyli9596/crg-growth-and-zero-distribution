import CRGLinearKernelSubdivision

/-! Deletion of actual zero cells and detection of genuine endpoint jets.
Only extreme surviving cells are needed for the dominant endpoint in each
half-plane, so flat internal boundaries need not be joined first. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval BigOperators
namespace CRGLinearKernelActiveCells
open CRGLinearKernelIntegration CRGLinearKernelCancellation
open CRGLinearKernelSubdivision

variable {ι κ : Type*} [Fintype ι] {a b : ι → ℝ}

/-- Zero means zero as an analytic density in every component, rather than
zero of a finite truncation of an asymptotic expansion. -/
def cells (S : Subdivision a b) (v : κ → ℕ → ℝ → ℂ) : Finset ℕ := by
  classical
  exact (Finset.range S.count).filter fun i =>
    ∃ k : κ, ∃ t ∈ Icc (S.node i) (S.node (i+1)), v k i t ≠ 0

theorem mem_cells_iff (S : Subdivision a b) (v : κ → ℕ → ℝ → ℂ) (i : ℕ) :
    i ∈ cells S v ↔ i < S.count ∧
      ∃ k : κ, ∃ t ∈ Icc (S.node i) (S.node (i+1)), v k i t ≠ 0 := by
  classical
  simp [cells]

theorem kernel_zero_of_cell_deleted (S : Subdivision a b) (v : κ → ℕ → ℝ → ℂ)
    {i : ℕ} (hi : i < S.count) (hdel : i ∉ cells S v) (k : κ) (ζ : ℂ) :
    kernel (v k i) (S.node i) (S.node (i+1)) ζ = 0 := by
  have hz : ∀ t ∈ Icc (S.node i) (S.node (i+1)), v k i t = 0 := by
    intro t ht
    by_contra hne
    exact hdel ((mem_cells_iff S v i).mpr ⟨hi,k,t,ht,hne⟩)
  unfold kernel
  have he : (∫ t in S.node i..S.node (i+1), v k i t * Complex.exp (ζ*(t:ℂ))) =
      ∫ t in S.node i..S.node (i+1), (0:ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le ((S.increasing i (i+1) (Nat.lt_succ_self i)
      (Nat.succ_le_of_lt hi)).le)] at ht
    simp only [hz t ht, zero_mul]
  rw [he]
  simp

theorem sum_kernels_eq_surviving_cells (S : Subdivision a b)
    (v : κ → ℕ → ℝ → ℂ) (k : κ) (ζ : ℂ) :
    (∑ i ∈ Finset.range S.count, kernel (v k i) (S.node i) (S.node (i+1)) ζ) =
      ∑ i ∈ cells S v, kernel (v k i) (S.node i) (S.node (i+1)) ζ := by
  classical
  symm
  apply Finset.sum_subset (by intro i hi; exact Finset.mem_range.mpr ((mem_cells_iff S v i).mp hi).1)
  intro i hi hdel
  exact kernel_zero_of_cell_deleted S v (Finset.mem_range.mp hi) hdel k ζ

theorem sum_kernels_zero_of_no_cells (S : Subdivision a b)
    (v : κ → ℕ → ℝ → ℂ) (hempty : cells S v = ∅) (k : κ) (ζ : ℂ) :
    (∑ i ∈ Finset.range S.count, kernel (v k i) (S.node i) (S.node (i+1)) ζ) = 0 := by
  rw [sum_kernels_eq_surviving_cells,hempty]
  simp

theorem zero_on_interval_of_lower_jets_zero {v : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hv : AnalyticOnNhd ℝ v (Icc a b))
    (hj : ∀ j : ℕ, iteratedDeriv j v a = 0) : EqOn v 0 (Icc a b) := by
  have hva := hv a ⟨le_rfl,hab⟩
  have ho : ∀ n : ℕ, (n:ℕ∞) ≤ analyticOrderAt v a := fun n =>
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hva).mpr (fun j _=>hj j)
  have htop : analyticOrderAt v a=⊤ :=
    ENat.eq_of_forall_natCast_le_iff (fun n=>by simp [ho n])
  exact hv.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Icc
    ⟨le_rfl,hab⟩ (analyticOrderAt_eq_top.mp htop)

theorem exists_nonzero_upper_jet {v : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hv : AnalyticOnNhd ℝ v (Icc a b))
    (hne : ∃ t ∈ Icc a b, v t ≠ 0) : ∃ j : ℕ, iteratedDeriv j v b ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨t,ht,hne⟩ := hne
  exact hne (zero_on_interval_of_endpoint_jets_zero hab hv h ht)

theorem exists_nonzero_lower_jet {v : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hv : AnalyticOnNhd ℝ v (Icc a b))
    (hne : ∃ t ∈ Icc a b, v t ≠ 0) : ∃ j : ℕ, iteratedDeriv j v a ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨t,ht,hne⟩ := hne
  exact hne (zero_on_interval_of_lower_jets_zero hab hv h ht)

/-- The rightmost actual surviving cell has a nonzero finite upper jet in
some coefficient component. All other surviving endpoints lie to its left. -/
theorem extreme_upper_cell (S : Subdivision a b) (v : κ → ℕ → ℝ → ℂ)
    (hv : ∀ k i, i<S.count → AnalyticOnNhd ℝ (v k i)
      (Icc (S.node i) (S.node (i+1)))) (hne : (cells S v).Nonempty) :
    ∃ m ∈ cells S v, (∀ i ∈ cells S v, i ≤ m) ∧
      ∃ k : κ, ∃ j : ℕ, iteratedDeriv j (v k m) (S.node (m+1)) ≠ 0 := by
  classical
  let m := (cells S v).max' hne
  have hm : m ∈ cells S v := Finset.max'_mem _ _
  obtain ⟨hmcount,k,t,ht,hvt⟩ := (mem_cells_iff S v m).mp hm
  obtain ⟨j,hj⟩ := exists_nonzero_upper_jet
    ((S.increasing m (m+1) (Nat.lt_succ_self m) (Nat.succ_le_of_lt hmcount)).le)
    (hv k m hmcount) ⟨t,ht,hvt⟩
  exact ⟨m,hm,fun i hi => Finset.le_max' _ _ hi,k,j,hj⟩

/-- The analogous genuine lower endpoint for the other half-plane. -/
theorem extreme_lower_cell (S : Subdivision a b) (v : κ → ℕ → ℝ → ℂ)
    (hv : ∀ k i, i<S.count → AnalyticOnNhd ℝ (v k i)
      (Icc (S.node i) (S.node (i+1)))) (hne : (cells S v).Nonempty) :
    ∃ m ∈ cells S v, (∀ i ∈ cells S v, m ≤ i) ∧
      ∃ k : κ, ∃ j : ℕ, iteratedDeriv j (v k m) (S.node m) ≠ 0 := by
  classical
  let m := (cells S v).min' hne
  have hm : m ∈ cells S v := Finset.min'_mem _ _
  obtain ⟨hmcount,k,t,ht,hvt⟩ := (mem_cells_iff S v m).mp hm
  obtain ⟨j,hj⟩ := exists_nonzero_lower_jet
    ((S.increasing m (m+1) (Nat.lt_succ_self m) (Nat.succ_le_of_lt hmcount)).le)
    (hv k m hmcount) ⟨t,ht,hvt⟩
  exact ⟨m,hm,fun i hi => Finset.min'_le _ _ hi,k,j,hj⟩

#print axioms kernel_zero_of_cell_deleted
#print axioms sum_kernels_eq_surviving_cells
#print axioms extreme_upper_cell
#print axioms extreme_lower_cell
end CRGLinearKernelActiveCells
