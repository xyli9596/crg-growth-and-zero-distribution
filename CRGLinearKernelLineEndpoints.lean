import CRGLinearKernelLinePackets
import CRGLinearKernelNonzeroInterior
import CRGLinearKernelLineGeometry

/-! Canonical genuine extreme endpoint densities of each nonzero supporting
line, constructed from the original Corollary 5.2 coefficient data. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval BigOperators
namespace CRGLinearKernelLineEndpoints
open CRGLinearKernel CRGLinearKernelIntegration CRGLinearKernelEntire
open CRGLinearKernelLines CRGLinearKernelSubdivision CRGLinearKernelActiveCells
open CRGLinearKernelLinePackets CRGLinearKernelNonzeroInterior
variable {n : ℕ}

def activeLines (D : CoefficientData n) : Finset ℂ := by
  classical
  exact (lines D).filter fun q => (survivingCells D q).Nonempty

theorem mem_activeLines (D : CoefficientData n) (q : ℂ) :
    q ∈ activeLines D ↔ q ∈ lines D ∧ (survivingCells D q).Nonempty := by
  classical
  simp [activeLines]

/-- Removal of zero supporting lines is an identity of the actual entire
coefficients, rather than removal of an asymptotic zero series. -/
theorem coefficient_eq_active_packets (D : CoefficientData n) (k : Fin n) (z : ℂ) :
    D.coefficient k z=D.exponential k z+∑ q ∈ activeLines D,packet D q k z := by
  rw [CoefficientData.coefficient,integral_sum_eq_packets]
  congr 1
  symm
  apply Finset.sum_subset (by intro q hq;exact ((mem_activeLines D q).mp hq).1)
  intro q hq hdel
  have hempty : survivingCells D q=∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hne
    exact hdel ((mem_activeLines D q).mpr ⟨hq,hne⟩)
  exact packet_zero_of_no_cells D q hempty k z

def upperCell (D : CoefficientData n) (q : ℂ) : ℕ :=
  if h : (survivingCells D q).Nonempty then (survivingCells D q).max' h else 0

def lowerCell (D : CoefficientData n) (q : ℂ) : ℕ :=
  if h : (survivingCells D q).Nonempty then (survivingCells D q).min' h else 0

def upperEnd (D : CoefficientData n) (q : ℂ) : ℝ :=
  (subdivision D).node (upperCell D q+1)
def lowerEnd (D : CoefficientData n) (q : ℂ) : ℝ :=
  (subdivision D).node (lowerCell D q)
def upperDensity (D : CoefficientData n) (q : ℂ) (k : Fin n) : ℝ → ℂ :=
  cellWeight D q k (upperCell D q)
def lowerDensity (D : CoefficientData n) (q : ℂ) (k : Fin n) : ℝ → ℂ :=
  cellWeight D q k (lowerCell D q)

theorem upperCell_mem (D : CoefficientData n) {q : ℂ} (hq : q ∈ activeLines D) :
    upperCell D q ∈ survivingCells D q := by
  have hne := ((mem_activeLines D q).mp hq).2
  simp only [upperCell,dif_pos hne]
  exact Finset.max'_mem _ _

theorem lowerCell_mem (D : CoefficientData n) {q : ℂ} (hq : q ∈ activeLines D) :
    lowerCell D q ∈ survivingCells D q := by
  have hne := ((mem_activeLines D q).mp hq).2
  simp only [lowerCell,dif_pos hne]
  exact Finset.min'_mem _ _

theorem cell_le_upperCell (D : CoefficientData n) {q : ℂ} (hq : q ∈ activeLines D)
    {i : ℕ} (hi : i ∈ survivingCells D q) : i ≤ upperCell D q := by
  have hne := ((mem_activeLines D q).mp hq).2
  simp only [upperCell,dif_pos hne]
  exact Finset.le_max' _ _ hi

theorem lowerCell_le_cell (D : CoefficientData n) {q : ℂ} (hq : q ∈ activeLines D)
    {i : ℕ} (hi : i ∈ survivingCells D q) : lowerCell D q ≤ i := by
  have hne := ((mem_activeLines D q).mp hq).2
  simp only [lowerCell,dif_pos hne]
  exact Finset.min'_le _ _ hi

theorem upper_cell_interval_positive (D : CoefficientData n) {q : ℂ}
    (hq : q ∈ activeLines D) :
    (subdivision D).node (upperCell D q) < upperEnd D q := by
  have hm := (mem_cells_iff (subdivision D) (cellWeight D q) _).mp (upperCell_mem D hq)
  exact (subdivision D).increasing _ _ (Nat.lt_succ_self _) (Nat.succ_le_of_lt hm.1)

theorem lower_cell_interval_positive (D : CoefficientData n) {q : ℂ}
    (hq : q ∈ activeLines D) :
    lowerEnd D q < (subdivision D).node (lowerCell D q+1) := by
  have hm := (mem_cells_iff (subdivision D) (cellWeight D q) _).mp (lowerCell_mem D hq)
  exact (subdivision D).increasing _ _ (Nat.lt_succ_self _) (Nat.succ_le_of_lt hm.1)

/-- A true nonzero analytic endpoint density exists on the interior, which
is the source witness consumed by the Watson endpoint series theorem. -/
theorem upperDensity_nonzero (D : CoefficientData n) {q : ℂ} (hq : q ∈ activeLines D) :
    ∃ k : Fin n, ∃ t ∈ Ioo ((subdivision D).node (upperCell D q)) (upperEnd D q),
      upperDensity D q k t ≠ 0 := by
  obtain ⟨_,k,t,ht,hne⟩ :=
    (mem_cells_iff (subdivision D) (cellWeight D q) _).mp (upperCell_mem D hq)
  obtain ⟨u,hu,hvu⟩ := exists_nonzero_interior (upper_cell_interval_positive D hq)
    (cellWeight_analytic D q k _).continuousOn ⟨t,ht,hne⟩
  exact ⟨k,u,hu,hvu⟩

theorem lowerDensity_nonzero (D : CoefficientData n) {q : ℂ} (hq : q ∈ activeLines D) :
    ∃ k : Fin n, ∃ t ∈ Ioo (lowerEnd D q) ((subdivision D).node (lowerCell D q+1)),
      lowerDensity D q k t ≠ 0 := by
  obtain ⟨_,k,t,ht,hne⟩ :=
    (mem_cells_iff (subdivision D) (cellWeight D q) _).mp (lowerCell_mem D hq)
  obtain ⟨u,hu,hvu⟩ := exists_nonzero_interior (lower_cell_interval_positive D hq)
    (cellWeight_analytic D q k _).continuousOn ⟨t,ht,hne⟩
  exact ⟨k,u,hu,hvu⟩

/-- All other upper endpoints are strictly smaller than the selected one. -/
theorem other_upperEnd_lt (D : CoefficientData n) {q : ℂ} (hq : q ∈ activeLines D)
    {i : ℕ} (hi : i ∈ survivingCells D q) (hne : i ≠ upperCell D q) :
    (subdivision D).node (i+1)<upperEnd D q := by
  have hm := (mem_cells_iff (subdivision D) (cellWeight D q) _).mp (upperCell_mem D hq)
  exact (subdivision D).increasing _ _
    (Nat.succ_lt_succ (lt_of_le_of_ne (cell_le_upperCell D hq hi) hne))
    (Nat.succ_le_of_lt hm.1)

/-- The analogous strict gap for lower endpoints in the other half-plane. -/
theorem lowerEnd_lt_other (D : CoefficientData n) {q : ℂ} (hq : q ∈ activeLines D)
    {i : ℕ} (hi : i ∈ survivingCells D q) (hne : i ≠ lowerCell D q) :
    lowerEnd D q<(subdivision D).node i := by
  have hiCount := ((mem_cells_iff (subdivision D) (cellWeight D q) i).mp hi).1
  exact (subdivision D).increasing _ _
    (lt_of_le_of_ne (lowerCell_le_cell D hq hi) (Ne.symm hne)) hiCount.le

#print axioms coefficient_eq_active_packets
#print axioms upperDensity_nonzero
#print axioms lowerDensity_nonzero
#print axioms other_upperEnd_lt
#print axioms lowerEnd_lt_other
end CRGLinearKernelLineEndpoints
