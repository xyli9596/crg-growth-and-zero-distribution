import CRGLinearKernelLines
import CRGLinearKernelActiveCells

/-! Supporting-line packets constructed from the exact coefficient data of
Corollary 5.2. Every zero cell is discarded by an integral identity. Every
surviving line has genuine nonzero extreme endpoint jets. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval BigOperators
namespace CRGLinearKernelLinePackets
open CRGLinearKernel CRGLinearKernelIntegration CRGLinearKernelEntire
open CRGLinearKernelLines CRGLinearKernelSubdivision CRGLinearKernelActiveCells
variable {n : ℕ}

def lowerEndpoint (D : CoefficientData n) (ell : Fin D.count) : ℝ :=
  lower (D.lower ell) (D.upper ell) (scale (D.slope ell))
def upperEndpoint (D : CoefficientData n) (ell : Fin D.count) : ℝ :=
  upper (D.lower ell) (D.upper ell) (scale (D.slope ell))
def normalizedWeight (D : CoefficientData n) (k : Fin n) (ell : Fin D.count) : ℝ → ℂ :=
  density (fun t=>D.weight k ell (t:ℂ)) (scale (D.slope ell))

theorem normalized_interval_positive (D : CoefficientData n) (ell : Fin D.count) :
    lowerEndpoint D ell < upperEndpoint D ell :=
  lower_lt_upper (D.interval_positive ell) (scale_ne_zero (D.slope_nonzero ell))

theorem real_weight_analytic (D : CoefficientData n) (k : Fin n) (ell : Fin D.count) :
    AnalyticOnNhd ℝ (fun t : ℝ=>D.weight k ell (t:ℂ)) (Icc (D.lower ell) (D.upper ell)) := by
  intro t ht
  exact (((D.weight_holomorphic k ell) (t:ℂ) ⟨t,ht,rfl⟩).restrictScalars (𝕜 := ℝ)).comp
    (Complex.ofRealCLM.analyticAt t)

theorem normalizedWeight_analytic (D : CoefficientData n) (k : Fin n) (ell : Fin D.count) :
    AnalyticOnNhd ℝ (normalizedWeight D k ell)
      (Icc (lowerEndpoint D ell) (upperEndpoint D ell)) :=
  density_analytic (D.interval_positive ell).le (scale_ne_zero (D.slope_nonzero ell))
    (real_weight_analytic D k ell)

/-- Chosen from the actual finite set of normalized real endpoints, before
any direction, solution, or coefficient asymptotic truncation is selected. -/
def subdivision (D : CoefficientData n) : Subdivision (lowerEndpoint D) (upperEndpoint D) :=
  Classical.choice (exists_subdivision (lowerEndpoint D) (upperEndpoint D)
    (normalized_interval_positive D))

def lines (D : CoefficientData n) : Finset ℂ := by
  classical
  exact Finset.univ.image fun ell : Fin D.count=>line (D.slope ell)

def weightsOnLine (D : CoefficientData n) (q : ℂ) (k : Fin n) (ell : Fin D.count)
    (t : ℝ) : ℂ := if line (D.slope ell)=q then normalizedWeight D k ell t else 0

theorem weightsOnLine_analytic (D : CoefficientData n) (q : ℂ) (k : Fin n)
    (ell : Fin D.count) : AnalyticOnNhd ℝ (weightsOnLine D q k ell)
      (Icc (lowerEndpoint D ell) (upperEndpoint D ell)) := by
  by_cases hq : line (D.slope ell)=q
  · have he : weightsOnLine D q k ell=normalizedWeight D k ell := by
      funext t
      simp only [weightsOnLine,if_pos hq]
    rw [he]
    exact normalizedWeight_analytic D k ell
  · have he : weightsOnLine D q k ell=(fun _=>0) := by
      funext t
      simp only [weightsOnLine,if_neg hq]
    rw [he]
    exact analyticOnNhd_const

def cellWeight (D : CoefficientData n) (q : ℂ) : Fin n → ℕ → ℝ → ℂ :=
  (subdivision D).cellWeight (weightsOnLine D q)

def survivingCells (D : CoefficientData n) (q : ℂ) : Finset ℕ :=
  cells (subdivision D) (cellWeight D q)

/-- The actual packet is the integral sum after exact deletion of zero cells. -/
def packet (D : CoefficientData n) (q : ℂ) (k : Fin n) (z : ℂ) : ℂ :=
  ∑ i ∈ survivingCells D q,
    kernel (cellWeight D q k i) ((subdivision D).node i) ((subdivision D).node (i+1)) (q*z)

theorem cellWeight_analytic (D : CoefficientData n) (q : ℂ) (k : Fin n) (i : ℕ) :
    AnalyticOnNhd ℝ (cellWeight D q k i)
      (Icc ((subdivision D).node i) ((subdivision D).node (i+1))) :=
  (subdivision D).cellWeight_analytic (weightsOnLine D q) (weightsOnLine_analytic D q) k i

theorem packet_eq_interval_sum (D : CoefficientData n) (q : ℂ) (k : Fin n) (z : ℂ) :
    packet D q k z = ∑ ell : Fin D.count,
      if line (D.slope ell)=q then
        kernel (normalizedWeight D k ell) (lowerEndpoint D ell) (upperEndpoint D ell) (q*z)
      else 0 := by
  have hs := (subdivision D).sum_kernels_eq_cellWeights
    (weightsOnLine D q) (weightsOnLine_analytic D q) k (q*z)
  rw [sum_kernels_eq_surviving_cells] at hs
  change _=packet D q k z at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro ell _
  by_cases hq : line (D.slope ell)=q
  · have he : weightsOnLine D q k ell=normalizedWeight D k ell := by
      funext t
      simp only [weightsOnLine,if_pos hq]
    rw [he,if_pos hq]
  · have he : weightsOnLine D q k ell=(fun _=>0) := by
      funext t
      simp only [weightsOnLine,if_neg hq]
    rw [he,if_neg hq]
    simp only [kernel,zero_mul,intervalIntegral.integral_zero]

/-- Exact supporting-line grouping of all original oriented integrals. -/
theorem integral_sum_eq_packets (D : CoefficientData n) (k : Fin n) (z : ℂ) :
    (∑ ell : Fin D.count,linearKernel (fun t=>D.weight k ell (t:ℂ))
      (D.lower ell) (D.upper ell) (D.slope ell) z) =
    ∑ q ∈ lines D,packet D q k z := by
  classical
  simp_rw [packet_eq_interval_sum]
  have hf := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin D.count)))
    (t := lines D) (g := fun ell=>line (D.slope ell))
    (fun ell _=>by simp [lines])
    (fun ell=>kernel (normalizedWeight D k ell) (lowerEndpoint D ell)
      (upperEndpoint D ell) (line (D.slope ell)*z))
  calc
    (∑ ell : Fin D.count,linearKernel (fun t=>D.weight k ell (t:ℂ))
      (D.lower ell) (D.upper ell) (D.slope ell) z) =
      ∑ ell : Fin D.count,kernel (normalizedWeight D k ell) (lowerEndpoint D ell)
        (upperEndpoint D ell) (line (D.slope ell)*z) := by
          apply Finset.sum_congr rfl
          intro ell _
          exact linearKernel_on_line _ (D.interval_positive ell).le (D.slope_nonzero ell) z
    _ = _ := hf.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ell _
      by_cases he : line (D.slope ell)=q
      · simp only [if_pos he,he]
      · simp only [if_neg he]

/-- A discarded whole supporting line contributes exactly zero. -/
theorem packet_zero_of_no_cells (D : CoefficientData n) (q : ℂ)
    (hempty : survivingCells D q=∅) (k : Fin n) (z : ℂ) : packet D q k z=0 := by
  simp only [packet,hempty,Finset.sum_empty]

/-- The positive half-plane chooses the rightmost surviving cell, with a
nonzero actual endpoint derivative in some coefficient component. -/
theorem packet_upper_endpoint (D : CoefficientData n) (q : ℂ)
    (hne : (survivingCells D q).Nonempty) :
    ∃ m ∈ survivingCells D q, (∀ i ∈ survivingCells D q, i ≤ m) ∧
      ∃ k : Fin n, ∃ j : ℕ,
        iteratedDeriv j (cellWeight D q k m) ((subdivision D).node (m+1)) ≠ 0 :=
  extreme_upper_cell (subdivision D) (cellWeight D q)
    (fun k i _=>cellWeight_analytic D q k i) hne

/-- The negative half-plane chooses the corresponding leftmost endpoint. -/
theorem packet_lower_endpoint (D : CoefficientData n) (q : ℂ)
    (hne : (survivingCells D q).Nonempty) :
    ∃ m ∈ survivingCells D q, (∀ i ∈ survivingCells D q, m ≤ i) ∧
      ∃ k : Fin n, ∃ j : ℕ,
        iteratedDeriv j (cellWeight D q k m) ((subdivision D).node m) ≠ 0 :=
  extreme_lower_cell (subdivision D) (cellWeight D q)
    (fun k i _=>cellWeight_analytic D q k i) hne

#print axioms normalizedWeight_analytic
#print axioms packet_eq_interval_sum
#print axioms integral_sum_eq_packets
#print axioms packet_upper_endpoint
#print axioms packet_lower_endpoint
end CRGLinearKernelLinePackets
