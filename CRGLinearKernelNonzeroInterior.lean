import CRGLinearKernelActiveCells

set_option autoImplicit false
noncomputable section
open Set
namespace CRGLinearKernelNonzeroInterior

/-- A continuous density on a nondegenerate interval cannot be supported
only at its endpoints. This also applies to each analytic cell density. -/
theorem exists_nonzero_interior {v : ℝ → ℂ} {a b : ℝ}
    (hab : a < b) (hv : ContinuousOn v (Icc a b))
    (hne : ∃ t ∈ Icc a b,v t≠0) : ∃ t ∈ Ioo a b,v t≠0 := by
  by_contra h
  push Not at h
  have hz : EqOn v 0 (Ioo a b) := fun t ht=>h t ht
  have hz' : EqOn v 0 (Icc a b) := hz.of_subset_closure hv continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])
  obtain ⟨t,ht,hne⟩ := hne
  exact hne (hz' ht)

#print axioms exists_nonzero_interior
end CRGLinearKernelNonzeroInterior
