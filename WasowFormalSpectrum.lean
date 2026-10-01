import WasowLeadingBlocks

/-! Exhaustive spectral alternatives for the actual complex leading matrix. -/
set_option autoImplicit false
noncomputable section
namespace WasowFormalSpectrum
open Module WasowLeadingBlocks

/-- Over the complex numbers, absence of a second distinct eigenvalue means
that subtracting one scalar leaves a genuinely nilpotent matrix. Empty matrices
are included without a nonzero-dimension premise. -/
theorem single_eigen_or_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ) :
    (∃ α : ℂ, IsNilpotent (C - α • 1)) ∨
      ∃ a b : Eigenvalues (Matrix.toLin' C), a ≠ b := by
  classical
  by_cases hι : IsEmpty ι
  · let := hι
    exact Or.inl ⟨0, 1, Subsingleton.elim _ _⟩
  let : Nonempty ι := not_isEmpty_iff.mp hι
  let f : Module.End ℂ (ι → ℂ) := Matrix.toLin' C
  by_cases hs : ∃ a b : Eigenvalues f, a ≠ b
  · exact Or.inr hs
  obtain ⟨α, hα⟩ := f.exists_eigenvalue
  have hu (μ : ℂ) (hμ : f.HasEigenvalue μ) : μ = α := by
    have he : (⟨μ,hμ⟩ : Eigenvalues f) = ⟨α,hα⟩ := by
      by_contra hn
      exact hs ⟨⟨μ,hμ⟩, ⟨α,hα⟩, hn⟩
    exact congrArg Subtype.val he
  have htop : f.maxGenEigenspace α = ⊤ := by
    apply top_unique
    rw [← f.iSup_maxGenEigenspace_eq_top]
    apply iSup_le
    intro μ
    by_cases hμ : f.HasEigenvalue μ
    · rw [hu μ hμ]
    · have hb : f.maxGenEigenspace μ = ⊥ := by
        by_contra hn
        exact hμ (Module.End.HasUnifEigenvalue.lt zero_lt_one hn)
      rw [hb]
      exact bot_le
  have hn : IsNilpotent (f - α • 1) := by
    refine ⟨Module.finrank ℂ (ι → ℂ), ?_⟩
    rw [f.maxGenEigenspace_eq_genEigenspace_finrank α, Module.End.genEigenspace_nat] at htop
    exact LinearMap.ker_eq_top.mp htop
  left
  refine ⟨α, ?_⟩
  have hh := hn.map (Matrix.toLinAlgEquiv (Pi.basisFun ℂ ι)).symm
  simp only [map_sub, map_smul, map_one] at hh
  change IsNilpotent (LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι)
    (Matrix.toLin' C) - α • 1) at hh
  rwa [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at hh

#print axioms single_eigen_or_split
end WasowFormalSpectrum
