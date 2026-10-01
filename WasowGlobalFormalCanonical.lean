import WasowGlobalFormalRegular
import WasowLaurentPhase

/-! A single coefficient matrix with fixed polynomial phases and complete
regular-singular blocks. Different phase fibers have no regular coupling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace WasowGlobalFormalCanonical
open WasowLaurentGauge WasowLaurentRamification WasowLaurentPhase
open WasowFormalNormalization WasowGlobalFormalRegular
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure NormalData (ι : Type*) [Fintype ι] [DecidableEq ι] where
  phase : ι → Polynomial ℂ
  phase_zero : ∀i, (phase i).coeff 0=0
  regular : Series ι
  separated : ∀n i j, phase i ≠ phase j → PowerSeries.coeff n regular i j=0

def coefficient (N : NormalData ι) : Matrix ι ι L :=
  Matrix.diagonal (fun i => D (phaseLaurent (N.phase i))) + regularCoefficient N.regular

/-- A full regular-singular coefficient has zero exponential phase. -/
def regularData (R : Series ι) : NormalData ι where
  phase := fun _ => 0
  phase_zero := by simp
  regular := R
  separated := by intros; contradiction

@[simp] theorem coefficient_regularData (R : Series ι) :
    coefficient (regularData R) = regularCoefficient R := by
  simp [coefficient, regularData]

/-- A scalar extracted before recursion is added to every phase in its block. -/
def addPhase (N : NormalData ι) (Q : Polynomial ℂ) (hQ : Q.coeff 0=0) : NormalData ι where
  phase := fun i => N.phase i+Q
  phase_zero := by intro i; simp [N.phase_zero, hQ]
  regular := N.regular
  separated := by
    intro n i j hne
    apply N.separated n i j
    intro he
    exact hne (congrArg (fun F => F+Q) he)

theorem coefficient_addPhase (N : NormalData ι) (Q : Polynomial ℂ) (hQ : Q.coeff 0=0) :
    coefficient (addPhase N Q hQ) = coefficient N + D (phaseLaurent Q) • 1 := by
  apply Matrix.ext
  intro i j
  by_cases hij : i=j
  · subst j
    simp [coefficient, addPhase, Matrix.add_apply, Matrix.smul_apply, add_comm, add_left_comm]
  · simp [coefficient, addPhase, Matrix.add_apply, Matrix.smul_apply, hij]

/-- Additional ramification acts on the phase and the entire regular series. -/
def ramifiedData (N : NormalData ι) (p : ℕ) (hp : 0<p) : NormalData ι where
  phase := fun i => (N.phase i).comp (Polynomial.X^p)
  phase_zero := by
    intro i
    change (WasowPhaseFamily.refinePhase p (N.phase i)).coeff 0=0
    rw [WasowPhaseFamily.refinePhase_coeff_zero p hp, N.phase_zero]
  regular := (p:ℂ) • expandSeries p N.regular
  separated := by
    intro n i j hne
    have hij : N.phase i ≠ N.phase j := by
      intro he
      exact hne (congrArg (fun F : Polynomial ℂ => F.comp (Polynomial.X^p)) he)
    simp only [PowerSeries.coeff_smul, expandSeries, PowerSeries.coeff_mk, Matrix.smul_apply]
    split_ifs
    · simp [N.separated _ i j hij]
    · simp

theorem coefficient_ramifiedData (N : NormalData ι) (p : ℕ) (hp : 0<p) :
    coefficient (ramifiedData N p hp) = pullback p hp (coefficient N) := by
  have hreg := pullback_regularCoefficient p hp N.regular
  apply Matrix.ext
  intro i j
  have hregij := congrArg (fun M : Matrix ι ι L => M i j) hreg
  by_cases hij : i=j
  · subst j
    simp only [coefficient, ramifiedData, Matrix.add_apply, Matrix.diagonal_apply_eq,
      pullback, map_add, mul_add]
    rw [derivative_phase_ramify, ← hregij]
    rfl
  · simp only [coefficient, ramifiedData, Matrix.add_apply, Matrix.diagonal_apply_ne _ hij,
      zero_add, pullback]
    exact hregij.symm

section Blocks
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {I : σ → Type*} [∀a, Fintype (I a)] [∀a, DecidableEq (I a)]

def blockData (N : ∀a, NormalData (I a)) : NormalData (Σa,I a) where
  phase := fun x => (N x.1).phase x.2
  phase_zero := fun x => (N x.1).phase_zero x.2
  regular := blockSeries (fun a => (N a).regular)
  separated := by
    rintro n ⟨a,i⟩ ⟨b,j⟩ hne
    by_cases hab : a=b
    · subst b
      simp only [blockSeries, PowerSeries.coeff_mk, Matrix.blockDiagonal'_apply_eq]
      exact (N a).separated n i j hne
    · simp [blockSeries, Matrix.blockDiagonal'_apply_ne _ _ _ hab]

theorem coefficient_blockData (N : ∀a, NormalData (I a)) :
    coefficient (blockData N) = Matrix.blockDiagonal' (fun a => coefficient (N a)) := by
  apply Matrix.ext
  rintro ⟨a,i⟩ ⟨b,j⟩
  by_cases hab : a=b
  · subst b
    simp [coefficient, blockData, regularCoefficient_blocks, Matrix.diagonal_apply,
      Matrix.add_apply]
  · simp [coefficient, blockData, regularCoefficient_blocks,
      Matrix.blockDiagonal'_apply_ne _ _ _ hab,
      show (⟨a,i⟩ : Sigma I) ≠ ⟨b,j⟩ from fun hh => hab (congrArg Sigma.fst hh)]

end Blocks

#print axioms coefficient_regularData
#print axioms addPhase
#print axioms coefficient_addPhase
#print axioms ramifiedData
#print axioms coefficient_ramifiedData
#print axioms blockData
#print axioms coefficient_blockData
end WasowGlobalFormalCanonical
