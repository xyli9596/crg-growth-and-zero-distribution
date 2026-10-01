import WasowGlobalFormalCanonical

/-! Actual Laurent gauges assembled with a single common ramification.
All normalization matrices and their inverses are constructed by products. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace WasowGlobalFormalAssembly
open WasowLaurentGauge WasowGlobalFormalEdges WasowGlobalFormalSplit
open WasowGlobalFormalRegular WasowGlobalFormalCanonical
open WasowLaurentRamification WasowLaurentPhase
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A genuine single Laurent gauge to fixed polynomial phases and complete
regular blocks, including both inverse identities. -/
structure Realization (A : Matrix ι ι L) where
  index : Type
  [finiteIndex : Fintype index]
  [decidableIndex : DecidableEq index]
  denominator : ℕ
  positive : 0 < denominator
  normal : NormalData index
  change : Change (pullback denominator positive A) (coefficient normal)
attribute [instance] Realization.finiteIndex Realization.decidableIndex

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem pullback_one (A : Matrix ι κ L) : pullback 1 (by omega) A=A := by
  apply Matrix.ext
  intro i j
  simp [pullback, jacobian]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem pullback_congr (p q : ℕ) (hp : 0<p) (hq : 0<q) (h : p=q)
    (A : Matrix ι κ L) : pullback p hp A = pullback q hq A := by
  subst q
  rfl

/-- The identity gauge starts a regular-singular leaf. -/
def regularRealization (R : WasowFormalNormalization.Series ι) : Realization (regularCoefficient R) where
  index := ι
  denominator := 1
  positive := by omega
  normal := regularData R
  change := by
    rw [pullback_one, coefficient_regularData]
    refine ⟨1,1,by simp,by simp,?_⟩
    have hd := derivative_constant (1 : Matrix ι ι ℂ)
    rw [constant_one] at hd
    simpa only [GaugeEquation, Matrix.one_mul, Matrix.mul_one, sub_self] using hd.symm

/-- Compose a concrete preliminary edge with a previously assembled tail. -/
def precompose {A : Matrix ι ι L} {B : Matrix κ κ L}
    (f : Change A B) (R : Realization B) : Realization A where
  index := R.index
  denominator := R.denominator
  positive := R.positive
  normal := R.normal
  change := (ramifyChange f R.denominator R.positive).comp R.change

/-- A previously ramified edge is absorbed into the single common denominator. -/
def precomposeRamified {A : Matrix ι ι L} {B : Matrix κ κ L}
    (p : ℕ) (hp : 0<p) (f : Change (pullback p hp A) B) (R : Realization B) :
    Realization A where
  index := R.index
  denominator := R.denominator*p
  positive := Nat.mul_pos R.positive hp
  normal := R.normal
  change := by
    have h := (ramifyChange f R.denominator R.positive).comp R.change
    rw [pullback_comp] at h
    exact h

omit [Fintype ι] in
theorem pullback_addScalar (p : ℕ) (hp : 0<p) (A : Matrix ι ι L) (c : L) :
    pullback p hp (A+c•1) = pullback p hp A + (jacobian p*ramify p hp c)•1 := by
  apply Matrix.ext
  intro i j
  by_cases hij : i=j
  · subst j
    simp [pullback, Matrix.add_apply, Matrix.smul_apply, mul_add]
  · simp [pullback, Matrix.add_apply, Matrix.smul_apply, hij]

/-- Restore a fixed polynomial scalar phase before any direction is chosen. -/
def addScalar {A : Matrix ι ι L} (R : Realization A)
    (Q : Polynomial ℂ) (hQ : Q.coeff 0=0) :
    Realization (A+D (phaseLaurent Q)•1) where
  index := R.index
  denominator := R.denominator
  positive := R.positive
  normal := addPhase R.normal (Q.comp (Polynomial.X^R.denominator)) (by
    change (WasowPhaseFamily.refinePhase R.denominator Q).coeff 0=0
    rw [WasowPhaseFamily.refinePhase_coeff_zero _ R.positive, hQ])
  change := by
    rw [coefficient_addPhase, pullback_addScalar, ← derivative_phase_ramify]
    exact R.change.addScalar _

theorem pullback_blocks {σ : Type} [Fintype σ] [DecidableEq σ]
    {I : σ → Type} [∀a, Fintype (I a)] [∀a, DecidableEq (I a)]
    (p : ℕ) (hp : 0<p) (A : ∀a, Matrix (I a) (I a) L) :
    pullback p hp (Matrix.blockDiagonal' A) = Matrix.blockDiagonal' (fun a => pullback p hp (A a)) := by
  apply Matrix.ext
  rintro ⟨a,i⟩ ⟨b,j⟩
  by_cases hab : a=b
  · subst b
    simp [pullback]
  · simp [pullback, Matrix.blockDiagonal'_apply_ne _ _ _ hab]

/-- A finite product denominator synchronizes both actual gauges and complete
coefficient matrices of all branches. -/
def blocks {σ : Type} [Fintype σ] [DecidableEq σ]
    {I : σ → Type} [∀a, Fintype (I a)] [∀a, DecidableEq (I a)]
    (A : ∀a, Matrix (I a) (I a) L) (R : ∀a, Realization (A a)) :
    Realization (Matrix.blockDiagonal' A) := by
  let p : σ → ℕ := fun a => (R a).denominator
  let P := WasowPhaseFamily.commonDenominator p
  have hp (a : σ) : 0<p a := (R a).positive
  have hP : 0<P := WasowPhaseFamily.commonDenominator_pos p hp
  let k : σ → ℕ := fun a => P/p a
  have hk (a : σ) : 0<k a := WasowPhaseFamily.common_refinement_pos p hp a
  let N : ∀a, NormalData (R a).index := fun a => ramifiedData (R a).normal (k a) (hk a)
  have H (a : σ) : Change (pullback P hP (A a)) (coefficient (N a)) := by
    have hh := ramifyChange (R a).change (k a) (hk a)
    rw [pullback_comp] at hh
    have he : k a*(R a).denominator=P := by
      rw [Nat.mul_comm]
      exact WasowPhaseFamily.common_refinement_mul p a
    rw [coefficient_ramifiedData]
    rw [pullback_congr _ P _ hP he] at hh
    exact hh
  refine ⟨(Σa,(R a).index), P, hP, blockData N, ?_⟩
  rw [pullback_blocks, coefficient_blockData]
  exact blockChange _ _ H

#print axioms pullback_congr
#print axioms pullback_one
#print axioms regularRealization
#print axioms precompose
#print axioms precomposeRamified
#print axioms pullback_addScalar
#print axioms addScalar
#print axioms pullback_blocks
#print axioms blocks
end WasowGlobalFormalAssembly
