import WasowGlobalFormalAssembly

/-! A real full reduction tree produces ONE actual Laurent gauge and its true
inverse after ONE fixed ramification. Its target has fixed polynomial phases
and complete regular-singular blocks. No global gauge is supplied as input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace WasowGlobalFormalTree
open WasowLaurentGauge WasowLaurentRamification WasowLaurentShearing
open WasowGlobalFormalEdges WasowGlobalFormalSplit WasowGlobalFormalRegular
open WasowGlobalFormalCanonical WasowGlobalFormalAssembly WasowLaurentPhase
open WasowFormalSuccessor WasowFormalNormalization WasowFormalSplit WasowRecursiveTree
open WasowScalarPhase
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Actual scalar add-back on a child after its complete subtree is assembled. -/
def restoreScalar {A : Matrix ι ι L} (R : Realization A) (q : ℕ) (α : ℂ) :
    Realization (A+scalarCoefficient q α•1) := by
  have hh := WasowGlobalFormalAssembly.addScalar R (rankPhase q α) (rankPhase_coeff_zero q α)
  rw [WasowLaurentPhase.derivative_rankPhase] at hh
  exact hh

/-- A real spectral family and all actual child gauges combine to one gauge. -/
def familyRealization {A : Series ι} {q : ℕ} (F : Family A q)
    (children : ∀a, Realization (differentialCoefficient (F.child a).shape.rank (F.child a).series)) :
    Realization (differentialCoefficient q A) := by
  have RC (a : Spectrum A) : Realization
      (differentialCoefficient q (F.child a).series + scalarCoefficient q a.val•1) := by
    have hc := children a
    rw [(F.normalization a).rank_eq] at hc
    exact restoreScalar hc q a.val
  exact precompose (familyChange F) (blocks _ RC)

/-- Recursion follows the genuine terminating full-series tree. Each branch
uses its recorded actual shearing and normalization matrices. -/
def treeRealization {old : FormalState} (t : Tree old) :
    Realization (differentialCoefficient old.shape.rank old.series) := by
  induction t with
  | regular old d stopping =>
      have hs := shearChange d
      rw [shearingRank_stopping d stopping] at hs
      have hr := regularRealization (-(rawSeries old d.slope))
      rw [regularCoefficient_neg] at hr
      exact precomposeRamified d.slope.den d.slope.den_pos hs hr
  | single old next i data child ih =>
      exact precomposeRamified i.slope.den i.slope.den_pos (singleChange data)
        (restoreScalar ih next.shape.rank i.eigenvalue)
  | split old d continuing rank rank_update family a b distinct children ih =>
      have hs := shearChange d
      rw [shearingRank_eq d rank rank_update, differentialCoefficientZ_nat] at hs
      exact precomposeRamified d.slope.den d.slope.den_pos hs
        (familyRealization family ih)

/-- Arbitrary initial spectral coordinates, all scalar extractions, all
ramifications and every leaf are now multiplied into a single real gauge. -/
def reductionRealization {A : Series ι} {q : ℕ} (R : Reduction A q) :
    Realization (differentialCoefficient q A) :=
  familyRealization R.initial (fun a => treeRealization (R.trees a))

/-- Existence follows from the proved finite reduction algorithm, with no
assumed normal form or formal gauge in the hypotheses. -/
theorem exists_global_realization (A : Series ι) (q : ℕ) :
    Nonempty (Realization (differentialCoefficient q A)) := by
  obtain ⟨R⟩ := exists_reduction A q
  exact ⟨reductionRealization R⟩

#print axioms restoreScalar
#print axioms familyRealization
#print axioms treeRealization
#print axioms reductionRealization
#print axioms exists_global_realization
end WasowGlobalFormalTree
