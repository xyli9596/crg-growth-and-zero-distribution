import WasowLaurentGauge
import WasowRecursiveTree

/-! Actual Laurent matrix gauges for the coordinate, normalization, scalar and
finite-block edges of the complete formal reduction. Every constructed change
contains concrete Laurent matrices with both inverse equations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace WasowGlobalFormalEdges
open WasowLaurentGauge WasowFormalSuccessor WasowFormalNormalization
variable {ι κ ν : Type*}

/-- Constant coordinate matrices as genuine Laurent matrices, also rectangular. -/
def constant (P : Matrix ι κ ℂ) : Matrix ι κ L := P.map HahnSeries.C

theorem constant_mul [Fintype κ] (P : Matrix ι κ ℂ) (Q : Matrix κ ν ℂ) :
    constant (P*Q) = constant P * constant Q := by
  ext i j
  simp [constant, Matrix.mul_apply, map_sum, map_mul]

theorem constant_one [DecidableEq ι] : constant (1 : Matrix ι ι ℂ) = 1 := by
  ext i j
  simp [constant, Matrix.one_apply]

theorem derivative_constant (P : Matrix ι κ ℂ) : matrixDerivative (constant P) = 0 := by
  apply Matrix.ext
  intro i j
  change D (HahnSeries.C (P i j)) = 0
  simp [D, HahnSeries.C_apply, LaurentSeries.derivative]

/-- A concrete invertible differential change. Constructors below supply its
actual matrices, rather than assuming existence of a final global gauge. -/
structure Change [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι L) (B : Matrix κ κ L) where
  G : Matrix ι κ L
  H : Matrix κ ι L
  GH : G*H=1
  HG : H*G=1
  equation : GaugeEquation A G B

variable [Fintype ι] [Fintype κ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

/-- Actual multiplication of Laurent gauges, with the inverse order reversed. -/
def Change.comp {A : Matrix ι ι L} {B : Matrix κ κ L} {C : Matrix ν ν L}
    (f : Change A B) (g : Change B C) : Change A C where
  G := f.G*g.G
  H := g.H*f.H
  GH := by simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc g.G, g.GH, Matrix.one_mul, f.GH]
  HG := by simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc f.H, f.HG, Matrix.one_mul, g.HG]
  equation := gaugeEquation_comp A f.G B g.G C f.equation g.equation

/-- A scalar coefficient is restored to both systems through the same true gauge. -/
def Change.addScalar {A : Matrix ι ι L} {B : Matrix κ κ L}
    (f : Change A B) (c : L) : Change (A+c•1) (B+c•1) where
  G := f.G
  H := f.H
  GH := f.GH
  HG := f.HG
  equation := by
    unfold GaugeEquation at *
    rw [Matrix.add_mul, Matrix.mul_add]
    have hl : (c • (1 : Matrix ι ι L)) * f.G = c • f.G := by
      apply Matrix.ext
      intro i j
      simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, mul_ite, ite_mul]
    have hr : f.G * (c • (1 : Matrix κ κ L)) = c • f.G := by
      apply Matrix.ext
      intro i j
      simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, mul_ite, ite_mul, mul_comm]
    rw [hl, hr]
    have hh := f.equation
    unfold GaugeEquation at hh
    rw [show A*f.G+c•f.G-(f.G*B+c•f.G)=A*f.G-f.G*B by abel, hh]

/-- Constants with actual rectangular inverses supply a differential change. -/
def constantChange (A : Matrix ι ι L) (P : Matrix ι κ ℂ) (Q : Matrix κ ι ℂ)
    (hPQ : P*Q=1) (hQP : Q*P=1) : Change A (constant Q*A*constant P) where
  G := constant P
  H := constant Q
  GH := by rw [← constant_mul, hPQ, constant_one]
  HG := by rw [← constant_mul, hQP, constant_one]
  equation := by
    unfold GaugeEquation
    rw [derivative_constant]
    have hh : constant P*constant Q = 1 := by rw [← constant_mul, hPQ, constant_one]
    rw [← Matrix.mul_assoc (constant P), ← Matrix.mul_assoc (constant P), hh,
      Matrix.one_mul, sub_self]

/-- Constant-coordinate transport of the complete matrix series commutes with
its actual embedding into Laurent matrices. -/
theorem toLaurent_coordinate (A : Series ι) (P : Matrix ι κ ℂ) (Q : Matrix κ ι ℂ)
    (hPQ : P*Q=1) (hQP : Q*P=1) :
    toLaurent (PowerSeries.map (coordinateEquiv P Q hPQ hQP).toRingHom A) =
      constant Q * toLaurent A * constant P := by
  ext i j n
  simp only [toLaurent_apply, PowerSeries.coeff_coe, WasowPowerSeries.coeff_entry,
    PowerSeries.coeff_map]
  simp only [constant, Matrix.mul_apply, Matrix.map_apply, HahnSeries.coeff_sum,
    HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero, HahnSeries.coeff_single_zero_mul]
  by_cases hn : n < 0
  · simp [PowerSeries.coeff_coe, hn]
  · simp only [toLaurent_apply, PowerSeries.coeff_coe, if_neg hn, WasowPowerSeries.coeff_entry]
    rfl

/-- The book rank coefficient transforms by the same actual constant basis. -/
theorem differentialCoefficient_coordinate (q : ℕ) (A : Series ι)
    (P : Matrix ι κ ℂ) (Q : Matrix κ ι ℂ) (hPQ : P*Q=1) (hQP : Q*P=1) :
    differentialCoefficient q (PowerSeries.map (coordinateEquiv P Q hPQ hQP).toRingHom A) =
      constant Q * differentialCoefficient q A * constant P := by
  rw [differentialCoefficient, toLaurent_coordinate A P Q hPQ hQP]
  apply Matrix.ext
  intro i j
  simp only [differentialCoefficient, Matrix.mul_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  funext x
  congr 1
  funext y
  ring

/-- An actual full-series unit gauge, embedded with its supplied true inverse. -/
def powerSeriesChange (q : ℕ) (A P B S : Series ι) (hPS : P*S=1) (hSP : S*P=1)
    (heq : A*P-P*B = -(PowerSeries.X^(q+2)*WasowPowerSeries.derivative P)) :
    Change (differentialCoefficient q A) (differentialCoefficient q B) where
  G := toLaurent P
  H := toLaurent S
  GH := (toLaurent_inverses P S hPS hSP).1
  HG := (toLaurent_inverses P S hPS hSP).2
  equation := powerSeries_gauge_equation q A P B heq

/-- Actual constant coordinates and the normalized complete-series gauge are
multiplied, producing one genuine Laurent gauge for a normalization edge. -/
def normalizationChange {A : Series ι} {q : ℕ} {next : FormalState}
    (d : Data A q next) : Change (differentialCoefficient q A)
      (differentialCoefficient q next.series) := by
  have hC := constantChange (differentialCoefficient q A) d.P d.Q d.PQ d.QP
  rw [← differentialCoefficient_coordinate q A d.P d.Q d.PQ d.QP] at hC
  exact hC.comp (powerSeriesChange q _ d.gauge next.series d.inverse
    d.inverse_right d.inverse_left d.equation)

section Blocks
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {I J : σ → Type*} [∀ a, Fintype (I a)] [∀ a, Fintype (J a)]
variable [∀ a, DecidableEq (I a)] [∀ a, DecidableEq (J a)]

omit [Fintype σ] [∀ a, Fintype (I a)] [∀ a, Fintype (J a)]
  [∀ a, DecidableEq (I a)] [∀ a, DecidableEq (J a)] in
theorem matrixDerivative_blocks (G : ∀ a, Matrix (I a) (J a) L) :
    matrixDerivative (Matrix.blockDiagonal' G) =
      Matrix.blockDiagonal' (fun a => matrixDerivative (G a)) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases hab : a=b
  · subst b
    simp [matrixDerivative]
  · simp [matrixDerivative, Matrix.blockDiagonal'_apply_ne _ _ _ hab]

/-- Finite branches are combined using actual block Laurent matrices, including
both inverse equations and the full derivative identity. -/
def blockChange (A : ∀ a, Matrix (I a) (I a) L) (B : ∀ a, Matrix (J a) (J a) L)
    (f : ∀ a, Change (A a) (B a)) :
    Change (Matrix.blockDiagonal' A) (Matrix.blockDiagonal' B) where
  G := Matrix.blockDiagonal' (fun a => (f a).G)
  H := Matrix.blockDiagonal' (fun a => (f a).H)
  GH := by
    rw [← Matrix.blockDiagonal'_mul]
    simp only [(f _).GH]
    exact Matrix.blockDiagonal'_one
  HG := by
    rw [← Matrix.blockDiagonal'_mul]
    simp only [(f _).HG]
    exact Matrix.blockDiagonal'_one
  equation := by
    unfold GaugeEquation
    rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul,
      ← Matrix.blockDiagonal'_sub, matrixDerivative_blocks]
    congr 1
    funext a
    exact (f a).equation

end Blocks

#print axioms constant_mul
#print axioms constant_one
#print axioms derivative_constant
#print axioms Change.comp
#print axioms Change.addScalar
#print axioms constantChange
#print axioms toLaurent_coordinate
#print axioms differentialCoefficient_coordinate
#print axioms powerSeriesChange
#print axioms normalizationChange
#print axioms matrixDerivative_blocks
#print axioms blockChange
end WasowGlobalFormalEdges
