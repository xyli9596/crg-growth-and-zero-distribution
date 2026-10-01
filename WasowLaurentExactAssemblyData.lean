import WasowFuchsianRealization

/-! Concrete analytic inputs for exact realization of an arbitrary finite
Laurent gauge. No leading-identity or convergent formal-gauge hypothesis is used. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix.Norms.Operator
attribute [local instance] Measure.Subtype.measureSpace
namespace WasowLaurentExactAssembly
open WasowPolynomialTail WasowGaugeAssembly
variable {m : ℕ}
abbrev Mat := Matrix (Fin m) (Fin m) ℂ

local instance : ContinuousENorm (Matrix (Fin m) (Fin m) ℂ) where
  enorm M := (‖M‖₊ : ENNReal)
  continuous_enorm := by
    simp_rw [Matrix.linfty_opNNNorm_def]
    fun_prop

/-- An actual finite gauge with its derivative, true two-sided inverse and
polynomial control. The cleared leading matrix is allowed to be singular. -/
structure FiniteGauge (Z W Z' : ℝ → Mat (m := m)) (K : ℕ) where
  control : Control Z W K
  derivative : ∀ r > control.R, ∀ i j,
    HasDerivAt (fun t => Z t i j) (Z' r i j) r
  inverse_left : ∀ r > control.R, W r * Z r = 1
  inverse_right : ∀ r > control.R, Z r * W r = 1

/-- The actual conjugated residual has arbitrarily small integrable tails
beyond any prescribed radius. This intermediate property is supplied by the
finite-truncation estimate, rather than by an assumed approximate gauge. -/
def SmallConjugatedTails (T S E : ℝ → Mat (m := m)) : Prop :=
  ∀ Rmin ε : ℝ, 0<ε → ∃ R : ℝ, 1≤R ∧ Rmin≤R ∧
    ContinuousOn (fun r => S r * E r * T r) (Ici R) ∧
    IntegrableOn (fun r => S r * E r * T r) (Ici R) ∧
    (∫ r in Ici R, ‖S r * E r * T r‖) < ε

/-- The precise continuous linear operator consumed by the Volterra solver. -/
def tailOperator (T S E : ℝ → Mat (m := m)) (R : ℝ) :
    Ici R → ((Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) :=
  fun r => toOperator (S r * E r * T r)

/-- Multiplication adds the two genuine polynomial exponents. -/
theorem product_mulVec_bound (M N : Mat (m := m)) (C D : ℝ) (hC : 0≤C)
    (K L : ℕ) {r : ℝ} (hr : 0≤r)
    (hM : ‖M‖ ≤ C*r^K) (hN : ‖N‖ ≤ D*r^L) (x : Fin m → ℂ) :
    ‖(M*N).mulVec x‖ ≤ (C*D) * r ^ ((K+L:ℕ):ℝ) * ‖x‖ := by
  have hb : ‖M*N‖ ≤ (C*D)*r^(K+L) := by
    calc
      _ ≤ ‖M‖*‖N‖ := norm_mul_le _ _
      _ ≤ (C*r^K)*(D*r^L) := mul_le_mul hM hN (norm_nonneg _) (mul_nonneg hC (pow_nonneg hr _))
      _ = _ := by rw [pow_add]; ring
  exact (Matrix.linfty_opNorm_mulVec (M*N) x).trans
    (mul_le_mul_of_nonneg_right (by simpa only [Real.rpow_natCast] using hb) (norm_nonneg x))

#print axioms product_mulVec_bound
end WasowLaurentExactAssembly
