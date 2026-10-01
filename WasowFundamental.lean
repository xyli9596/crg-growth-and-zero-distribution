import WasowVolterra
import Mathlib.Topology.Instances.Matrix

/-!
# Actual fundamental matrices from the mixed Volterra columns

The phase directions, their monotonicity/decay, and the small L1 remainder tail
are explicit inputs. Columns are constructed by the existing fixed-point
lemma. Their normalized matrix tends to the identity, so the genuine solution
matrix is invertible on a sufficiently late real half-line. This does not
supply the formal reduction or automatically choose admissible phases/tails.
-/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology BoundedContinuousFunction
attribute [local instance] Measure.Subtype.measureSpace
open WasowVolterra
namespace WasowFundamental

theorem retract_tendsto_atTop (a : ℝ) : Tendsto (retract a) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b : ℝ)] with r hr
  change (b : ℝ) ≤ max a r
  exact hr.trans (le_max_right _ _)

theorem extend_tendsto {α : Type*} [TopologicalSpace α] {a : ℝ}
    {u : Ici a → α} {v : α} (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (extend a u) atTop (𝓝 v) := hu.comp (retract_tendsto_atTop a)

/-- Column `j` is the normalized mixed-Volterra solution with limit `eⱼ`. -/
def normalizedMatrix {m : ℕ} {a : ℝ}
    (u : Fin m → Ici a →ᵇ (Fin m → ℂ)) (r : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => extend a (u j) r i

/-- Restore the exponential phase on each column. -/
def fundamentalMatrix {m : ℕ} {a : ℝ}
    (u : Fin m → Ici a →ᵇ (Fin m → ℂ)) (Q : Fin m → ℝ → ℂ) (r : ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  normalizedMatrix u r * Matrix.diagonal (fun j => Complex.exp (Q j r))

@[simp] theorem fundamentalMatrix_apply {m : ℕ} {a : ℝ}
    (u : Fin m → Ici a →ᵇ (Fin m → ℂ)) (Q : Fin m → ℝ → ℂ)
    (r : ℝ) (i j : Fin m) :
    fundamentalMatrix u Q r i j = Complex.exp (Q j r) * extend a (u j) r i := by
  simp [fundamentalMatrix, Matrix.mul_diagonal, normalizedMatrix, mul_comm]

/-- The full normalized matrix tends to the identity, rather than merely
having separately prescribed entries on unrelated tails. -/
theorem normalizedMatrix_tendsto_one {m : ℕ} {a : ℝ}
    (u : Fin m → Ici a →ᵇ (Fin m → ℂ))
    (hu : ∀ j, Tendsto (u j) atTop (𝓝 (Pi.single j (1 : ℂ) : Fin m → ℂ))) :
    Tendsto (normalizedMatrix u) atTop (𝓝 1) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hentry := tendsto_pi_nhds.mp (extend_tendsto (hu j)) i
  simpa [normalizedMatrix, Matrix.one_apply, Pi.single_apply, eq_comm] using hentry

/-- The determinant is eventually nonzero because its limit is exactly one. -/
theorem eventually_det_normalizedMatrix_ne_zero {m : ℕ} {a : ℝ}
    (u : Fin m → Ici a →ᵇ (Fin m → ℂ))
    (hu : ∀ j, Tendsto (u j) atTop (𝓝 (Pi.single j (1 : ℂ) : Fin m → ℂ))) :
    ∀ᶠ r : ℝ in atTop, (normalizedMatrix u r).det ≠ 0 := by
  have hc : Continuous (fun M : Matrix (Fin m) (Fin m) ℂ => M.det) := continuous_id.matrix_det
  have hd := hc.tendsto (1 : Matrix (Fin m) (Fin m) ℂ)
  have hl := hd.comp (normalizedMatrix_tendsto_one u hu)
  simp only [Matrix.det_one] at hl
  have he : {z : ℂ | z ≠ 0} ∈ 𝓝 (1 : ℂ) :=
    isClosed_singleton.isOpen_compl.mem_nhds (by simp)
  simpa only [Function.comp_apply] using hl.eventually he

/-- Restoring exponentials preserves the nonzero determinant pointwise. -/
theorem det_fundamentalMatrix_ne_zero {m : ℕ} {a : ℝ}
    (u : Fin m → Ici a →ᵇ (Fin m → ℂ)) (Q : Fin m → ℝ → ℂ) {r : ℝ}
    (hu : (normalizedMatrix u r).det ≠ 0) : (fundamentalMatrix u Q r).det ≠ 0 := by
  rw [fundamentalMatrix, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero hu (Finset.prod_ne_zero_iff.mpr (fun j _ => Complex.exp_ne_zero _))

/-- A normalized column solving the phase-difference equation gives a column
of the actual solution matrix satisfying the original ODE. -/
theorem fundamentalMatrix_column_hasDerivAt {m : ℕ} {a : ℝ}
    (u : Fin m → Ici a →ᵇ (Fin m → ℂ)) (Q dQ : Fin m → ℝ → ℂ)
    (R : Ici a → (Fin m → ℂ) →L[ℂ] (Fin m → ℂ))
    (j : Fin m) {r : ℝ} (hQ : HasDerivAt (Q j) (dQ j r) r)
    (hu : HasDerivAt (extend a (u j))
      (fun i => (dQ i r-dQ j r)*extend a (u j) r i +
        (extend a R r (extend a (u j) r)) i) r) :
    HasDerivAt (fun t i => fundamentalMatrix u Q t i j)
      (fun i => dQ i r * fundamentalMatrix u Q r i j +
        (extend a R r (fun k => fundamentalMatrix u Q r k j)) i) r := by
  have hh := denormalize_hasDerivAt (extend a (u j)) (Q j) (fun i => dQ i r)
    (extend a R r) j hQ hu
  have hcol (t : ℝ) : Complex.exp (Q j t) • extend a (u j) t =
      (fun i => fundamentalMatrix u Q t i j) := by
    funext i
    simp only [fundamentalMatrix_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [hcol] using hh


/-- Actual fundamental-matrix construction under the mixed-Volterra hypotheses.
The first index of `mode` selects the column, the second the component. All
columns use the same half-line and the same integrable operator remainder. -/
theorem exists_fundamental_matrix (m : ℕ) (a : ℝ)
    (mode : Fin m → Fin m → Bool) (Q dQ : Fin m → ℝ → ℂ)
    (hQ : ∀ i, Continuous (Q i))
    (hdQ : ∀ i r, a < r → HasDerivAt (Q i) (dQ i r) r)
    (hord : ∀ j i, if mode j i then
      Antitone (fun t : Ici a => (Q i t-Q j t).re)
      else Monotone (fun t : Ici a => (Q i t-Q j t).re))
    (hdecay : ∀ j i, mode j i = true →
      Tendsto (fun r : Ici a => (Q i r-Q j r).re) atTop atBot)
    (R : Ici a → (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) (hR : Continuous R)
    (hL1 : Integrable (fun s : Ici a => ‖R s‖))
    (hsmall : (∫ s : Ici a, ‖R s‖) < 1) :
    ∃ u : Fin m → Ici a →ᵇ (Fin m → ℂ),
      (∀ j r i, u j r i = (Pi.single j (1 : ℂ) : Fin m → ℂ) i + ∫ s : Ici a,
        MixedVolterra.kernel (mode j i) (fun t : Ici a => Q i t-Q j t) r s *
          (R s (u j s)) i) ∧
      Tendsto (normalizedMatrix u) atTop (𝓝 1) ∧
      (∀ r : ℝ, a < r → ∀ j, HasDerivAt (fun t i => fundamentalMatrix u Q t i j)
        (fun i => dQ i r * fundamentalMatrix u Q r i j +
          (extend a R r (fun k => fundamentalMatrix u Q r k j)) i) r) ∧
      ∃ A : ℝ, a < A ∧ ∀ r : ℝ, A ≤ r →
        (normalizedMatrix u r).det ≠ 0 ∧ (fundamentalMatrix u Q r).det ≠ 0 := by
  classical
  choose u hu hlim hode using fun j => exists_phase_difference_column_ode m a j
    (mode j) Q dQ hQ hdQ (hord j) (hdecay j) R hR hL1 hsmall
  refine ⟨u, hu, normalizedMatrix_tendsto_one u hlim, ?_, ?_⟩
  · intro r hr j
    exact fundamentalMatrix_column_hasDerivAt u Q dQ R j (hdQ j r hr) (hode j r hr)
  · obtain ⟨A, hA⟩ := eventually_atTop.mp (eventually_det_normalizedMatrix_ne_zero u hlim)
    refine ⟨max A (a+1), (lt_add_one a).trans_le (le_max_right _ _), fun r hr => ?_⟩
    have hdet := hA r ((le_max_left _ _).trans hr)
    exact ⟨hdet, det_fundamentalMatrix_ne_zero u Q hdet⟩

end WasowFundamental

#print axioms WasowFundamental.retract_tendsto_atTop
#print axioms WasowFundamental.extend_tendsto
#print axioms WasowFundamental.fundamentalMatrix_apply
#print axioms WasowFundamental.normalizedMatrix_tendsto_one
#print axioms WasowFundamental.eventually_det_normalizedMatrix_ne_zero
#print axioms WasowFundamental.det_fundamentalMatrix_ne_zero
#print axioms WasowFundamental.fundamentalMatrix_column_hasDerivAt

#print axioms WasowFundamental.exists_fundamental_matrix
