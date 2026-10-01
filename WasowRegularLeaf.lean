import WasowFuchsianTruncation
import WasowFuchsianRealization

/-! The general regular formal leaf supplies its actual regular gauge.
The integer growth exponent is selected before the finite truncation order.
The scalar-phase corollary assumes the complete displayed formal canonical
identity, but assumes neither convergence of the formal regular block nor an
already realized regular gauge. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Operator
namespace WasowRegularLeaf
open CRGNormalFormGoal WasowFuchsianTruncation WasowFuchsianRealization
open WasowGaugeAssembly
variable {m : ℕ}

/-- The complete finite regular block constructs the actual regular gauge
required by analytic realization, for any sufficiently large integer exponent. -/
theorem exists_regularGauge
    (D : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (L : ℕ)
    (hL : ‖PowerSeries.constantCoeff D‖ + 1 ≤ L) {M : ℕ} (hM : 0 < M) :
    ∃ T S : ℝ → Matrix (Fin m) (Fin m) ℂ,
      Nonempty (RegularGauge (regularCoefficient D M) T S L) := by
  obtain ⟨R, C, hR, hC, T, S, hTc, hSc, hTd, _, hinv, hb⟩ :=
    exists_truncated_fundamental D hM
  have hp (r : ℝ) (hr : R ≤ r) : r ^ (‖PowerSeries.constantCoeff D‖ + 1) ≤ r ^ L := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le (hR.trans hr) hL
  let ctrl : WasowPolynomialTail.Control T S L := {
    C := C
    C_pos := hC
    R := R
    R_one := hR
    T_continuous := hTc
    S_continuous := hSc
    T_bound := fun r hr => (hb r hr).1.trans (mul_le_mul_of_nonneg_left (hp r hr) hC.le)
    S_bound := fun r hr => (hb r hr).2.trans (mul_le_mul_of_nonneg_left (hp r hr) hC.le) }
  refine ⟨T, S, ⟨{
    control := ctrl
    derivative := ?_
    inverse_left := fun r hr => (hinv r hr.le).1
    inverse_right := fun r hr => (hinv r hr.le).2 }⟩⟩
  intro r hr i j
  exact ((entryMap i j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r (hTd r hr)

/-- One integer exponent works for every finite truncation of the given
regular formal block. The radius and the constructed gauge may depend on it. -/
theorem exists_uniform_regular_exponent
    (D : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) :
    ∃ L : ℕ, ‖PowerSeries.constantCoeff D‖ + 1 ≤ L ∧
      ∀ M : ℕ, 0 < M → ∃ T S : ℝ → Matrix (Fin m) (Fin m) ℂ,
        Nonempty (RegularGauge (regularCoefficient D M) T S L) := by
  obtain ⟨L, hL⟩ := exists_nat_ge (‖PowerSeries.constantCoeff D‖ + 1)
  exact ⟨L, hL, fun _ hM => exists_regularGauge D L hL hM⟩

/-- A scalar phase on the whole block commutes with every actual regular
gauge, without any hypothesis on the regular coefficient matrices. -/
theorem scalar_diagonal_commute (c : ℂ) (T : Matrix (Fin m) (Fin m) ℂ) :
    Commute (Matrix.diagonal (fun _ => c)) T := by
  have heq : Matrix.diagonal (fun _ : Fin m => c) = c • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  rw [heq]
  show (c • (1 : Matrix (Fin m) (Fin m) ℂ)) * T = T * (c • 1)
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- A supplied finite canonical form with one scalar phase and an arbitrary
finite regular block has a true exact ray gauge. The regular gauge is actually
constructed here; no commutation or convergence assumption is needed for it. -/
theorem exists_exact_rayGauge_of_scalar_regular_leaf
    (A₀ : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ Rmin : ℝ)
    (D : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (L M : ℕ)
    (hL : ‖PowerSeries.constantCoeff D‖ + 1 ≤ L) (hM : 0 < M)
    {a : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (ha : HasFPowerSeriesAt a s 0)
    (A P B : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hc : ∀ n, s.coeff n = PowerSeries.coeff n A)
    (q N : ℕ) (hq : 0 < q) (hN : q + 2 * L + 1 ≤ N)
    (hP : PowerSeries.constantCoeff P = 1)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P))
    (p : ℕ) (hp : 0 < p) (F : Polynomial ℂ) (ℓ : Fin p)
    (hcoef : ∀ r > Rmin, coefficientOnRay A₀ θ r = rayCoefficient a q r)
    (hcanon : ∀ r > Rmin, truncatedCoefficient B q N r =
      Matrix.diagonal (fun _ => deriv (phaseOnRay p F θ ℓ) r) + regularCoefficient D M r)
    (hpole : ∀ r > Rmin, ∀ i j, (A₀ i j).denom.eval (ray θ r) ≠ 0) :
    Nonempty (RayGaugeWitness A₀ θ (fun _ => phaseOnRay p F θ ℓ)) := by
  obtain ⟨T, S, ⟨g⟩⟩ := exists_regularGauge D L hL hM
  exact exists_exact_rayGauge_of_fuchsian_formal_truncation A₀ θ Rmin
    (regularCoefficient D M) T S L g ha A P B hc q N hq hN hP heq p hp (fun _ => F) ℓ
    hcoef hcanon (fun r _ => scalar_diagonal_commute _ (T r)) hpole

#print axioms exists_regularGauge
#print axioms exists_uniform_regular_exponent
#print axioms scalar_diagonal_commute
#print axioms exists_exact_rayGauge_of_scalar_regular_leaf
end WasowRegularLeaf
