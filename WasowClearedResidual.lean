import WasowActualTruncation

/-! High-order residuals after clearing the pole of a Laurent gauge.
The polynomial gauge may have a singular constant coefficient. The formal
identity includes the derivative of its scalar pole factor explicitly. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology Matrix.Norms.Operator
open Filter Asymptotics
namespace WasowClearedResidual
open WasowMatrixPolynomial WasowActualTruncation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Series := PowerSeries (Matrix ι ι ℂ)

/-- If the gauge is t^(-a) P and both differential coefficients have pole
order at most h, this is the full differential equation after clearing powers. -/
def Equation (a h : ℕ) (A P B : Series (ι := ι)) : Prop :=
  A * P - P * B = PowerSeries.X ^ h * WasowPowerSeries.derivative P -
    (a : ℂ) • (PowerSeries.X ^ (h - 1) * P)

def polynomialDefect (a h N : ℕ) (A P B : Series (ι := ι)) : Polynomial (Matrix ι ι ℂ) :=
  PowerSeries.trunc N A * PowerSeries.trunc N P -
    PowerSeries.trunc N P * PowerSeries.trunc N B -
    Polynomial.X ^ h * (PowerSeries.trunc N P).derivative +
    (a : ℂ) • (Polynomial.X ^ (h - 1) * PowerSeries.trunc N P)

/-- Multiplication by a nonnegative power cannot expose a discarded term. -/
theorem coeff_shifted_truncation (P : Series (ι := ι)) (d : ℕ)
    {N k : ℕ} (hk : k < N) :
    PowerSeries.coeff k (PowerSeries.X ^ d *
      ((PowerSeries.trunc N P : Polynomial (Matrix ι ι ℂ)) : Series)) =
      PowerSeries.coeff k (PowerSeries.X ^ d * P) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  split_ifs with hd
  · exact WasowTruncation.coeff_truncation P (by omega)
  · rfl

/-- Every low coefficient cancels using the actual cleared formal equation. -/
theorem polynomialDefect_coeff_zero (a h N : ℕ) (hh : 0 < h)
    (A P B : Series (ι := ι)) (heq : Equation a h A P B) :
    ∀ k < N, (polynomialDefect a h N A P B).coeff k = 0 := by
  intro k hk
  have hA := fun i hi => WasowTruncation.coeff_truncation A (N := N) (k := i) hi
  have hP := fun i hi => WasowTruncation.coeff_truncation P (N := N) (k := i) hi
  have hB := fun i hi => WasowTruncation.coeff_truncation B (N := N) (k := i) hi
  have hAP := WasowTruncation.coeff_mul_congr_below hk hA hP
  have hPB := WasowTruncation.coeff_mul_congr_below hk hP hB
  have hd := WasowTruncation.coeff_shifted_derivative_truncation P (h - 1) hk
  rw [Nat.sub_add_cancel hh] at hd
  have hs := coeff_shifted_truncation P (h - 1) hk
  have he : A * P - P * B - PowerSeries.X ^ h * WasowPowerSeries.derivative P +
      (a : ℂ) • (PowerSeries.X ^ (h - 1) * P) = 0 := by
    rw [heq]
    abel
  have hc := congrArg (PowerSeries.coeff k) he
  simp only [map_add, map_sub, PowerSeries.coeff_smul, map_zero] at hc
  have hsm (Q : Polynomial (Matrix ι ι ℂ)) (v : ℂ) :
      PowerSeries.coeff k ((v • Q : Polynomial (Matrix ι ι ℂ)) : Series) =
        v • PowerSeries.coeff k (Q : PowerSeries (Matrix ι ι ℂ)) := by
    simp only [Polynomial.coeff_coe, Polynomial.coeff_smul]
  rw [← Polynomial.coeff_coe]
  simpa only [polynomialDefect, Polynomial.coe_add, coe_sub_noncomm,
    Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, coe_derivative,
    map_add, map_sub, hsm, PowerSeries.coeff_smul, hAP, hPB, hd, hs] using hc

theorem polynomialDefect_divisible (a h N : ℕ) (hh : 0 < h)
    (A P B : Series (ι := ι)) (heq : Equation a h A P B) :
    Polynomial.X ^ N ∣ polynomialDefect a h N A P B :=
  Polynomial.X_pow_dvd_iff.mpr (polynomialDefect_coeff_zero a h N hh A P B heq)

/-- The concrete cleared residual of the actual analytic coefficient and the
finite gauge and target. No infinite formal gauge is evaluated. -/
def actualDefect (a h N : ℕ) (c : ℂ → Matrix ι ι ℂ)
    (P B : Series (ι := ι)) (z : ℂ) : Matrix ι ι ℂ :=
  c z * eval (PowerSeries.trunc N P) z -
    eval (PowerSeries.trunc N P) z * eval (PowerSeries.trunc N B) z -
    z ^ h • deriv (eval (PowerSeries.trunc N P)) z +
    ((a : ℂ) * z ^ (h - 1)) • eval (PowerSeries.trunc N P) z

/-- Exact separation into the analytic Taylor remainder and a finite polynomial. -/
theorem actualDefect_eq (a h N : ℕ) (c : ℂ → Matrix ι ι ℂ)
    (A P B : Series (ι := ι)) (z : ℂ) :
    actualDefect a h N c P B z =
      (c z - eval (PowerSeries.trunc N A) z) * eval (PowerSeries.trunc N P) z +
        eval (polynomialDefect a h N A P B) z := by
  unfold actualDefect polynomialDefect
  have hd : deriv (eval (PowerSeries.trunc N P)) z = eval (PowerSeries.trunc N P).derivative z :=
    (hasDerivAt_eval (PowerSeries.trunc N P) z).deriv
  rw [hd]
  have hsm (v : ℂ) (Q : Polynomial (Matrix ι ι ℂ)) : eval (v • Q) z = v • eval Q z := by
    change evaluation z (v • Q) = _
    rw [Algebra.smul_def, map_mul]
    simp [eval, evaluation, Polynomial.eval₂RingHom'_apply, Algebra.algebraMap_eq_smul_one]
  rw [eval_add, eval_sub, eval_sub, eval_mul, eval_mul, eval_X_pow_mul,
    hsm, eval_X_pow_mul, smul_smul, Matrix.sub_mul]
  abel

/-- Arbitrarily high-order actual residual; no invertibility or convergence
assumption is made on the formal P or B. Pole losses are accounted for later. -/
theorem actualDefect_isBigO
    (a h N : ℕ) (hh : 0 < h)
    {c : ℂ → Matrix ι ι ℂ} {s : FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ)}
    (hc : HasFPowerSeriesAt c s 0) (A P B : Series (ι := ι))
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n A) (heq : Equation a h A P B) :
    actualDefect a h N c P B =O[𝓝 (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ N) := by
  have hA : (fun z : ℂ => c z - eval (PowerSeries.trunc N A) z) =O[𝓝 0]
      (fun z : ℂ => ‖z‖ ^ N) := by
    exact (hc.isBigO_sub_partialSum_pow N).congr_left
      (fun z => by rw [zero_add, eval_trunc_eq_partialSum s A hcoeff]; rfl)
  have hP : eval (PowerSeries.trunc N P) =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) :=
    isBigO_const_of_tendsto ((continuous_eval _).tendsto 0) (by norm_num)
  have hproduct : (fun z : ℂ =>
      (c z - eval (PowerSeries.trunc N A) z) * eval (PowerSeries.trunc N P) z) =O[𝓝 0]
      (fun z : ℂ => ‖z‖ ^ N) := by
    simpa only [mul_one] using hA.mul hP
  have hfinite := isBigO_eval_of_X_pow_dvd (polynomialDefect a h N A P B) N
    (polynomialDefect_divisible a h N hh A P B heq)
  exact (hproduct.add hfinite).congr_left (fun z => (actualDefect_eq a h N c A P B z).symm)

#print axioms coeff_shifted_truncation
#print axioms polynomialDefect_coeff_zero
#print axioms polynomialDefect_divisible
#print axioms actualDefect_eq
#print axioms actualDefect_isBigO
end WasowClearedResidual
