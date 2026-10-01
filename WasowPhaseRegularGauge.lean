import WasowRegularLeaf

/-! The actual regular fundamental matrix preserves every phase fiber.
The commutation conclusion follows from the initialized matrix ODE and its
true inverse: the derivative of `S * D * T` is zero whenever the coefficient
commutes with the constant matrix `D`.  No commutation property of a solution
is assumed. The integer growth exponent is chosen before truncation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter
open scoped Topology BigOperators Matrix.Norms.Operator
namespace WasowPhaseRegularGauge
open WasowFuchsianRealization WasowFuchsianTruncation WasowMatrixPolynomial
variable {m : ℕ}

/-- Constants in the commutant of the coefficient remain in the commutant
of the actual initialized fundamental matrix and of its true inverse. -/
theorem matrix_solutions_commute (a : ℝ)
    (A T S : ℝ → Matrix (Fin m) (Fin m) ℂ)
    (hT0 : T a = 1) (hS0 : S a = 1)
    (hTc : ContinuousOn T (Ici a)) (hSc : ContinuousOn S (Ici a))
    (hTd : ∀ r > a, HasDerivAt T (A r * T r) r)
    (hSd : ∀ r > a, HasDerivAt S (-(S r * A r)) r)
    (D : Matrix (Fin m) (Fin m) ℂ)
    (hD : ∀ r > a, Commute D (A r)) :
    ∀ r ≥ a, Commute D (T r) ∧ Commute D (S r) := by
  have hd (r : ℝ) (hr : a < r) :
      HasDerivAt (fun t => S t * D * T t) 0 r := by
    have he : -(S r * A r) * D * T r + S r * D * (A r * T r) = 0 := by
      calc
        _ = -(S r * (A r * D) * T r) + S r * (D * A r) * T r := by noncomm_ring
        _ = 0 := by rw [← (hD r hr).eq]; abel
    have hSD (i j : Fin m) :
        HasDerivAt (fun t => (S t * D) i j) ((-(S r * A r) * D) i j) r := by
      have hh := WasowRealization.matrix_product_hasDerivAt S (fun _ => D)
        (-(S r*A r)) 0
        (fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp (hSd r hr) i) j)
        (fun i j => hasDerivAt_const r (D i j)) i j
      simpa only [Matrix.mul_zero, add_zero] using hh
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    have hh := WasowRealization.matrix_product_hasDerivAt (fun t => S t*D) T
      (-(S r*A r)*D) (A r*T r) hSD
      (fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp (hTd r hr) i) j) i j
    simpa only [he, Matrix.zero_apply] using hh
  have he : EqOn (fun t => S t * D * T t)
      (fun _ => S (a + 1) * D * T (a + 1)) (Ioi a) := by
    intro r hr
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (f := fun t => S t * D * T t)
      (convex_Ioi a).isPreconnected
      (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hd r hr).deriv) hr (show a < a + 1 by linarith)
  have he' : EqOn (fun t => S t * D * T t)
      (fun _ => S (a + 1) * D * T (a + 1)) (Ici a) :=
    he.of_subset_closure ((hSc.mul continuousOn_const).mul hTc)
      continuousOn_const Ioi_subset_Ici_self (by rw [closure_Ioi])
  have hinit := he' (show a ∈ Ici a from le_refl a)
  change S a * D * T a = _ at hinit
  rw [hS0, hT0, one_mul, mul_one] at hinit
  intro r hr
  have hconj : S r * D * T r = D := (he' hr).trans hinit.symm
  obtain ⟨hST, hTS⟩ := WasowFuchsianBounds.matrix_solutions_inverse a A T S
    hT0 hS0 hTc hSc hTd hSd r hr
  constructor
  · show D * T r = T r * D
    calc
      _ = T r * (S r * D * T r) := by rw [← mul_assoc, ← mul_assoc, hTS, one_mul]
      _ = _ := by rw [hconj]
  · show D * S r = S r * D
    calc
      _ = (S r * D * T r) * S r := by rw [hconj]
      _ = _ := by rw [mul_assoc, hTS, mul_one]

/-- A matrix with zero entries between distinct fibers commutes with each
diagonal whose entries are constant on those fibers. -/
theorem diagonal_commute_of_separated {β : Type*} (F : Fin m → β)
    (A : Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ i j, F i ≠ F j → A i j = 0)
    (c : Fin m → ℂ) (hc : ∀ i j, F i = F j → c i = c j) :
    Commute (Matrix.diagonal c) A := by
  show Matrix.diagonal c * A = A * Matrix.diagonal c
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : F i = F j
  · rw [hc i j h, mul_comm]
  · rw [hA i j h]; simp

/-- The actual finite polynomial retains every zero off-fiber entry. -/
theorem eval_trunc_separated {β : Type*} (F : Fin m → β)
    (R : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hR : ∀ n i j, F i ≠ F j → (PowerSeries.coeff n R) i j = 0)
    (M : ℕ) (z : ℂ) (i j : Fin m) (hij : F i ≠ F j) :
    eval (PowerSeries.trunc M R) z i j = 0 := by
  rw [eval_eq_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro n hn
  rw [PowerSeries.coeff_trunc]
  split_ifs <;> simp [hR n i j hij]

/-- Every actual regular truncation has a coefficient commuting with every
constant diagonal on the original phase fibers. -/
theorem regularCoefficient_commute {β : Type*} (F : Fin m → β)
    (R : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hR : ∀ n i j, F i ≠ F j → (PowerSeries.coeff n R) i j = 0)
    (M : ℕ) (r : ℝ) (c : Fin m → ℂ)
    (hc : ∀ i j, F i = F j → c i = c j) :
    Commute (Matrix.diagonal c) (regularCoefficient R M r) := by
  apply diagonal_commute_of_separated F _ _ c hc
  intro i j hij
  change (r : ℂ)⁻¹ * eval (PowerSeries.trunc M R) (r : ℂ)⁻¹ i j = 0
  rw [eval_trunc_separated F R hR M _ i j hij, mul_zero]

/-- The initialized ODE constructs one genuine regular gauge which commutes
with all fiber-constant diagonals simultaneously. -/
theorem exists_regularGauge_preserving_fibers {β : Type*} (F : Fin m → β)
    (R : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (hR : ∀ n i j, F i ≠ F j → (PowerSeries.coeff n R) i j = 0)
    (L : ℕ) (hL : ‖PowerSeries.constantCoeff R‖ + 1 ≤ L)
    {M : ℕ} (hM : 0 < M) :
    ∃ T S : ℝ → Matrix (Fin m) (Fin m) ℂ,
      ∃ g : RegularGauge (regularCoefficient R M) T S L,
        ∀ r > g.control.R, ∀ c : Fin m → ℂ,
          (∀ i j, F i = F j → c i = c j) →
          Commute (Matrix.diagonal c) (T r) ∧ Commute (Matrix.diagonal c) (S r) := by
  obtain ⟨a, ha, hc, hb⟩ := exists_regular_tail_bound R hM
  obtain ⟨T, S, hT0, hS0, hTc, hSc, hTd, hSd⟩ :=
    WasowFuchsianFundamental.exists_matrix_solutions (regularCoefficient R M) hc
  obtain ⟨C, hC, hbound⟩ := WasowFuchsianBounds.matrix_solutions_bounds a (a + 1)
    (‖PowerSeries.constantCoeff R‖ + 1) (regularCoefficient R M) T S
    (by linarith) (by linarith) (by positivity) hTd hSd (fun r hr => hb r hr.le)
  have hinv := WasowFuchsianBounds.matrix_solutions_inverse a
    (regularCoefficient R M) T S hT0 hS0 hTc hSc hTd hSd
  have hp (r : ℝ) (hr : a + 1 ≤ r) : r ^ (‖PowerSeries.constantCoeff R‖ + 1) ≤ r ^ L := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ r) hL
  let ctrl : WasowPolynomialTail.Control T S L := {
    C := C, C_pos := hC, R := a + 1, R_one := by linarith
    T_continuous := hTc.mono (Ici_subset_Ici.mpr (by linarith))
    S_continuous := hSc.mono (Ici_subset_Ici.mpr (by linarith))
    T_bound := fun r hr => (hbound r hr).1.trans (mul_le_mul_of_nonneg_left (hp r hr) hC.le)
    S_bound := fun r hr => (hbound r hr).2.trans (mul_le_mul_of_nonneg_left (hp r hr) hC.le) }
  let g : RegularGauge (regularCoefficient R M) T S L := {
    control := ctrl
    derivative := fun r hr i j => ((WasowGaugeAssembly.entryMap i j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r
      (hTd r (by dsimp [ctrl] at hr; linarith))
    inverse_left := fun r hr => (hinv r (by dsimp [ctrl] at hr; linarith)).1
    inverse_right := fun r hr => (hinv r (by dsimp [ctrl] at hr; linarith)).2 }
  refine ⟨T, S, g, ?_⟩
  intro r hr c hcf
  apply matrix_solutions_commute a (regularCoefficient R M) T S hT0 hS0 hTc hSc hTd hSd
    (Matrix.diagonal c) (fun r _ => regularCoefficient_commute F R hR M r c hcf) r
  dsimp [g, ctrl] at hr
  linarith

#print axioms matrix_solutions_commute
#print axioms diagonal_commute_of_separated
#print axioms eval_trunc_separated
#print axioms regularCoefficient_commute
#print axioms exists_regularGauge_preserving_fibers
end WasowPhaseRegularGauge
