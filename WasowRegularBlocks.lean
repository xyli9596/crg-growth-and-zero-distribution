import WasowRegularLeaf
import WasowPhaseFamilyBlocks

/-! Finite assembly of general regular formal leaves. One common integer
exponent is selected before truncation; every finite regular coefficient is
retained. Block-scalar phases commute with the constructed block gauge. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators Matrix.Norms.Operator
namespace WasowRegularBlocks
open WasowPhaseFamilyBlocks WasowRegularLeaf WasowFuchsianTruncation
open WasowFuchsianRealization WasowPolynomialTail
variable {s : ℕ} (d : Fin s → ℕ)

theorem blockMatrix_continuousOn
    (T : ∀ a, ℝ → Matrix (Fin (d a)) (Fin (d a)) ℂ) (I : Set ℝ)
    (hT : ∀ a, ContinuousOn (T a) I) :
    ContinuousOn (fun r => blockMatrix d (fun a => T a r)) I := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  obtain ⟨⟨a,i⟩,rfl⟩ := (columns d).surjective i
  obtain ⟨⟨b,j⟩,rfl⟩ := (columns d).surjective j
  by_cases hab : a = b
  · subst b
    simpa only [blockMatrix_apply_same] using
      (continuousOn_pi.mp (continuousOn_pi.mp (hT a) i) j)
  · simpa only [blockMatrix_apply_ne d _ a b hab] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ)) I)

/-- Actual finite block assembly retains derivatives and inverse identities,
while taking a common radius and a common operator-norm bound. -/
theorem assemble_regularGauge
    (J T S : ∀ a, ℝ → Matrix (Fin (d a)) (Fin (d a)) ℂ) (L : ℕ)
    (g : ∀ a, RegularGauge (J a) (T a) (S a) L) :
    Nonempty (RegularGauge (fun r => blockMatrix d (fun a => J a r))
      (fun r => blockMatrix d (fun a => T a r))
      (fun r => blockMatrix d (fun a => S a r)) L) := by
  let R : ℝ := 1 + ∑ a, (g a).control.R
  let C : ℝ := 1 + ∑ a, (g a).control.C
  have hR : 1 ≤ R := by
    dsimp [R]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ =>
      zero_le_one.trans (g a).control.R_one)
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun a _ =>
      (g a).control.C_pos.le)
  have hRg (a : Fin s) : (g a).control.R ≤ R := by
    have hh := Finset.single_le_sum (fun b _ => zero_le_one.trans (g b).control.R_one)
      (Finset.mem_univ a)
    dsimp [R]; linarith
  have hCg (a : Fin s) : (g a).control.C ≤ C := by
    have hh := Finset.single_le_sum (fun b _ => (g b).control.C_pos.le) (Finset.mem_univ a)
    dsimp [C]; linarith
  have hbound (M : ∀ a, ℝ → Matrix (Fin (d a)) (Fin (d a)) ℂ)
      (hb : ∀ a r, (g a).control.R ≤ r → ‖M a r‖ ≤ (g a).control.C * r ^ L)
      (r : ℝ) (hr : R ≤ r) : ‖blockMatrix d (fun a => M a r)‖ ≤ C * r ^ L := by
    have hn : 0 ≤ r := zero_le_one.trans (hR.trans hr)
    apply WasowRegularTail.matrix_norm_le_of_mulVec_bound _ (mul_nonneg hC.le (pow_nonneg hn _))
    apply blockMatrix_bound d _ _ (mul_nonneg hC.le (pow_nonneg hn _))
    intro a x
    apply (Matrix.linfty_opNorm_mulVec (M a r) x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    exact (hb a r ((hRg a).trans hr)).trans
      (mul_le_mul_of_nonneg_right (hCg a) (pow_nonneg hn _))
  let ctrl : Control (fun r => blockMatrix d (fun a => T a r))
      (fun r => blockMatrix d (fun a => S a r)) L := {
    C := C
    C_pos := hC
    R := R
    R_one := hR
    T_continuous := blockMatrix_continuousOn d T (Ici R)
      (fun a => (g a).control.T_continuous.mono (Ici_subset_Ici.mpr (hRg a)))
    S_continuous := blockMatrix_continuousOn d S (Ici R)
      (fun a => (g a).control.S_continuous.mono (Ici_subset_Ici.mpr (hRg a)))
    T_bound := hbound T (fun a => (g a).control.T_bound)
    S_bound := hbound S (fun a => (g a).control.S_bound) }
  refine ⟨{
    control := ctrl
    derivative := ?_
    inverse_left := ?_
    inverse_right := ?_ }⟩
  · intro r hr i j
    rw [← blockMatrix_mul]
    exact blockMatrix_hasDerivAt d T (fun a => J a r * T a r) r
      (fun a => (g a).derivative r ((hRg a).trans_lt hr)) i j
  · intro r hr
    rw [← blockMatrix_mul]
    have heq : (fun a => S a r * T a r) = (fun a => (1 : Matrix (Fin (d a)) (Fin (d a)) ℂ)) := by
      funext a
      exact (g a).inverse_left r ((hRg a).trans_lt hr)
    rw [heq, blockMatrix_one]
  · intro r hr
    rw [← blockMatrix_mul]
    have heq : (fun a => T a r * S a r) = (fun a => (1 : Matrix (Fin (d a)) (Fin (d a)) ℂ)) := by
      funext a
      exact (g a).inverse_right r ((hRg a).trans_lt hr)
    rw [heq, blockMatrix_one]

/-- Every block-scalar phase commutes with the complete assembled gauge. -/
theorem block_scalar_commute (c : Fin s → ℂ)
    (T : ∀ a, Matrix (Fin (d a)) (Fin (d a)) ℂ) :
    Commute (Matrix.diagonal (fun i => c ((columns d).symm i).1)) (blockMatrix d T) := by
  rw [← blockMatrix_diagonal d (fun a _ => c a)]
  change _ * _ = _ * _
  rw [← blockMatrix_mul, ← blockMatrix_mul]
  congr 1
  funext a
  exact (scalar_diagonal_commute (c a) (T a)).eq

/-- Actual block regular gauges for any common integer exponent dominating
all residues. This exponent is allowed to be fixed before choosing M. -/
theorem exists_block_regularGauge
    (D : ∀ a, PowerSeries (Matrix (Fin (d a)) (Fin (d a)) ℂ)) (L : ℕ)
    (hL : ∀ a, ‖PowerSeries.constantCoeff (D a)‖ + 1 ≤ L)
    {M : ℕ} (hM : 0 < M) :
    ∃ T S : ∀ a, ℝ → Matrix (Fin (d a)) (Fin (d a)) ℂ,
      Nonempty (RegularGauge (fun r => blockMatrix d (fun a => regularCoefficient (D a) M r))
        (fun r => blockMatrix d (fun a => T a r))
        (fun r => blockMatrix d (fun a => S a r)) L) := by
  classical
  choose T S hg using fun a => exists_regularGauge (D a) L (hL a) hM
  exact ⟨T, S, assemble_regularGauge d _ T S L (fun a => Classical.choice (hg a))⟩

/-- One integer exponent controls all finite regular truncations on all
blocks. Neither the formal series nor a putative infinite gauge is evaluated. -/
theorem exists_uniform_block_regularGauge
    (D : ∀ a, PowerSeries (Matrix (Fin (d a)) (Fin (d a)) ℂ)) :
    ∃ L : ℕ, (∀ a, ‖PowerSeries.constantCoeff (D a)‖ + 1 ≤ L) ∧
      ∀ M : ℕ, 0 < M →
        ∃ T S : ∀ a, ℝ → Matrix (Fin (d a)) (Fin (d a)) ℂ,
          Nonempty (RegularGauge (fun r => blockMatrix d (fun a => regularCoefficient (D a) M r))
            (fun r => blockMatrix d (fun a => T a r))
            (fun r => blockMatrix d (fun a => S a r)) L) := by
  classical
  choose L hL using fun a => exists_nat_ge (‖PowerSeries.constantCoeff (D a)‖ + 1)
  let K : ℕ := ∑ a, L a
  have hK (a : Fin s) : ‖PowerSeries.constantCoeff (D a)‖ + 1 ≤ K := by
    apply (hL a).trans
    exact_mod_cast (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a) :
      L a ≤ ∑ b, L b)
  exact ⟨K, hK, fun _ hM => exists_block_regularGauge d D K hK hM⟩

/-- A complete finite canonical form with finitely many scalar-phase regular
blocks is analytically realized. The full block regular gauges and their
commutation with the phase diagonal are constructed by this theorem. -/
theorem exists_exact_rayGauge_of_regular_blocks
    (A₀ : Matrix (Fin (∑ a, d a)) (Fin (∑ a, d a)) (RatFunc ℂ)) (θ Rmin : ℝ)
    (D : ∀ a, PowerSeries (Matrix (Fin (d a)) (Fin (d a)) ℂ)) (L M : ℕ)
    (hL : ∀ a, ‖PowerSeries.constantCoeff (D a)‖ + 1 ≤ L) (hM : 0 < M)
    {a : ℂ → Matrix (Fin (∑ a, d a)) (Fin (∑ a, d a)) ℂ}
    {z : FormalMultilinearSeries ℂ ℂ (Matrix (Fin (∑ a, d a)) (Fin (∑ a, d a)) ℂ)}
    (ha : HasFPowerSeriesAt a z 0)
    (A P B : PowerSeries (Matrix (Fin (∑ a, d a)) (Fin (∑ a, d a)) ℂ))
    (hc : ∀ n, z.coeff n = PowerSeries.coeff n A)
    (q N : ℕ) (hq : 0 < q) (hN : q + 2 * L + 1 ≤ N)
    (hP : PowerSeries.constantCoeff P = 1)
    (heq : A * P - P * B = -(PowerSeries.X ^ (q + 1) * WasowPowerSeries.derivative P))
    (p : ℕ) (hp : 0 < p) (F : Fin s → Polynomial ℂ) (ℓ : Fin p)
    (hcoef : ∀ r > Rmin, CRGNormalFormGoal.coefficientOnRay A₀ θ r =
      WasowGaugeAssembly.rayCoefficient a q r)
    (hcanon : ∀ r > Rmin, WasowGaugeAssembly.truncatedCoefficient B q N r =
      Matrix.diagonal (fun i => deriv
        (CRGNormalFormGoal.phaseOnRay p (F ((columns d).symm i).1) θ ℓ) r) +
      blockMatrix d (fun a => regularCoefficient (D a) M r))
    (hpole : ∀ r > Rmin, ∀ i j, (A₀ i j).denom.eval (CRGNormalFormGoal.ray θ r) ≠ 0) :
    Nonempty (CRGNormalFormGoal.RayGaugeWitness A₀ θ
      (fun i => CRGNormalFormGoal.phaseOnRay p (F ((columns d).symm i).1) θ ℓ)) := by
  obtain ⟨T, S, ⟨g⟩⟩ := exists_block_regularGauge d D L hL hM
  exact exists_exact_rayGauge_of_fuchsian_formal_truncation A₀ θ Rmin
    (fun r => blockMatrix d (fun a => regularCoefficient (D a) M r))
    (fun r => blockMatrix d (fun a => T a r))
    (fun r => blockMatrix d (fun a => S a r)) L g ha A P B hc q N hq hN hP heq
    p hp (fun i => F ((columns d).symm i).1) ℓ hcoef hcanon
    (fun r _ => block_scalar_commute d
      (fun a => deriv (CRGNormalFormGoal.phaseOnRay p (F a) θ ℓ) r) (fun a => T a r)) hpole

#print axioms exists_exact_rayGauge_of_regular_blocks

#print axioms blockMatrix_continuousOn
#print axioms assemble_regularGauge
#print axioms block_scalar_commute
#print axioms exists_block_regularGauge
#print axioms exists_uniform_block_regularGauge
end WasowRegularBlocks
