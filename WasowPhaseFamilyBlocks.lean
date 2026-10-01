import WasowPhaseFamily
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Actual finite block assembly, including a common tail, operator bounds,
nonpoles and entrywise derivatives. Different child phase denominators are
reconciled by a single product denominator fixed before the ray angle. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowPhaseFamilyBlocks
open CRGNormalFormGoal WasowPhaseFamily
variable {s : ℕ} (d : Fin s → ℕ)

def columns : (Σ a, Fin (d a)) ≃ Fin (∑ a, d a) := finSigmaFinEquiv

def blockMatrix {R : Type*} [Zero R] (M : ∀ a, Matrix (Fin (d a)) (Fin (d a)) R) :
    Matrix (Fin (∑ a, d a)) (Fin (∑ a, d a)) R :=
  (Matrix.blockDiagonal' M).submatrix (columns d).symm (columns d).symm

theorem blockMatrix_apply_same {R : Type*} [Zero R]
    (M : ∀ a, Matrix (Fin (d a)) (Fin (d a)) R) (a : Fin s) (i j : Fin (d a)) :
    blockMatrix d M (columns d ⟨a,i⟩) (columns d ⟨a,j⟩) = M a i j := by
  simp [blockMatrix]

theorem blockMatrix_apply_ne {R : Type*} [Zero R]
    (M : ∀ a, Matrix (Fin (d a)) (Fin (d a)) R) (a b : Fin s)
    (h : a ≠ b) (i : Fin (d a)) (j : Fin (d b)) :
    blockMatrix d M (columns d ⟨a,i⟩) (columns d ⟨b,j⟩) = 0 := by
  simp [blockMatrix, Matrix.blockDiagonal'_apply_ne _ _ _ h]

theorem blockMatrix_mul {R : Type*} [NonUnitalNonAssocSemiring R]
    (M N : ∀ a, Matrix (Fin (d a)) (Fin (d a)) R) :
    blockMatrix d (fun a => M a * N a) = blockMatrix d M * blockMatrix d N := by
  unfold blockMatrix
  rw [Matrix.blockDiagonal'_mul, Matrix.submatrix_mul_equiv]

theorem blockMatrix_sub {R : Type*} [AddGroup R]
    (M N : ∀ a, Matrix (Fin (d a)) (Fin (d a)) R) :
    blockMatrix d (fun a => M a - N a) = blockMatrix d M - blockMatrix d N := by
  unfold blockMatrix
  change (Matrix.blockDiagonal' (M - N)).submatrix _ _ = _
  rw [Matrix.blockDiagonal'_sub]
  rfl

theorem blockMatrix_one {R : Type*} [Zero R] [One R] :
    blockMatrix d (fun _ => (1 : Matrix _ _ R)) = 1 := by
  unfold blockMatrix
  change (Matrix.blockDiagonal' (1 : ∀ a, Matrix (Fin (d a)) (Fin (d a)) R)).submatrix _ _ = _
  rw [Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

theorem blockMatrix_diagonal {R : Type*} [Zero R] (v : ∀ a, Fin (d a) → R) :
    blockMatrix d (fun a => Matrix.diagonal (v a)) =
      Matrix.diagonal (fun i => v ((columns d).symm i).1 ((columns d).symm i).2) := by
  unfold blockMatrix
  rw [Matrix.blockDiagonal'_diagonal, Matrix.submatrix_diagonal_equiv]
  rfl

theorem blockMatrix_mulVec (M : ∀ a, Matrix (Fin (d a)) (Fin (d a)) ℂ)
    (x : Fin (∑ a, d a) → ℂ) (a : Fin s) (i : Fin (d a)) :
    (blockMatrix d M).mulVec x (columns d ⟨a,i⟩) =
      (M a).mulVec (fun j => x (columns d ⟨a,j⟩)) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (columns d)]
  simp only [Fintype.sum_sigma]
  rw [Fintype.sum_eq_single a]
  · simp only [blockMatrix_apply_same]
  · intro b hb
    apply Finset.sum_eq_zero
    intro j _
    rw [blockMatrix_apply_ne d M a b (Ne.symm hb), zero_mul]

theorem blockMatrix_bound (M : ∀ a, Matrix (Fin (d a)) (Fin (d a)) ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hM : ∀ a x, ‖(M a).mulVec x‖ ≤ B * ‖x‖) (x : Fin (∑ a, d a) → ℂ) :
    ‖(blockMatrix d M).mulVec x‖ ≤ B * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (norm_nonneg x))).mpr
  intro j
  obtain ⟨⟨a,i⟩,rfl⟩ := (columns d).surjective j
  rw [blockMatrix_mulVec]
  exact (norm_le_pi_norm _ i).trans ((hM a _).trans
    (mul_le_mul_of_nonneg_left (pi_norm_comp_le x (fun j => columns d ⟨a,j⟩)) hB))

theorem coefficientOnRay_blockMatrix
    (A : ∀ a, Matrix (Fin (d a)) (Fin (d a)) (RatFunc ℂ)) (θ r : ℝ) :
    coefficientOnRay (blockMatrix d A) θ r = blockMatrix d (fun a => coefficientOnRay (A a) θ r) := by
  ext i j
  obtain ⟨⟨a,i⟩,rfl⟩ := (columns d).surjective i
  obtain ⟨⟨b,j⟩,rfl⟩ := (columns d).surjective j
  by_cases hab : a=b
  · subst b
    simp only [coefficientOnRay, blockMatrix_apply_same]
  · simp only [coefficientOnRay, blockMatrix_apply_ne d _ a b hab, RatFunc.eval_zero, mul_zero]

theorem blockMatrix_hasDerivAt
    (M : ∀ a, ℝ → Matrix (Fin (d a)) (Fin (d a)) ℂ)
    (M' : ∀ a, Matrix (Fin (d a)) (Fin (d a)) ℂ) (r : ℝ)
    (hM : ∀ a i j, HasDerivAt (fun t => M a t i j) (M' a i j) r)
    (i j : Fin (∑ a, d a)) :
    HasDerivAt (fun t => blockMatrix d (fun a => M a t) i j) (blockMatrix d M' i j) r := by
  obtain ⟨⟨a,i⟩,rfl⟩ := (columns d).surjective i
  obtain ⟨⟨b,j⟩,rfl⟩ := (columns d).surjective j
  by_cases hab : a=b
  · subst b
    simpa only [blockMatrix_apply_same] using hM a i j
  · simpa only [blockMatrix_apply_ne d _ a b hab] using hasDerivAt_const r (0 : ℂ)

/-- Assemble actual witnesses from finitely many blocks on one common tail.
The operator norm estimate uses restrictions of the same infinity-norm vector. -/
theorem assemble_rayGauge
    (A : ∀ a, Matrix (Fin (d a)) (Fin (d a)) (RatFunc ℂ)) (θ : ℝ)
    (q : ∀ a, Fin (d a) → ℝ → ℂ) (W : ∀ a, RayGaugeWitness (A a) θ (q a)) :
    Nonempty (RayGaugeWitness (blockMatrix d A) θ
      (fun i => q ((columns d).symm i).1 ((columns d).symm i).2)) := by
  let R : ℝ := 1 + ∑ a, (W a).R
  let C : ℝ := 1 + ∑ a, (W a).C
  let K : ℝ := ∑ a, (W a).K
  have hR : 1 ≤ R := by
    dsimp [R]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun a _ => (W a).R_pos.le))
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun a _ => (W a).C_pos.le))
  have hK : 0 ≤ K := Finset.sum_nonneg (fun a _ => (W a).K_nonneg)
  have hWR (a : Fin s) : (W a).R ≤ R := by
    have hh := Finset.single_le_sum (fun b _ => (W b).R_pos.le) (Finset.mem_univ a)
    dsimp [R]
    linarith
  have hWC (a : Fin s) : (W a).C ≤ C := by
    have hh := Finset.single_le_sum (fun b _ => (W b).C_pos.le) (Finset.mem_univ a)
    dsimp [C]
    linarith
  have hWK (a : Fin s) : (W a).K ≤ K :=
    Finset.single_le_sum (fun b _ => (W b).K_nonneg) (Finset.mem_univ a)
  have hbound (r : ℝ) (hr : R < r) (a : Fin s) :
      (W a).C * r ^ (W a).K ≤ C * r ^ K := by
    apply mul_le_mul (hWC a)
      (Real.rpow_le_rpow_of_exponent_le (hR.trans hr.le) (hWK a))
      (Real.rpow_nonneg (zero_le_one.trans (hR.trans hr.le)) _) hC.le
  refine ⟨{
    T := fun r => blockMatrix d (fun a => (W a).T r)
    S := fun r => blockMatrix d (fun a => (W a).S r)
    T' := fun r => blockMatrix d (fun a => (W a).T' r)
    R := R, C := C, K := K
    R_pos := zero_lt_one.trans_le hR, C_pos := hC, K_nonneg := hK
    pole_free := ?_
    T_derivative := ?_
    inverse_left := ?_
    inverse_right := ?_
    T_bound := ?_
    S_bound := ?_
    gauge_identity := ?_ }⟩
  · intro r hr i j
    obtain ⟨⟨a,i⟩,rfl⟩ := (columns d).surjective i
    obtain ⟨⟨b,j⟩,rfl⟩ := (columns d).surjective j
    by_cases hab : a=b
    · subst b
      rw [blockMatrix_apply_same]
      exact (W a).pole_free r ((hWR a).trans_lt hr) i j
    · rw [blockMatrix_apply_ne d A a b hab]
      simp [RatFunc.denom_zero]
  · intro r hr i j
    exact blockMatrix_hasDerivAt d (fun a => (W a).T) (fun a => (W a).T' r) r
      (fun a => (W a).T_derivative r ((hWR a).trans_lt hr)) i j
  · intro r hr
    rw [← blockMatrix_mul]
    have he : (fun a => (W a).S r * (W a).T r) = (fun a => (1 : Matrix (Fin (d a)) (Fin (d a)) ℂ)) := by
      funext a
      exact (W a).inverse_left r ((hWR a).trans_lt hr)
    rw [he, blockMatrix_one]
  · intro r hr
    rw [← blockMatrix_mul]
    have he : (fun a => (W a).T r * (W a).S r) = (fun a => (1 : Matrix (Fin (d a)) (Fin (d a)) ℂ)) := by
      funext a
      exact (W a).inverse_right r ((hWR a).trans_lt hr)
    rw [he, blockMatrix_one]
  · intro r hr x
    exact blockMatrix_bound d _ _
      (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans (hR.trans hr.le)) _))
      (fun a x => ((W a).T_bound r ((hWR a).trans_lt hr) x).trans
        (mul_le_mul_of_nonneg_right (hbound r hr a) (norm_nonneg x))) x
  · intro r hr x
    exact blockMatrix_bound d _ _
      (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans (hR.trans hr.le)) _))
      (fun a x => ((W a).S_bound r ((hWR a).trans_lt hr) x).trans
        (mul_le_mul_of_nonneg_right (hbound r hr a) (norm_nonneg x))) x
  · intro r hr
    rw [coefficientOnRay_blockMatrix, ← blockMatrix_mul, ← blockMatrix_mul,
      ← blockMatrix_mul, ← blockMatrix_sub]
    have hh : (fun a => (W a).S r * coefficientOnRay (A a) θ r * (W a).T r -
        (W a).S r * (W a).T' r) = (fun a => Matrix.diagonal (fun i => deriv (q a i) r)) := by
      funext a
      exact (W a).gauge_identity r ((hWR a).trans_lt hr)
    rw [hh, blockMatrix_diagonal]

/-- Different child denominators are converted to one fixed parent family.
Both the family and the product denominator are independent of the angle. -/
theorem block_family_assembly
    (A : ∀ a, Matrix (Fin (d a)) (Fin (d a)) (RatFunc ℂ))
    (p : Fin s → ℕ) (hp : ∀ a, 0 < p a)
    (F : ∀ a, Fin (d a) → Polynomial ℂ)
    (h : ∀ θ a, Nonempty (RayGaugeWitness (A a) θ
      (fun i => phaseOnRay (p a) (F a i) θ ⟨0,hp a⟩))) :
    ∀ θ : ℝ, Nonempty (RayGaugeWitness (blockMatrix d A) θ
      (fun i => phaseOnRay (commonDenominator p)
        (commonFamily p F ((columns d).symm i)) θ ⟨0,commonDenominator_pos p hp⟩)) := by
  intro θ
  let W := fun a => Classical.choice (h θ a)
  obtain ⟨V⟩ := assemble_rayGauge d A θ
    (fun a i => phaseOnRay (p a) (F a i) θ ⟨0,hp a⟩) W
  refine ⟨{ V with gauge_identity := ?_ }⟩
  intro r hr
  rw [V.gauge_identity r hr]
  congr 1
  funext i
  apply Eq.symm
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds (V.R_pos.trans hr)] with t ht
  exact phaseOnRay_commonFamily p hp F ((columns d).symm i) θ ht.le

end WasowPhaseFamilyBlocks
#print axioms WasowPhaseFamilyBlocks.blockMatrix_apply_same
#print axioms WasowPhaseFamilyBlocks.blockMatrix_apply_ne
#print axioms WasowPhaseFamilyBlocks.blockMatrix_mul
#print axioms WasowPhaseFamilyBlocks.blockMatrix_sub
#print axioms WasowPhaseFamilyBlocks.blockMatrix_one
#print axioms WasowPhaseFamilyBlocks.blockMatrix_diagonal
#print axioms WasowPhaseFamilyBlocks.blockMatrix_mulVec
#print axioms WasowPhaseFamilyBlocks.blockMatrix_bound
#print axioms WasowPhaseFamilyBlocks.coefficientOnRay_blockMatrix
#print axioms WasowPhaseFamilyBlocks.blockMatrix_hasDerivAt

#print axioms WasowPhaseFamilyBlocks.assemble_rayGauge
#print axioms WasowPhaseFamilyBlocks.block_family_assembly
