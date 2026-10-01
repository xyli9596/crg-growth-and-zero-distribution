import WasowPencilDescent
import WasowSingleEigenBlocks
import Mathlib.Algebra.Polynomial.RingDivision

/-! Constant similarity and scalar translation preserve the actual polynomial
pencil degree invariant. These are algebraic invariances, not descent hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace WasowPencilSimilarity
open WasowPencilReduction WasowReductionDescent WasowPencilDescent

variable {ι : Type*} [Fintype ι]

theorem minorGCD_map_associated (T : Matrix ι ι ℂ[X]) (e : ℂ[X] ≃+* ℂ[X]) (k : ℕ) :
    Associated (e (minorGCD T k)) (minorGCD (T.map e) k) := by
  have hmap (A : Matrix ι ι ℂ[X]) (f : ℂ[X] ≃+* ℂ[X]) (r c : Fin k → ι) :
      ((A.map f).submatrix r c).det = f ((A.submatrix r c).det) := by
    exact (RingHom.map_det f.toRingHom _).symm
  apply associated_of_dvd_dvd
  · rw [dvd_minorGCD_iff]
    intro r c
    rw [hmap T e r c]
    obtain ⟨q, hq⟩ := minorGCD_dvd_minor T k r c
    refine ⟨e q, ?_⟩
    rw [← map_mul, hq]
  · have hd : e.symm (minorGCD (T.map e) k) ∣ minorGCD T k := by
      rw [dvd_minorGCD_iff]
      intro r c
      obtain ⟨q, hq⟩ := minorGCD_dvd_minor (T.map e) k r c
      rw [hmap T e r c] at hq
      refine ⟨e.symm q, ?_⟩
      simpa using congrArg e.symm hq
    obtain ⟨q, hq⟩ := hd
    refine ⟨e q, ?_⟩
    simpa using congrArg e hq

theorem natDegree_translate (p : ℂ[X]) (α : ℂ) :
    (Polynomial.algEquivAevalXAddC α p).natDegree = p.natDegree := by
  simp [Polynomial.algEquivAevalXAddC_apply, ← Polynomial.comp_eq_aeval,
    Polynomial.natDegree_comp]

theorem minorGCD_translate_degree (T : Matrix ι ι ℂ[X]) (α : ℂ) (k : ℕ) :
    (minorGCD (T.map (Polynomial.algEquivAevalXAddC α)) k).natDegree =
      (minorGCD T k).natDegree := by
  have hh := Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_eq_degree_of_associated
      (minorGCD_map_associated T (Polynomial.algEquivAevalXAddC α).toRingEquiv k))
  exact hh.symm.trans (natDegree_translate _ α)

theorem degreeMass_translate (T : Matrix ι ι ℂ[X]) (α : ℂ) :
    WasowPencilDescent.degreeMass (T.map (Polynomial.algEquivAevalXAddC α)) =
      WasowPencilDescent.degreeMass T := by
  unfold WasowPencilDescent.degreeMass
  simp_rw [minorGCD_translate_degree]

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {h : σ → ℕ}

omit [Fintype σ] in
theorem pencil_sub_scalar (C : Matrix (OldIndex h) (OldIndex h) ℂ) (α : ℂ) :
    pencil (C - α • 1) = (pencil C).map (Polynomial.algEquivAevalXAddC α) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j <;>
    simp [pencil, hij, Polynomial.algEquivAevalXAddC_apply,
      smul_eq_mul, map_sub]
    ; ring

theorem degreeMass_sub_scalar (C : Matrix (OldIndex h) (OldIndex h) ℂ) (α : ℂ) :
    WasowPencilDescent.degreeMass (pencil (C - α • 1)) =
      WasowPencilDescent.degreeMass (pencil C) := by
  rw [pencil_sub_scalar, degreeMass_translate]

theorem pencil_similarity (C L R : Matrix (OldIndex h) (OldIndex h) ℂ)
    (hLR : L * R = 1) :
    pencil (L * C * R) = L.map Polynomial.C * pencil C * R.map Polynomial.C := by
  unfold pencil
  rw [Matrix.map_mul, Matrix.map_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [← Matrix.map_mul (L := L) (M := R), hLR]
  simp

theorem degreeMass_similarity (C L R : Matrix (OldIndex h) (OldIndex h) ℂ)
    (hLR : L * R = 1) (hRL : R * L = 1) :
    WasowPencilDescent.degreeMass (pencil (L * C * R)) =
      WasowPencilDescent.degreeMass (pencil C) := by
  rw [pencil_similarity C L R hLR]
  have hm : R.map Polynomial.C * L.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hRL]
    simp
  unfold WasowPencilDescent.degreeMass
  simp_rw [WasowMinorEquivalence.minorGCD_equivalent
    (L.map Polynomial.C) (R.map Polynomial.C) (pencil C)
    (R.map Polynomial.C) (L.map Polynomial.C) hm hm]

/-- The full single-eigenvalue normalization has weak descent for the original
constant matrix, including the scalar translation of its pencil. -/
theorem single_eigen_pencil_mass_le {s : ℕ} {h : Fin s → ℕ}
    (C : Matrix (OldIndex h) (OldIndex h) ℂ) (α : ℂ)
    (hrows : LastRowForm h C) (hlower : WasowSingleEigenBlocks.LowerBlocks C)
    (hN : IsNilpotent (C - α • 1)) :
    WasowPencilDescent.degreeMass (pencil C) ≤
      WasowPencilDescent.degreeMass (pencil (WasowMultiShiftReduction.jordanShift h)) := by
  obtain ⟨L, R, T, hLR, hRL, hT, hdiag, hoff, hlow, _⟩ :=
    WasowSingleEigenBlocks.exists_shift_diagonal_similarity C α hrows hlower hN
  have he : WasowPencilDescent.degreeMass (pencil T) =
      WasowPencilDescent.degreeMass (pencil C) := by
    rw [hT, degreeMass_similarity _ _ _ hLR hRL, degreeMass_sub_scalar]
  rw [← he]
  apply pencil_degreeMass_le (WasowSingleEigenBlocks.lastRowForm_of_blocks T hdiag hoff)
  · intro a b hab i j
    exact hlow (show OrderDual.toDual b < OrderDual.toDual a from hab)
  · intro a i j
    exact congrArg (fun A => A i j) (hdiag a)

/-- A nonzero actual off-diagonal block makes the original pencil invariant
strictly smaller after a single-eigenvalue normalized shearing step. -/
theorem single_eigen_pencil_mass_strict {s : ℕ} {h : Fin s → ℕ}
    (C : Matrix (OldIndex h) (OldIndex h) ℂ) (α : ℂ) (hh : Monotone h)
    (hrows : LastRowForm h C) (hlower : WasowSingleEigenBlocks.LowerBlocks C)
    (hN : IsNilpotent (C - α • 1))
    (hn : ∃ a b, a ≠ b ∧ WasowMultiShiftReduction.block C a b ≠ 0) :
    WasowPencilDescent.degreeMass (pencil C) <
      WasowPencilDescent.degreeMass (pencil (WasowMultiShiftReduction.jordanShift h)) := by
  obtain ⟨L, R, T, hLR, hRL, hT, hdiag, hoff, hlow, hniff⟩ :=
    WasowSingleEigenBlocks.exists_shift_diagonal_similarity C α hrows hlower hN
  have he : WasowPencilDescent.degreeMass (pencil T) =
      WasowPencilDescent.degreeMass (pencil C) := by
    rw [hT, degreeMass_similarity _ _ _ hLR hRL, degreeMass_sub_scalar]
  rw [← he]
  apply pencil_degreeMass_strict_drop hh
    (WasowSingleEigenBlocks.lastRowForm_of_blocks T hdiag hoff)
  · intro a b hab i j
    exact hlow (show OrderDual.toDual b < OrderDual.toDual a from hab)
  · intro a i j
    exact congrArg (fun A => A i j) (hdiag a)
  · obtain ⟨a, b, hab, hn⟩ := hn
    have htn := (hniff a b hab).mpr hn
    have he : ∃ i j, WasowMultiShiftReduction.block T a b i j ≠ 0 := by
      by_contra! hz
      apply htn
      apply Matrix.ext
      exact hz
    obtain ⟨i, j, hij⟩ := he
    have hi : i = Fin.last (h a) := by
      apply Fin.ext
      change i.val = h a
      by_contra hi
      have hil : i.val < h a := by omega
      exact hij (hoff a b hab i j hil)
    subst i
    exact ⟨a, b, hab, j, hij⟩

#print axioms minorGCD_map_associated
#print axioms natDegree_translate
#print axioms minorGCD_translate_degree
#print axioms degreeMass_translate
#print axioms pencil_sub_scalar
#print axioms degreeMass_sub_scalar
#print axioms pencil_similarity
#print axioms degreeMass_similarity
#print axioms single_eigen_pencil_mass_le
#print axioms single_eigen_pencil_mass_strict
end WasowPencilSimilarity
