import CRGExponentialCoefficients

/-! Collection of the actual monic equation into polynomial coefficient groups.
All derivative orders, including the monic top derivative, are retained. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators
namespace CRGCollectedEquation
open CRGExponentialCoefficients

abbrev TermIndex {n : ℕ} (N : Fin n→ℕ) := Unit ⊕ (Σk:Fin n,Fin (N k))

def termOrder {n : ℕ} {N : Fin n→ℕ} : TermIndex N→Fin (n+1)
  | .inl _ => Fin.last n
  | .inr ⟨k,_⟩ => k.castSucc

def termPolynomial {n : ℕ} {N : Fin n→ℕ}
    (P : (k:Fin n)→Fin (N k)→Polynomial ℂ) : TermIndex N→Polynomial ℂ
  | .inl _ => 1
  | .inr ⟨k,i⟩ => P k i

def termExponent {n : ℕ} {N : Fin n→ℕ}
    (Q : (k:Fin n)→Fin (N k)→Polynomial ℂ) : TermIndex N→Polynomial ℂ
  | .inl _ => 0
  | .inr ⟨k,i⟩ => Q k i

theorem raw_equation {n : ℕ} (a : Fin n→ℂ→ℂ) (f : ℂ→ℂ)
    (ha : ∀k,IsExponentialPolynomial (a k)) (heq : SolvesMonicEquation n a f) :
    ∃ N : Fin n→ℕ, ∃ P Q : (k:Fin n)→Fin (N k)→Polynomial ℂ,
      ∀z : ℂ, ∑i : TermIndex N,
        (termPolynomial P i).eval z*Complex.exp ((termExponent Q i).eval z)*
          iteratedDeriv (termOrder i).val f z = 0 := by
  classical
  choose N P Q hrep using ha
  refine ⟨N,P,Q,?_⟩
  intro z
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, Finset.univ_unique,
    Finset.sum_singleton, termPolynomial, termExponent, termOrder, eval_one, eval_zero,
    Complex.exp_zero, one_mul, Fin.val_last, Fin.val_castSucc]
  have hh := heq z
  simp_rw [hrep, Finset.sum_mul] at hh
  exact hh

def coefficientGroup {ι : Type*} [Fintype ι] {n : ℕ}
    (P Q : ι→Polynomial ℂ) (k : ι→Fin (n+1))
    (q : Polynomial ℂ) (j : Fin (n+1)) : Polynomial ℂ :=
  ∑i, if normalizedExponent (Q i)=q ∧ k i=j then
    normalizedMultiplier (P i) (Q i) else 0

theorem coefficient_group_sum {ι : Type*} [Fintype ι] {n : ℕ}
    (P Q : ι→Polynomial ℂ) (k : ι→Fin (n+1))
    (q : Polynomial ℂ) (v : Fin (n+1)→ℂ) (z : ℂ) :
    (∑j, (coefficientGroup P Q k q j).eval z*v j) =
      ∑i, if normalizedExponent (Q i)=q then
        (normalizedMultiplier (P i) (Q i)).eval z*v (k i) else 0 := by
  classical
  simp only [coefficientGroup, eval_finsetSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : normalizedExponent (Q i)=q
  · simp [h, apply_ite, eq_comm]
  · simp [h]

theorem collected_identity {ι : Type*} [Fintype ι] {n : ℕ}
    (P Q : ι→Polynomial ℂ) (k : ι→Fin (n+1))
    (v : Fin (n+1)→ℂ) (z : ℂ) :
    (∑i, (P i).eval z*Complex.exp ((Q i).eval z)*v (k i)) =
      ∑q ∈ Finset.univ.image (fun i => normalizedExponent (Q i)),
        Complex.exp (q.eval z)*(∑j,(coefficientGroup P Q k q j).eval z*v j) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ.image (fun i => normalizedExponent (Q i)))
    (g := fun i => normalizedExponent (Q i))
    (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    (fun i => (P i).eval z*Complex.exp ((Q i).eval z)*v (k i))]
  apply Finset.sum_congr rfl
  intro q _
  rw [coefficient_group_sum, Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : normalizedExponent (Q i)=q
  · simp only [h, if_true]
    rw [normalized_term, h]
    ring
  · simp [h]

theorem coefficientGroup_top {n : ℕ} {N : Fin n→ℕ}
    (P Q : (k:Fin n)→Fin (N k)→Polynomial ℂ) :
    coefficientGroup (termPolynomial P) (termExponent Q) termOrder 0 (Fin.last n)=1 := by
  classical
  simp [coefficientGroup, Fintype.sum_sum_type, termPolynomial,
    termExponent, termOrder, normalizedExponent, normalizedMultiplier]

structure CollectedEquation (n : ℕ) (f : ℂ→ℂ) where
  exponents : Finset (Polynomial ℂ)
  nonempty : exponents.Nonempty
  coeff : Polynomial ℂ→Fin (n+1)→Polynomial ℂ
  normalized : ∀q∈exponents,q.coeff 0=0
  nonzero_group : ∀q∈exponents,∃j,coeff q j≠0
  equation : ∀z : ℂ, ∑q∈exponents,Complex.exp (q.eval z)*
    (∑j,(coeff q j).eval z*iteratedDeriv j.val f z)=0

theorem exists_collected_equation {n : ℕ} (a : Fin n→ℂ→ℂ) (f : ℂ→ℂ)
    (ha : ∀k,IsExponentialPolynomial (a k)) (heq : SolvesMonicEquation n a f) :
    Nonempty (CollectedEquation n f) := by
  classical
  obtain ⟨N,P,Q,hraw⟩ := raw_equation a f ha heq
  let b := coefficientGroup (termPolynomial P) (termExponent Q) termOrder
  let S := Finset.univ.image (fun i : TermIndex N => normalizedExponent (termExponent Q i))
  let T := S.filter (fun q => ∃j,b q j≠0)
  have h0S : 0∈S := by
    apply Finset.mem_image.mpr
    refine ⟨Sum.inl (),Finset.mem_univ _,?_⟩
    simp [termExponent,normalizedExponent]
  have h0T : 0∈T := by
    apply Finset.mem_filter.mpr
    refine ⟨h0S,Fin.last n,?_⟩
    simpa only [b,coefficientGroup_top] using (one_ne_zero : (1:Polynomial ℂ)≠0)
  refine ⟨⟨T,⟨0,h0T⟩,b,?_,?_,?_⟩⟩
  · intro q hq
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
    rw [←hi]
    exact normalizedExponent_zero _
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro z
    have hh := collected_identity (termPolynomial P) (termExponent Q) termOrder
      (fun j => iteratedDeriv j.val f z) z
    have he : (∑q∈S,Complex.exp (q.eval z)*
        (∑j,(b q j).eval z*iteratedDeriv j.val f z))=0 := by
      rw [←hh]
      exact hraw z
    rw [show T=S.filter (fun q => ∃j,b q j≠0) from rfl,Finset.sum_filter]
    convert he using 1
    apply Finset.sum_congr rfl
    intro q _
    split_ifs with h
    · rfl
    · have hz : ∀j,b q j=0 := by simpa using h
      simp [hz]

theorem CollectedEquation.subtype_equation {n : ℕ} {f : ℂ→ℂ}
    (E : CollectedEquation n f) (z : ℂ) :
    (∑q : E.exponents,Complex.exp (q.val.eval z)*
      (∑j,(E.coeff q.val j).eval z*iteratedDeriv j.val f z))=0 := by
  classical
  exact (Finset.sum_coe_sort E.exponents (fun q : Polynomial ℂ =>
    Complex.exp (q.eval z)*(∑j,(E.coeff q j).eval z*iteratedDeriv j.val f z))).trans
      (E.equation z)

#print axioms CollectedEquation.subtype_equation
#print axioms coefficientGroup_top
#print axioms exists_collected_equation
#print axioms raw_equation
#print axioms coefficient_group_sum
#print axioms collected_identity
end CRGCollectedEquation
