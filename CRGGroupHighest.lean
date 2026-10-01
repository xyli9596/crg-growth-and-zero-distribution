import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Highest nonzero differential order of a polynomial coefficient group, and
its exact rational scalar equation. This is a finite algebraic construction. -/
noncomputable section
open Polynomial Filter
open scoped BigOperators Topology
namespace CRGGroupHighest

structure Highest {n : ℕ} (b : Fin (n+1) → Polynomial ℂ) where
  index : Fin (n+1)
  nonzero : b index ≠ 0
  above_zero : ∀ j : Fin (n+1), index.val < j.val → b j = 0

theorem exists_highest {n : ℕ} (b : Fin (n+1) → Polynomial ℂ)
    (hb : ∃ j, b j ≠ 0) : Nonempty (Highest b) := by
  classical
  let s := Finset.univ.filter (fun j => b j ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨j,hj⟩ := hb
    exact ⟨j, by simp [s,hj]⟩
  let m := s.max' hs
  have hm : m ∈ s := Finset.max'_mem s hs
  refine ⟨⟨m, (Finset.mem_filter.mp hm).2, fun j hj => ?_⟩⟩
  by_contra hbj
  have hjm : j ≤ m := Finset.le_max' s j (by simp [s,hbj])
  exact (not_le.mpr hj) hjm

def lowerIndex {n : ℕ} (m : Fin (n+1)) (j : Fin m.val) : Fin (n+1) :=
  ⟨j.val, j.isLt.trans m.isLt⟩

/-- Terms above the chosen highest order disappear; all lower terms retain
their exact original derivative indices. -/
theorem sum_truncate {n : ℕ} (v : Fin (n+1) → ℂ) (m : Fin (n+1))
    (hv : ∀ j, m.val < j.val → v j = 0) :
    (∑ j, v j) = v m + ∑ j : Fin m.val, v (lowerIndex m j) := by
  classical
  let e : Fin (m.val+1) → Fin (n+1) := Fin.castLE (Nat.succ_le_of_lt m.isLt)
  have hinj : Function.Injective e := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin (n+1) => x.val) hij)
  have hsum : (∑ j : Fin (n+1), v j) = ∑ i : Fin (m.val+1), v (e i) := by
    rw [← Finset.sum_image (fun i _ j _ hij => hinj hij)]
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro j _ hj
    apply hv j
    by_contra hle
    have hjm : j.val < m.val+1 := by omega
    apply hj
    exact Finset.mem_image.mpr ⟨⟨j.val,hjm⟩,Finset.mem_univ _,Fin.ext rfl⟩
  rw [hsum, Fin.sum_univ_castSucc]
  have he (j : Fin m.val) : e j.castSucc = lowerIndex m j := Fin.ext rfl
  have hel : e (Fin.last m.val) = m := Fin.ext rfl
  simp only [he,hel,add_comm]

theorem polynomial_group_truncate {n : ℕ} {b : Fin (n+1) → Polynomial ℂ}
    (H : Highest b) (v : Fin (n+1) → ℂ) (z : ℂ) :
    (∑ j, (b j).eval z*v j) =
      (b H.index).eval z*v H.index +
      ∑ j : Fin H.index.val, (b (lowerIndex H.index j)).eval z*v (lowerIndex H.index j) := by
  apply sum_truncate _ H.index
  intro j hj
  simp [H.above_zero j hj]

/-- Rational evaluation of a polynomial quotient is valid exactly where the
original polynomial denominator is nonzero; reduction of fractions causes no
hidden pole convention. -/
theorem eval_polynomial_quotient (p q : Polynomial ℂ) {z : ℂ} (hq : q.eval z ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z ((p : RatFunc ℂ)/(q : RatFunc ℂ)) = p.eval z/q.eval z := by
  have hq0 : q ≠ 0 := by intro h; apply hq; simp [h]
  have hd : (((p : RatFunc ℂ)/(q : RatFunc ℂ)).denom).eval z ≠ 0 := by
    intro hz
    apply hq
    exact Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℂ) z
      (RatFunc.denom_div_dvd p q) hz
  have he := RatFunc.eval_mul (RingHom.id ℂ) z (x := (p:RatFunc ℂ)/(q:RatFunc ℂ))
    (y := (q:RatFunc ℂ)) (by simpa using hd) (by simp)
  have hqR : (q : RatFunc ℂ) ≠ 0 := RatFunc.algebraMap_ne_zero hq0
  rw [div_mul_cancel₀ _ hqR] at he
  simp only [RatFunc.coePolynomial_eq_algebraMap, RatFunc.eval_algebraMap,
    Algebra.algebraMap_self, RingHom.id_apply, eval₂_id] at he
  exact (eq_div_iff hq).mpr he.symm

def rationalCoeff {n : ℕ} {b : Fin (n+1) → Polynomial ℂ}
    (H : Highest b) (j : Fin H.index.val) : RatFunc ℂ :=
  ((-b (lowerIndex H.index j) : Polynomial ℂ) : RatFunc ℂ)/(b H.index : RatFunc ℂ)

theorem rationalCoeff_eval {n : ℕ} {b : Fin (n+1) → Polynomial ℂ}
    (H : Highest b) (j : Fin H.index.val) {z : ℂ} (hz : (b H.index).eval z ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z (rationalCoeff H j) =
      -(b (lowerIndex H.index j)).eval z/(b H.index).eval z := by
  simpa only [rationalCoeff, eval_neg] using
    eval_polynomial_quotient (-b (lowerIndex H.index j)) (b H.index) hz

/-- Exact reduction at one evaluation point to a monic rational equation with
forcing epsilon*f. No analytic estimate is used in this algebraic identity. -/
theorem reduced_equation {n : ℕ} {b : Fin (n+1) → Polynomial ℂ}
    (H : Highest b) (v : Fin (n+1) → ℂ) (z ε F : ℂ)
    (hz : (b H.index).eval z ≠ 0)
    (heq : ∑ j, (b j).eval z*v j = ε*(b H.index).eval z*F) :
    v H.index = (∑ j : Fin H.index.val,
      RatFunc.eval (RingHom.id ℂ) z (rationalCoeff H j)*v (lowerIndex H.index j)) + ε*F := by
  rw [polynomial_group_truncate H v z] at heq
  simp_rw [rationalCoeff_eval H _ hz]
  have hs : (∑ j : Fin H.index.val,
      -(b (lowerIndex H.index j)).eval z/(b H.index).eval z*v (lowerIndex H.index j)) =
      -(∑ j : Fin H.index.val, (b (lowerIndex H.index j)).eval z*v (lowerIndex H.index j)) /
        (b H.index).eval z := by
    simp_rw [div_mul_eq_mul_div, neg_mul]
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
  rw [hs]
  apply (mul_left_cancel₀ hz)
  field_simp
  linear_combination heq

/-- Instantiation for actual iterated derivatives. The rational coefficients
are constructed once from the polynomial group and are independent of rays. -/
theorem reduced_differential_equation {n : ℕ} {b : Fin (n+1) → Polynomial ℂ}
    (H : Highest b) (f : ℂ → ℂ) (z ε : ℂ)
    (hz : (b H.index).eval z ≠ 0)
    (heq : ∑ j, (b j).eval z*iteratedDeriv j.val f z = ε*(b H.index).eval z*f z) :
    iteratedDeriv H.index.val f z =
      (∑ j : Fin H.index.val, RatFunc.eval (RingHom.id ℂ) z (rationalCoeff H j)*iteratedDeriv j.val f z) + ε*f z :=
  reduced_equation H (fun j => iteratedDeriv j.val f z) z ε (f z) hz heq

/-- The quotient form is the one produced by the normalized dominant-group
residual identity. -/
theorem reduced_differential_equation_of_quotient {n : ℕ} {b : Fin (n+1) → Polynomial ℂ}
    (H : Highest b) (f : ℂ → ℂ) (z ε : ℂ)
    (hz : (b H.index).eval z ≠ 0)
    (heq : (∑ j, (b j).eval z*iteratedDeriv j.val f z) / (b H.index).eval z = ε*f z) :
    iteratedDeriv H.index.val f z =
      (∑ j : Fin H.index.val, RatFunc.eval (RingHom.id ℂ) z (rationalCoeff H j)*iteratedDeriv j.val f z) + ε*f z := by
  apply reduced_differential_equation H f z ε hz
  have hh := (div_eq_iff hz).mp heq
  linear_combination hh

/-- Order zero is an exact multiplication operator, before any comparison with
the small residual. Only nonvanishing of the polynomial divisor is needed. -/
theorem quotient_eq_function_of_order_zero {n : ℕ} {b : Fin (n+1) → Polynomial ℂ}
    (H : Highest b) (hm : H.index.val = 0) (f : ℂ → ℂ) {z : ℂ}
    (hb : (b H.index).eval z ≠ 0) :
    (∑ j, (b j).eval z*iteratedDeriv j.val f z) / (b H.index).eval z = f z := by
  rw [polynomial_group_truncate H (fun j => iteratedDeriv j.val f z) z]
  have hs : (∑ j : Fin H.index.val,
      (b (lowerIndex H.index j)).eval z*iteratedDeriv (lowerIndex H.index j).val f z) = 0 := by
    have : IsEmpty (Fin H.index.val) := by rw [hm]; infer_instance
    exact Finset.sum_eq_zero (fun j _ => isEmptyElim j)
  rw [hs, add_zero, hm, iteratedDeriv_zero, mul_div_cancel_left₀ _ hb]

def positiveCoeff {n : ℕ} {b : Fin (n+1) → Polynomial ℂ}
    (H : Highest b) {m : ℕ} (hm : H.index.val = m+1) (j : Fin (m+1)) : RatFunc ℂ :=
  rationalCoeff H (Fin.cast hm.symm j)

/-- Transport to the successor-indexed scalar ODE interface, with all Fin casts
handled internally. -/
theorem positive_reduced_differential_equation {n : ℕ} {b : Fin (n+1) → Polynomial ℂ}
    (H : Highest b) {m : ℕ} (hm : H.index.val = m+1) (f : ℂ → ℂ) (z ε : ℂ)
    (hz : (b H.index).eval z ≠ 0)
    (heq : (∑ j, (b j).eval z*iteratedDeriv j.val f z) / (b H.index).eval z = ε*f z) :
    iteratedDeriv (m+1) f z =
      (∑ j : Fin (m+1), RatFunc.eval (RingHom.id ℂ) z (positiveCoeff H hm j)*iteratedDeriv j.val f z) + ε*f z := by
  have hh := reduced_differential_equation_of_quotient H f z ε hz heq
  have hs : (∑ j : Fin H.index.val,
      RatFunc.eval (RingHom.id ℂ) z (rationalCoeff H j)*iteratedDeriv j.val f z) =
      ∑ j : Fin (m+1), RatFunc.eval (RingHom.id ℂ) z (positiveCoeff H hm j)*iteratedDeriv j.val f z := by
    exact (Equiv.sum_comp (finCongr hm).symm
      (fun j => RatFunc.eval (RingHom.id ℂ) z (rationalCoeff H j)*iteratedDeriv j.val f z)).symm
  rw [hs, hm] at hh
  exact hh

/-- A nonunit normalized residual excludes the zeroth-order stopping branch. -/
theorem order_pos_of_residual_ne_one {n : ℕ} {b : Fin (n+1) → Polynomial ℂ}
    (H : Highest b) (f : ℂ → ℂ) (z ε : ℂ)
    (hb : (b H.index).eval z ≠ 0) (hf : f z ≠ 0) (hε : ε ≠ 1)
    (heq : (∑ j, (b j).eval z*iteratedDeriv j.val f z) / (b H.index).eval z = ε*f z) :
    0 < H.index.val := by
  apply Nat.pos_of_ne_zero
  intro hm
  rw [quotient_eq_function_of_order_zero H hm f hb] at heq
  apply hε
  apply (mul_right_cancel₀ hf)
  simpa using heq.symm

/-- A highest differential order of zero makes the normalized group residual
identically one wherever the leading coefficient and f are nonzero. -/
theorem normalized_residual_eq_one_of_order_zero {n : ℕ} {b : Fin (n+1) → Polynomial ℂ}
    (H : Highest b) (hm : H.index.val = 0) (f : ℂ → ℂ) {z : ℂ}
    (hb : (b H.index).eval z ≠ 0) (hf : f z ≠ 0) :
    (∑ j, (b j).eval z*iteratedDeriv j.val f z) / ((b H.index).eval z*f z) = 1 := by
  rw [polynomial_group_truncate H (fun j => iteratedDeriv j.val f z) z]
  have hs : (∑ j : Fin H.index.val,
      (b (lowerIndex H.index j)).eval z*iteratedDeriv (lowerIndex H.index j).val f z) = 0 := by
    have : IsEmpty (Fin H.index.val) := by rw [hm]; infer_instance
    exact Finset.sum_eq_zero (fun j _ => isEmptyElim j)
  rw [hs, add_zero, hm, iteratedDeriv_zero, div_self (mul_ne_zero hb hf)]

#print axioms positive_reduced_differential_equation
#print axioms order_pos_of_residual_ne_one
#print axioms reduced_differential_equation_of_quotient
#print axioms quotient_eq_function_of_order_zero
#print axioms exists_highest
#print axioms sum_truncate
#print axioms polynomial_group_truncate
#print axioms eval_polynomial_quotient
#print axioms rationalCoeff_eval
#print axioms reduced_equation
#print axioms reduced_differential_equation
#print axioms normalized_residual_eq_one_of_order_zero
end CRGGroupHighest
