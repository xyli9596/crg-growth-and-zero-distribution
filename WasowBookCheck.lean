import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
A local check of the literal, unnormalized uniqueness assertion in Wasow's
Lemma 19.1.  For h = 1 and k = 2 there are no first h - 1 rows to constrain.
The last row of H X - X K is not unique as X varies.  This counterexample does
not refute solvability, a suitably normalized statement, or Theorem 19.1.
-/
set_option autoImplicit false
noncomputable section

namespace WasowBookCheck

def Hshift : Matrix (Fin 1) (Fin 1) ℂ := 0
def Kshift : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
def Xzero : Matrix (Fin 1) (Fin 2) ℂ := !![0, 0]
def Xone : Matrix (Fin 1) (Fin 2) ℂ := !![1, 0]
def Mzero : Matrix (Fin 1) (Fin 2) ℂ := !![0, 0]
def Mone : Matrix (Fin 1) (Fin 2) ℂ := !![0, -1]

theorem zero_solution : Hshift * Xzero - Xzero * Kshift = Mzero := by
  ext i j
  fin_cases i
  fin_cases j <;>
    norm_num [Hshift, Kshift, Xzero, Mzero, Matrix.mul_apply, Fin.sum_univ_two]

theorem nonzero_solution : Hshift * Xone - Xone * Kshift = Mone := by
  ext i j
  fin_cases i
  fin_cases j <;>
    norm_num [Hshift, Kshift, Xone, Mone, Matrix.mul_apply, Fin.sum_univ_two]

theorem output_rows_distinct : Mzero ≠ Mone := by
  intro h
  have hh := congrFun (congrFun h 0) 1
  norm_num [Mzero, Mone] at hh

/-- With one row, the missing first-row constraints are vacuous.  The literal
claim that the output last row is unique is already false in these dimensions. -/
theorem not_existsUnique_unnormalized_last_row :
    ¬ ∃! M : Matrix (Fin 1) (Fin 2) ℂ,
      ∃ X : Matrix (Fin 1) (Fin 2) ℂ,
        (0 : Matrix (Fin 1) (Fin 1) ℂ) * X - X * Kshift = M := by
  rintro ⟨M, _, huniq⟩
  have hzero := huniq Mzero ⟨Xzero, zero_solution⟩
  have hone := huniq Mone ⟨Xone, nonzero_solution⟩
  exact output_rows_distinct (hzero.trans hone.symm)

end WasowBookCheck

#print axioms WasowBookCheck.zero_solution
#print axioms WasowBookCheck.nonzero_solution
#print axioms WasowBookCheck.output_rows_distinct
#print axioms WasowBookCheck.not_existsUnique_unnormalized_last_row
