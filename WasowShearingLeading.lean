import WasowShearing

/-!
The finite Newton-slope choice for an actual coefficient sequence. The
derivative correction contributes the separate candidate `q+1`; equality
with that candidate is retained as a stopping branch. No nilpotence or
strict descent of the new leading matrix is assumed here.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace WasowShearingLeading

variable {n : ℕ}

def firstOrder (v : ℕ → ℂ) : ℕ := by
  classical
  exact if hv : ∃ k, v k ≠ 0 then Nat.find hv else 0

theorem firstOrder_spec (v : ℕ → ℂ) (hv : ∃ k, v k ≠ 0) :
    v (firstOrder v) ≠ 0 := by
  simpa only [firstOrder, dif_pos hv] using Nat.find_spec hv

theorem firstOrder_le (v : ℕ → ℂ) {k : ℕ} (hk : v k ≠ 0) :
    firstOrder v ≤ k := by
  have hv : ∃ k, v k ≠ 0 := ⟨k,hk⟩
  simpa only [firstOrder, dif_pos hv] using Nat.find_min' hv hk

theorem firstOrder_pos (v : ℕ → ℂ) (hv : ∃ k, v k ≠ 0) (hzero : v 0 = 0) :
    0 < firstOrder v := by
  have hs := firstOrder_spec v hv
  by_contra! h
  have he : firstOrder v = 0 := by omega
  exact hs (he ▸ hzero)

/-- The exponent after multiplying the sheared coefficient by `x^σ`.
An original term `Aₖᵢⱼ x⁻ᵏ` acquires precisely this decay exponent. -/
def weightedDegree (σ : ℚ) (k : ℕ) (i j : Fin n) : ℚ :=
  k + ((j.val : ℚ) - i.val - 1) * σ

/-- A lower-triangular entry with at least one nonzero coefficient. -/
abbrev Feedback (A : ℕ → Matrix (Fin n) (Fin n) ℂ) :=
  {s : Fin n × Fin n // s.2 ≤ s.1 ∧ ∃ k, A k s.1 s.2 ≠ 0}

/-- There is a positive rational slope no larger than `q+1`. Every nonzero
coefficient has nonnegative transformed exponent. Either the derivative
candidate is reached, or a genuine lower-triangular coefficient survives. -/
theorem exists_leading_slope (A : ℕ → Matrix (Fin n) (Fin n) ℂ) (q : ℕ)
    (hzero : ∀ i j, j ≤ i → A 0 i j = 0) :
    ∃ σ : ℚ, 0 < σ ∧ σ ≤ (q+1 : ℕ) ∧
      (∀ k i j, A k i j ≠ 0 → 0 ≤ weightedDegree σ k i j) ∧
      (σ = (q+1 : ℕ) ∨ ∃ k i j, j ≤ i ∧
        A k i j ≠ 0 ∧ weightedDegree σ k i j = 0) := by
  classical
  let α : Option (Feedback A) → ℚ := fun e => match e with
    | none => q+1
    | some s => firstOrder (fun k => A k s.val.1 s.val.2)
  let d : Option (Feedback A) → ℕ := fun e => match e with
    | none => 0
    | some s => s.val.1.val - s.val.2.val
  have hα : ∀ e, 0 < α e := by
    intro e
    cases e with
    | none => dsimp [α]; positivity
    | some s =>
      dsimp [α]
      exact_mod_cast firstOrder_pos (fun k => A k s.val.1 s.val.2)
        s.property.2 (hzero _ _ s.property.1)
  obtain ⟨σ,hσ,hle,e,he⟩ := WasowShearing.exists_rational_slope α d hα
  have hcap : σ ≤ (q+1 : ℕ) := by simpa [α,d] using hle none
  refine ⟨σ,hσ,hcap,?_,?_⟩
  · intro k i j hk
    by_cases hji : j ≤ i
    · let s : Feedback A := ⟨(i,j),hji,⟨k,hk⟩⟩
      have hb := hle (some s)
      have hmin : (firstOrder (fun l => A l i j) : ℚ) ≤ k := by
        exact_mod_cast firstOrder_le (fun l => A l i j) hk
      have hd : ((i.val-j.val : ℕ) : ℚ) = (i.val : ℚ)-j.val :=
        Nat.cast_sub hji
      dsimp [α,d,s] at hb
      unfold weightedDegree
      rw [hd] at hb
      nlinarith
    · have hij : i.val + 1 ≤ j.val := by omega
      have hij' : (i.val : ℚ)+1 ≤ j.val := by exact_mod_cast hij
      unfold weightedDegree
      exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by linarith) hσ.le)
  · cases e with
    | none => exact Or.inl (by simpa [α,d] using he)
    | some s =>
      refine Or.inr ⟨firstOrder (fun k => A k s.val.1 s.val.2),
        s.val.1,s.val.2,s.property.1,
        firstOrder_spec _ s.property.2,?_⟩
      have hd : ((s.val.1.val-s.val.2.val : ℕ) : ℚ) =
          (s.val.1.val : ℚ)-s.val.2.val := Nat.cast_sub s.property.1
      dsimp [α,d] at he
      rw [hd] at he
      unfold weightedDegree
      nlinarith

/-- The genuine zero-weight coefficient, when an integral index exists. -/
def leadingMatrix (A : ℕ → Matrix (Fin n) (Fin n) ℂ) (σ : ℚ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => by
  classical
  exact if hk : ∃ k, weightedDegree σ k i j = 0 then A (Nat.find hk) i j else 0

theorem weightedDegree_injective (σ : ℚ) (i j : Fin n) :
    Function.Injective (fun k => weightedDegree σ k i j) := by
  intro k l hkl
  unfold weightedDegree at hkl
  have h : (k : ℚ) = l := by linarith
  exact_mod_cast h

theorem leadingMatrix_eq_coeff (A : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (σ : ℚ) (k : ℕ) (i j : Fin n) (hk : weightedDegree σ k i j = 0) :
    leadingMatrix A σ i j = A k i j := by
  classical
  have hex : ∃ k, weightedDegree σ k i j = 0 := ⟨k,hk⟩
  have he : Nat.find hex = k := weightedDegree_injective σ i j
    ((Nat.find_spec hex).trans hk.symm)
  simp only [leadingMatrix, dif_pos hex, he]

theorem leadingMatrix_ne_zero_iff (A : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (σ : ℚ) (i j : Fin n) :
    leadingMatrix A σ i j ≠ 0 ↔
      ∃ k, weightedDegree σ k i j = 0 ∧ A k i j ≠ 0 := by
  classical
  constructor
  · intro h
    by_cases hex : ∃ k, weightedDegree σ k i j = 0
    · exact ⟨Nat.find hex,Nat.find_spec hex,by simpa [leadingMatrix,hex] using h⟩
    · simp [leadingMatrix,hex] at h
  · rintro ⟨k,hk,hne⟩
    simpa only [leadingMatrix_eq_coeff A σ k i j hk] using hne

/-- Above the main diagonal the old shift entries are retained exactly. -/
theorem leadingMatrix_above (A : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hshape : ∀ i j, A 0 i j ≠ 0 → j.val = i.val+1)
    {σ : ℚ} (hσ : 0 < σ) (i j : Fin n) (hij : i < j) :
    leadingMatrix A σ i j = A 0 i j := by
  by_cases hadj : j.val = i.val+1
  · apply leadingMatrix_eq_coeff
    simp [weightedDegree, hadj]
  · have hgap : (i.val : ℚ)+1 < j.val := by
      have : i.val+1 < j.val := by omega
      exact_mod_cast this
    have hnon : ¬ ∃ k, weightedDegree σ k i j = 0 ∧ A k i j ≠ 0 := by
      rintro ⟨k,hk,_⟩
      have hp : 0 < weightedDegree σ k i j := by
        unfold weightedDegree
        exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _)
          (mul_pos (by linarith) hσ)
      linarith
    have hlead : leadingMatrix A σ i j = 0 := by
      by_contra hh
      exact hnon ((leadingMatrix_ne_zero_iff A σ i j).mp hh)
    have hold : A 0 i j = 0 := by by_contra hh; exact hadj (hshape i j hh)
    rw [hlead,hold]

/-- A fractional slope cannot have a diagonal zero-weight coefficient. -/
theorem leadingMatrix_diagonal_zero (A : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (σ : ℚ) (hfrac : ∀ k : ℕ, σ ≠ k) (i : Fin n) :
    leadingMatrix A σ i i = 0 := by
  by_contra hh
  obtain ⟨k,hk,_⟩ := (leadingMatrix_ne_zero_iff A σ i i).mp hh
  apply hfrac k
  unfold weightedDegree at hk
  linarith

/-- Positive-order row normalization passes to the sheared leading matrix.
Rows outside `lastRows` remain exactly their old shift rows. -/
theorem leadingMatrix_normalized_rows (A : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hshape : ∀ i j, A 0 i j ≠ 0 → j.val = i.val+1)
    (lastRows : Set (Fin n))
    (hnorm : ∀ k, 0 < k → ∀ i j, i ∉ lastRows → A k i j = 0)
    {σ : ℚ} (hσ : 0 < σ) (i j : Fin n) (hi : i ∉ lastRows) :
    leadingMatrix A σ i j = A 0 i j := by
  by_cases hij : i < j
  · exact leadingMatrix_above A hshape hσ i j hij
  · have hji : j ≤ i := le_of_not_gt hij
    have hold : A 0 i j = 0 := by
      by_contra hh
      have := hshape i j hh
      omega
    rw [hold]
    by_contra hh
    obtain ⟨k,hk,hne⟩ := (leadingMatrix_ne_zero_iff A σ i j).mp hh
    have hkpos : 0 < k := by
      by_contra! hn
      have : k=0 := by omega
      exact hne (this ▸ hold)
    exact hne (hnorm k hkpos i j hi)

/-- The selected non-stopping slope has a new nonzero lower-triangular
entry. It follows from attainment of the finite minimum. -/
theorem exists_slope_with_leading_feedback
    (A : ℕ → Matrix (Fin n) (Fin n) ℂ) (q : ℕ)
    (hshape : ∀ i j, A 0 i j ≠ 0 → j.val = i.val+1) :
    ∃ σ : ℚ, 0 < σ ∧ σ ≤ (q+1 : ℕ) ∧
      (∀ k i j, A k i j ≠ 0 → 0 ≤ weightedDegree σ k i j) ∧
      (σ = (q+1 : ℕ) ∨ ∃ i j, j ≤ i ∧ leadingMatrix A σ i j ≠ 0) := by
  obtain ⟨σ,hσ,hcap,hbound,hatt⟩ := exists_leading_slope A q (by
    intro i j hji
    by_contra hh
    have := hshape i j hh
    omega)
  refine ⟨σ,hσ,hcap,hbound,?_⟩
  rcases hatt with he | ⟨k,i,j,hji,hne,hk⟩
  · exact Or.inl he
  · exact Or.inr ⟨i,j,hji,(leadingMatrix_ne_zero_iff A σ i j).mpr ⟨k,hk,hne⟩⟩

/-- Below the derivative threshold its exponent is strictly positive, so
it cannot alter the selected leading matrix. The threshold branch is not
silently identified with this case. -/
theorem derivative_correction_positive {q : ℕ} {σ : ℚ}
    (hσ : σ < (q+1 : ℕ)) : 0 < (q+1 : ℕ)-σ := sub_pos.mpr hσ

theorem weightedDegree_ramified (p a k : ℕ) (hp : p ≠ 0) (i j : Fin n) :
    (p : ℚ) * weightedDegree ((a : ℚ)/p) k i j =
      p*k + ((j.val : ℚ)-i.val-1)*a := by
  unfold weightedDegree
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  field_simp

#print axioms weightedDegree_injective
#print axioms leadingMatrix_eq_coeff
#print axioms leadingMatrix_ne_zero_iff
#print axioms leadingMatrix_above
#print axioms leadingMatrix_diagonal_zero
#print axioms leadingMatrix_normalized_rows
#print axioms exists_slope_with_leading_feedback
#print axioms derivative_correction_positive
#print axioms weightedDegree_ramified
#print axioms firstOrder_spec
#print axioms firstOrder_le
#print axioms firstOrder_pos
#print axioms exists_leading_slope
end WasowShearingLeading
