import WasowShearingTermination

/-! The rank after minimal-denominator ramification is automatically a
natural number in the continuing branch. A successor then uses the actual
ramification multiplier and automatically chosen sorted Jordan coordinates. -/
set_option autoImplicit false
noncomputable section
namespace WasowRankSelection
open WasowMultiShiftReduction WasowOrderedShearing WasowShearingLeading
open WasowShearingTermination

/-- Below the stopping slope, the rational expression for the next rank is
an integer at least zero. Positivity of the slope is not needed for this
arithmetic fact; it is retained in the genuine successor theorem below. -/
theorem exists_ramified_rank (q : ℕ) (σ : ℚ) (hcap : σ < (q : ℚ) + 1) :
    ∃ q' : ℕ, (q' : ℚ) = (σ.den : ℚ) * ((q : ℚ) + 1 - σ) - 1 := by
  have hd : (0 : ℚ) < σ.den := by exact_mod_cast σ.den_pos
  have hnum : (σ.num : ℚ) < (σ.den : ℚ) * ((q : ℚ) + 1) := by
    have hh := mul_lt_mul_of_pos_right hcap hd
    rw [Rat.mul_den_eq_num] at hh
    nlinarith
  have hz : σ.num < (σ.den : ℤ) * ((q : ℤ) + 1) := by exact_mod_cast hnum
  let k : ℤ := (σ.den : ℤ) * ((q : ℤ) + 1) - σ.num - 1
  have hk : 0 ≤ k := by dsimp [k]; omega
  refine ⟨k.toNat, ?_⟩
  have hcast : ((k.toNat : ℕ) : ℚ) = (k : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hk
  rw [hcast]
  dsimp only [k]
  push_cast
  rw [← Rat.mul_den_eq_num σ]
  ring

/-- Continuing actual ramified single-eigenvalue data automatically produce
both a nonnegative next rank and the required sorted Jordan coordinates. -/
theorem exists_ramified_successor (old : State)
    (A : ℕ → Matrix (Index old.sizes) (Index old.sizes) ℂ)
    (hA : A 0 = jordanShift old.sizes)
    (hrows : ∀ k, 0 < k → ∀ a (i : Fin (old.sizes a+1)) j,
      i.val < old.sizes a → A k ⟨a,i⟩ j = 0)
    (σ : ℚ) (hσ : 0 < σ) (hcap : σ < (old.rank : ℚ) + 1)
    (hweights : ∀ k i j, flatCoefficients old.sizes A k i j ≠ 0 →
      0 ≤ weightedDegree σ k i j)
    (hfeedback : ∃ i j, j ≤ i ∧ leadingMatrix (flatCoefficients old.sizes A) σ i j ≠ 0)
    (α : ℂ)
    (hN : IsNilpotent ((σ.den : ℂ) • shearedLeading old.sizes A σ - α • 1)) :
    ∃ next : State, Step next old := by
  obtain ⟨q', hq'⟩ := exists_ramified_rank old.rank σ hcap
  have hc : (σ.den : ℂ) ≠ 0 := by exact_mod_cast σ.den_ne_zero
  obtain ⟨next, _, hs⟩ := WasowShearingTermination.exists_successor old A hA hrows
    σ hσ hcap hweights hfeedback (σ.den : ℂ) α hc hN q' hq'
  exact ⟨next, hs⟩

#print axioms exists_ramified_rank
#print axioms exists_ramified_successor
end WasowRankSelection
