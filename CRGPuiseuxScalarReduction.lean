import CRGAsymptoticCoefficientQuotient
import CRGGroupHighest

/-! Highest nonzero formal coefficient and the actual flat residual in the
scalar equation. All choices use the fixed coefficient expansions; actual
coefficients above the highest formal order need not vanish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology BigOperators
open Filter Asymptotics
namespace CRGPuiseuxScalarReduction
open CRGAsymptoticCoefficientQuotient
variable {n : ℕ}

structure Highest (A : Fin (n+1) → PowerSeries ℂ) where
  index : Fin (n+1)
  nonzero : A index ≠ 0
  above_zero : ∀ j : Fin (n+1), index.val<j.val → A j=0

theorem exists_highest (A : Fin (n+1) → PowerSeries ℂ)
    (hA : ∃j,A j≠0) : Nonempty (Highest A) := by
  classical
  let s := Finset.univ.filter (fun j => A j≠0)
  have hs : s.Nonempty := by
    obtain ⟨j,hj⟩ := hA
    exact ⟨j,by simp [s,hj]⟩
  let m := s.max' hs
  have hm : m∈s := Finset.max'_mem s hs
  refine ⟨⟨m,(Finset.mem_filter.mp hm).2,fun j hj => ?_⟩⟩
  by_contra hbj
  have hjm : j≤m := Finset.le_max' s j (by simp [s,hbj])
  exact (not_le.mpr hj) hjm

/-- A high coefficient has a zero formal series but is an actual function;
its quotient by the leading nonzero coefficient remains flat. -/
theorem flat_high_quotient
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0 : ℂ))
    {C : Fin (n+1) → ℂ → ℂ} {A : Fin (n+1) → PowerSeries ℂ}
    (hC : ∀j,CompleteExpansion l (C j) (A j)) (H : Highest A)
    (j : Fin (n+1)) (hj : H.index.val<j.val) :
    Flat l (fun z => C j z/C H.index z) := by
  have hz : Flat l (C j) := (flat_iff_zero_expansion _ _).mpr
    (by rw [← H.above_zero j hj]; exact hC j)
  exact flat_quotient hl hz (hC H.index) H.nonzero

/-- The forcing in the reduced normalized scalar equation. -/
def residual (C : Fin (n+1) → ℂ → ℂ) (m : Fin (n+1))
    (v : Fin (n+1) → ℂ → ℂ) (z : ℂ) : ℂ :=
  -∑ j : Fin (n+1), if m.val<j.val then C j z/C m z*v j z else 0

/-- The forcing is smaller than every positive power after any polynomial
loss from the logarithmic derivatives. -/
theorem residual_flat
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0 : ℂ))
    {C : Fin (n+1) → ℂ → ℂ} {A : Fin (n+1) → PowerSeries ℂ}
    (hC : ∀j,CompleteExpansion l (C j) (A j)) (H : Highest A)
    (v : Fin (n+1) → ℂ → ℂ)
    (hv : ∀ j, ∃K : ℕ, v j =O[l] (fun z : ℂ => (‖z‖^K)⁻¹)) :
    Flat l (residual C H.index v) := by
  classical
  intro N
  apply IsBigO.neg_left
  have ht : ∀j∈(Finset.univ : Finset (Fin (n+1))),
      (fun z => if H.index.val<j.val then C j z/C H.index z*v j z else 0) =O[l]
        (fun z : ℂ => ‖z‖^N) := by
    intro j _hj
    by_cases hj : H.index.val<j.val
    · obtain ⟨K,hK⟩ := hv j
      simpa only [if_pos hj] using
        flat_mul_of_power_bound hl (flat_high_quotient hl hC H j hj) K hK N
    · simp only [if_neg hj]
      exact isBigO_zero _ _
  exact (IsBigO.sum ht).congr_left (fun z => by simp only [Finset.sum_apply])

/-- Exact lower/highest/flat split of the actual equation. Terms with zero
formal series are retained inside the residual instead of being erased. -/
theorem reduced_equation
    (C : Fin (n+1) → ℂ → ℂ) (m : Fin (n+1))
    (v : Fin (n+1) → ℂ → ℂ) (z : ℂ) (hCm : C m z≠0)
    (heq : ∑j,C j z*v j z=0) :
    v m z + ∑j : Fin m.val,
      C (CRGGroupHighest.lowerIndex m j) z/C m z*
        v (CRGGroupHighest.lowerIndex m j) z = residual C m v z := by
  classical
  have hquot : ∑j,C j z/C m z*v j z=0 := by
    simp_rw [div_mul_eq_mul_div]
    rw [←Finset.sum_div,heq,zero_div]
  let w : Fin (n+1) → ℂ := fun j => if j.val≤m.val then C j z/C m z*v j z else 0
  have hlow := CRGGroupHighest.sum_truncate w m (fun j hj => by
    dsimp [w]
    rw [if_neg (by omega)])
  have hlower : (∑j : Fin m.val,w (CRGGroupHighest.lowerIndex m j)) =
      ∑j : Fin m.val,C (CRGGroupHighest.lowerIndex m j) z/C m z*
        v (CRGGroupHighest.lowerIndex m j) z := by
    apply Finset.sum_congr rfl
    intro j _hj
    dsimp [w,CRGGroupHighest.lowerIndex]
    rw [if_pos (by omega)]
  have hmain : w m=v m z := by
    dsimp [w]
    rw [if_pos le_rfl,div_self hCm,one_mul]
  have hsplit : (∑j,C j z/C m z*v j z)=
      (∑j,w j)+(∑j,if m.val<j.val then C j z/C m z*v j z else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    dsimp [w]
    by_cases hj : j.val≤m.val <;> simp [hj,not_lt.mpr]
    · omega
  rw [hsplit,hlow,hmain,hlower] at hquot
  exact eq_neg_of_add_eq_zero_left hquot

/-- Order zero is excluded by the actual normalized equation and the flat
forcing, before applying any normal form or ray comparison theorem. -/
theorem highest_order_positive
    {l : Filter ℂ} [NeBot l] (hl : l ≤ 𝓝[≠] (0 : ℂ))
    {C : Fin (n+1) → ℂ → ℂ} {A : Fin (n+1) → PowerSeries ℂ}
    (hC : ∀j,CompleteExpansion l (C j) (A j)) (H : Highest A)
    (v : Fin (n+1) → ℂ → ℂ)
    (hv : ∀ j, ∃K : ℕ, v j =O[l] (fun z : ℂ => (‖z‖^K)⁻¹))
    (hvzero : ∀ᶠz in l,v 0 z=1)
    (heq : ∀ᶠz in l,∑j,C j z*v j z=0) : 0<H.index.val := by
  apply Nat.pos_of_ne_zero
  intro hm
  have hf := residual_flat hl hC H v hv
  have ht := tendsto_of_completeExpansion (hl.trans nhdsWithin_le_nhds)
    ((flat_iff_zero_expansion _ _).mp hf)
  have hne := ht.eventually_ne zero_ne_one
  have hden := eventually_ne_zero_of_nonzero_series hl (hC H.index) H.nonzero
  have hindex : H.index=0 := Fin.ext hm
  have himpossible : ∀ᶠz in l,False := by
    filter_upwards [hden,hvzero,heq,hne] with z hd hz he hn
    have hr := reduced_equation C H.index v z hd he
    have hsum : (∑j : Fin H.index.val,
        C (CRGGroupHighest.lowerIndex H.index j) z/C H.index z*
          v (CRGGroupHighest.lowerIndex H.index j) z)=0 := by
      have : IsEmpty (Fin H.index.val) := by rw [hm];infer_instance
      exact Finset.sum_eq_zero (fun j _ => isEmptyElim j)
    rw [hsum,add_zero] at hr
    have hvindex : v H.index z=1 := by simpa only [hindex] using hz
    rw [hvindex] at hr
    exact hn hr.symm
  obtain ⟨z,hz⟩ := himpossible.exists
  exact hz

#print axioms exists_highest
#print axioms flat_high_quotient
#print axioms residual_flat
#print axioms reduced_equation
#print axioms highest_order_positive
end CRGPuiseuxScalarReduction
