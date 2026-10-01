import LevinDensity

/-!
# Measurable epsilon/eta exceptional-set diagonalization

This retains measurability in the positive-density-bound version of the
exceptional-set construction. The measure-theoretic construction is reused
from `LevinDensity`; the input sets need not themselves have density zero.
-/

open MeasureTheory Set Filter Topology
open LevinDensity

namespace LevinMeasurableDensity

/-- The epsilon/eta diagonal principle with measurable output. Each property
may start at its own radius. The properties become stronger as the index grows,
while the eventual relative-measure bounds tend to zero. -/
theorem exists_common_exceptional_set_of_eventual_density_bounds
    (E : ℕ → Set ℝ) (P : ℕ → ℝ → Prop)
    (hEm : ∀ n, MeasurableSet (E n))
    (eta : ℕ → ℝ) (heta : Tendsto eta atTop (𝓝 0))
    (hE : ∀ n, ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      volume (E n ∩ Icc 0 R) ≤ ENNReal.ofReal (eta n * R))
    (hP : ∀ n, ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r → r ∉ E n → P n r)
    (hmono : ∀ n m, n ≤ m → ∀ r, P m r → P n r) :
    ∃ F : Set ℝ, MeasurableSet F ∧ ZeroRadialDensity F ∧
      ∀ n, ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r → r ∉ F → P n r := by
  classical
  choose cutoff hcut using hP
  let B : ℕ → Set ℝ := fun n => E n ∪ Iic (cutoff n)
  have hBm (n : ℕ) : MeasurableSet (B n) := (hEm n).union measurableSet_Iic
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        volume (B n ∩ Icc 0 R) ≤ ENNReal.ofReal (ε * R) := by
    intro ε hε N
    obtain ⟨M, hM⟩ := eventually_atTop.1
      ((tendsto_order.1 heta).2 (ε / 2) (by positivity))
    let n := max N M
    obtain ⟨A, hA, hEA⟩ := hE n
    obtain ⟨C, hC, hIC⟩ := zeroRadialDensity_Iic (cutoff n) (ε / 2) (by positivity)
    refine ⟨n, le_max_left _ _, max (max A C) 1, ?_, ?_⟩
    · exact (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_right _ _)
    · intro R hR
      have hRA : A ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hR)
      have hRC : C ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hR)
      have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hR)
      apply (radialDensity_le_iff _ hRpos hε.le).1
      have hEn : radialDensity (E n) R ≤ ε / 2 := by
        apply (radialDensity_le_iff _ hRpos (by positivity)).2
        exact (hEA R hRA).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (hM n (le_max_right _ _)).le hRpos.le))
      have hIn : radialDensity (Iic (cutoff n)) R ≤ ε / 2 :=
        (radialDensity_le_iff _ hRpos (by positivity)).2 (hIC R hRC)
      exact (radialDensity_union_le _ _ hRpos.le).trans (by linarith)
  let T : ℕ → Set ℝ := fun n => ⋂ m ≥ n, B m
  have hTm (n : ℕ) : MeasurableSet (T n) :=
    MeasurableSet.iInter (fun m => MeasurableSet.iInter (fun _ => hBm m))
  have hTz (n : ℕ) : ZeroRadialDensity (T n) :=
    zeroRadialDensity_tail_iInter B hsmall n
  obtain ⟨F, hFm, hFz, hcontains⟩ :=
    exists_measurable_zeroRadialDensity_eventually_contains T hTz hTm
  refine ⟨F, hFm, hFz, ?_⟩
  intro n
  obtain ⟨R₀, _, hR₀⟩ := hcontains n
  refine ⟨R₀, fun r hr hrF => ?_⟩
  by_contra hnot
  apply hrF
  apply hR₀ r hr
  simp only [T, mem_iInter]
  intro m hnm
  by_cases he : r ∈ E m
  · exact Or.inl he
  · by_cases hrm : cutoff m ≤ r
    · exact False.elim (hnot (hmono n m hnm r (hcut m r hrm he)))
    · exact Or.inr (le_of_not_ge hrm)

end LevinMeasurableDensity

#print axioms LevinMeasurableDensity.exists_common_exceptional_set_of_eventual_density_bounds
