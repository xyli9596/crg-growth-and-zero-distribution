import WasowLaurentFiniteRealization

/-! Complete asymptotic matrix expansions on an arbitrary approach filter.
Unlike Taylor expansions, the formal series below is not required to converge.
The filter may be a closed subsector approaching the origin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Filter Asymptotics
namespace CRGAsymptoticCoefficientCompleteExpansion
open WasowMatrixPolynomial WasowLaurentGauge WasowLaurentClearing
open WasowLaurentTruncation WasowLaurentFiniteRealization
variable {m : ℕ}

/-- Every finite partial sum approximates the actual coefficient to its next
order on the specified filter. No infinite formal series is evaluated. -/
def CompleteExpansion (l : Filter ℂ) (c : ℂ → Mat (m := m))
    (A : PowerSeries (Mat (m := m))) : Prop :=
  ∀ N : ℕ, (fun z => c z - eval (PowerSeries.trunc N A) z) =O[l]
    (fun z : ℂ => ‖z‖ ^ N)

/-- A convergent expansion is one special case of a complete asymptotic
expansion; this direction imposes no convergence on its later users. -/
theorem completeExpansion_of_taylor
    {c : ℂ → Mat (m := m)}
    {s : FormalMultilinearSeries ℂ ℂ (Mat (m := m))}
    (hc : HasFPowerSeriesAt c s 0) (A : PowerSeries (Mat (m := m)))
    (hcoeff : ∀ n, s.coeff n = PowerSeries.coeff n A)
    {l : Filter ℂ} (hl : l ≤ 𝓝 (0 : ℂ)) : CompleteExpansion l c A := by
  intro N
  have ht : (fun z : ℂ => c z - eval (PowerSeries.trunc N A) z) =O[𝓝 0]
      (fun z : ℂ => ‖z‖ ^ N) :=
    (hc.isBigO_sub_partialSum_pow N).congr_left
      (fun z => by rw [zero_add, WasowActualTruncation.eval_trunc_eq_partialSum s A hcoeff])
  exact ht.mono hl

/-- The finite cleared defect has arbitrary order using only the complete
asymptotic expansion and the actual formal differential equation. -/
theorem actualDefect_isBigO_of_completeExpansion
    {l : Filter ℂ} (hl : l ≤ 𝓝 (0 : ℂ))
    {c : ℂ → Mat (m := m)} {A : PowerSeries (Mat (m := m))}
    (hc : CompleteExpansion l c A)
    (a h N : ℕ) (hh : 0 < h) (P B : PowerSeries (Mat (m := m)))
    (heq : WasowClearedResidual.Equation a h A P B) :
    WasowClearedResidual.actualDefect a h N c P B =O[l]
      (fun z : ℂ => ‖z‖ ^ N) := by
  have hP : eval (PowerSeries.trunc N P) =O[l] (fun _ : ℂ => (1 : ℝ)) :=
    (isBigO_const_of_tendsto ((continuous_eval (PowerSeries.trunc N P)).tendsto 0) (by norm_num)).mono hl
  have hproduct : (fun z : ℂ =>
      (c z - eval (PowerSeries.trunc N A) z) * eval (PowerSeries.trunc N P) z) =O[l]
      (fun z : ℂ => ‖z‖ ^ N) := by
    simpa only [mul_one] using (hc N).mul hP
  have hfinite := (isBigO_eval_of_X_pow_dvd
    (WasowClearedResidual.polynomialDefect a h N A P B) N
    (WasowClearedResidual.polynomialDefect_divisible a h N hh A P B heq)).mono hl
  exact (hproduct.add hfinite).congr_left
    (fun z => (WasowClearedResidual.actualDefect_eq a h N c A P B z).symm)

/-- The inverse-normalized Laurent remainder retains its fixed pole losses.
Only the actual coefficient's complete asymptotic expansion is assumed. -/
theorem remainder_isBigO_of_completeExpansion
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0 : ℂ))
    {c : ℂ → Mat (m := m)} {A : PowerSeries (Mat (m := m))}
    (hc : CompleteExpansion l c A)
    (a b h k : ℕ) (hh : 0 < h) (P Q B : PowerSeries (Mat (m := m)))
    (hPQ : P * Q = PowerSeries.X ^ (a+b))
    (heq : WasowClearedResidual.Equation a h A P B) :
    WasowLaurentRemainder.remainder a h (a+b+h+k) c P B =O[l]
      (fun z : ℂ => ‖z‖ ^ k) := by
  let N := a+b+h+k
  obtain ⟨CG, hCG, hG⟩ := WasowLaurentInverse.eventually_inverse_bounds
    P Q a b N hPQ (by dsimp [N]; omega)
  obtain ⟨CE, hCE, hE⟩ :=
    (actualDefect_isBigO_of_completeExpansion (hl.trans nhdsWithin_le_nhds)
      hc a h N hh P B heq).exists_pos
  apply IsBigO.of_bound (CG * CE)
  filter_upwards [hG.filter_mono hl, hE.bound, (show ∀ᶠ z in l, z ≠ 0 from Filter.Eventually.filter_mono hl self_mem_nhdsWithin)]
    with z hg he hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hraw : ‖WasowLaurentActualResidual.rawDefect a h N c P B z‖ =
      ‖WasowClearedResidual.actualDefect a h N c P B z‖ / ‖z‖ ^ (a+h) := by
    rw [WasowLaurentActualResidual.rawDefect_eq a h N hh c P B hz]
    simp only [norm_smul, zpow_neg, zpow_natCast, norm_inv, norm_pow, div_eq_mul_inv, mul_comm]
  have he' : ‖WasowClearedResidual.actualDefect a h N c P B z‖ ≤ CE * ‖z‖ ^ N := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg z) N)] using he
  have hb : ‖WasowLaurentRemainder.remainder a h N c P B z‖ ≤ CG * CE * ‖z‖ ^ k := by
    calc
      _ ≤ ‖(WasowLaurentInverse.finiteGauge P a N z)⁻¹‖ *
          ‖WasowLaurentActualResidual.rawDefect a h N c P B z‖ := norm_mul_le _ _
      _ ≤ (CG / ‖z‖ ^ b) * (CE * ‖z‖ ^ N / ‖z‖ ^ (a+h)) := by
        rw [hraw]
        apply mul_le_mul hg.2.2.2.2
          (div_le_div_of_nonneg_right he' (pow_nonneg (norm_nonneg z) _))
          (div_nonneg (norm_nonneg _) (by positivity)) (div_nonneg hCG.le (by positivity))
      _ = _ := by
        have hp : ‖z‖ ^ N = ‖z‖ ^ (a+b+h) * ‖z‖ ^ k := by rw [← pow_add]
        rw [hp]
        simp only [pow_add]
        field_simp
  simpa only [N, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg z) k)] using hb

/-- Genuine finite Laurent realization along a subsector filter, valid even
for divergent coefficient expansions. Inverse exponents are fixed by the
formal gauge and do not depend on the requested residual order. -/
theorem finite_realization_of_completeExpansion
    {l : Filter ℂ} (hl : l ≤ 𝓝[≠] (0 : ℂ))
    (A B G H : LMat (m := m))
    (h : ℕ) (hh : 0 < h) (hA : poleOrder A ≤ h) (hB : poleOrder B ≤ h)
    (hGH : G*H=1) (hHG : H*G=1) (heq : GaugeEquation A G B)
    {c : ℂ → Mat (m := m)} (hc : CompleteExpansion l c (clearAt h A)) (k : ℕ) :
    residual h B G H c k =O[l] (fun z : ℂ => ‖z‖ ^ k) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in l,
      (gauge h G H k z).det ≠ 0 ∧
      (gauge h G H k z)⁻¹ * gauge h G H k z = 1 ∧
      gauge h G H k z * (gauge h G H k z)⁻¹ = 1 ∧
      ‖gauge h G H k z‖ ≤ C / ‖z‖ ^ poleOrder G ∧
      ‖(gauge h G H k z)⁻¹‖ ≤ C / ‖z‖ ^ poleOrder H ∧
      DifferentiableAt ℂ (gauge h G H k) z ∧
      actualCoefficient h c z * gauge h G H k z =
        deriv (gauge h G H k) z +
          gauge h G H k z * (target h B G H k z + residual h B G H c k z) := by
  refine ⟨?_, ?_⟩
  · exact remainder_isBigO_of_completeExpansion hl hc (poleOrder G) (poleOrder H)
      h k hh (cleared G) (cleared H) (clearAt h B) (cleared_mul G H hGH)
      (equation_clearAt _ hh A B G hA hB heq)
  · obtain ⟨C,hC,hb⟩ := WasowLaurentInverse.eventually_inverse_bounds_of_laurent G H
      hGH hHG (truncationOrder h G H k) (by unfold truncationOrder; omega)
    refine ⟨C,hC,?_⟩
    filter_upwards [hb.filter_mono hl,
      (show ∀ᶠ z in l, z ≠ 0 from Filter.Eventually.filter_mono hl self_mem_nhdsWithin)] with z hz hzne
    exact ⟨hz.1,hz.2.1,hz.2.2.1,hz.2.2.2.1,hz.2.2.2.2,
      gauge_differentiableAt h G H k hzne,
      transformed_equation h B G H c k z hz.2.2.1⟩

#print axioms completeExpansion_of_taylor
#print axioms actualDefect_isBigO_of_completeExpansion
#print axioms remainder_isBigO_of_completeExpansion
#print axioms finite_realization_of_completeExpansion
end CRGAsymptoticCoefficientCompleteExpansion
