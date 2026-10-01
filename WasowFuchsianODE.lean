import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.ContinuousMap.Compact

/-! Genuine global existence for continuous bounded linear equations.
The Picard operator acts on all continuous curves on a compact interval,
so no a priori solution or invariant ball is an assumption. -/
set_option autoImplicit false
noncomputable section
open Set Filter Function MeasureTheory intervalIntegral
open scoped Topology Nat NNReal
namespace WasowFuchsianODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {a b : ℝ}

/-- Continuous extension by projection onto the compact interval. -/
def extend (hab : a ≤ b) (u : C(Icc a b, E)) (t : ℝ) : E :=
  u (projIcc a b hab t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuous_extend (hab : a ≤ b) (u : C(Icc a b, E)) :
    Continuous (extend hab u) := u.continuous.comp (continuous_projIcc)

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem extend_of_mem (hab : a ≤ b) (u : C(Icc a b, E))
    {t : ℝ} (ht : t ∈ Icc a b) : extend hab u t = u ⟨t, ht⟩ := by
  simp [extend, projIcc_of_mem hab ht]

def integrand (hab : a ≤ b) (A : C(Icc a b, E →L[ℝ] E))
    (u : C(Icc a b, E)) (t : ℝ) :=
  A (projIcc a b hab t) (extend hab u t)

omit [CompleteSpace E] in
theorem continuous_integrand (hab : a ≤ b) (A : C(Icc a b, E →L[ℝ] E))
    (u : C(Icc a b, E)) : Continuous (integrand hab A u) :=
  (A.continuous.comp continuous_projIcc).clm_apply (continuous_extend hab u)

def next (hab : a ≤ b) (A : C(Icc a b, E →L[ℝ] E)) (x : E)
    (u : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := x + ∫ s in a..t.1, integrand hab A u s
  continuous_toFun := continuous_const.add
    ((differentiable_integral_of_continuous (continuous_integrand hab A u)).continuous.comp
      continuous_subtype_val)

/-- The factorial estimate gives a contraction of some Picard iterate on
any compact time interval, irrespective of its length. -/
theorem iterate_bound (hab : a ≤ b) (A : C(Icc a b, E →L[ℝ] E))
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x : E)
    (u v : C(Icc a b, E)) (n : ℕ) (t : Icc a b) :
    dist ((next hab A x)^[n] u t) ((next hab A x)^[n] v t) ≤
      (K * |t.1 - a|) ^ n / n.factorial * dist u v := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm]
    change ‖(x + ∫ s in a..t.1, integrand hab A ((next hab A x)^[n] u) s) -
      (x + ∫ s in a..t.1, integrand hab A ((next hab A x)^[n] v) s)‖ ≤ _
    rw [add_sub_add_left_eq_sub, ← integral_sub
      ((continuous_integrand hab A _).intervalIntegrable _ _)
      ((continuous_integrand hab A _).intervalIntegrable _ _)]
    calc
      _ ≤ ∫ s in uIoc a t.1, (K : ℝ) ^ (n + 1) * |s - a| ^ n /
          n.factorial * dist u v := by
        rw [norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le
          (Continuous.integrableOn_uIoc (by fun_prop))
        apply (ae_restrict_mem measurableSet_Ioc).mono
        intro s hs
        have hs' : s ∈ Icc a b :=
          (uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨le_rfl, hab⟩ t.2)) hs
        simp only [integrand, projIcc_of_mem hab hs', extend_of_mem hab _ hs']
        rw [← map_sub]
        calc
          _ ≤ ‖A ⟨s, hs'⟩‖ * ‖((next hab A x)^[n] u) ⟨s, hs'⟩ -
              ((next hab A x)^[n] v) ⟨s, hs'⟩‖ := (A ⟨s, hs'⟩).le_opNorm _
          _ ≤ (K : ℝ) * dist (((next hab A x)^[n] u) ⟨s, hs'⟩)
              (((next hab A x)^[n] v) ⟨s, hs'⟩) := by
            rw [dist_eq_norm]; gcongr; exact hK _
          _ ≤ _ := by
            rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
            gcongr
            simpa only [← mul_pow] using hn ⟨s, hs'⟩
      _ ≤ _ := by
        apply le_of_abs_le
        rw [← abs_intervalIntegral_eq, intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
          intervalIntegral.integral_const_mul, abs_mul, abs_div, abs_mul, abs_intervalIntegral_eq,
          integral_pow_abs_sub_uIoc, abs_div, abs_pow, abs_pow, abs_dist,
          NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

/-- Existence of the actual Picard fixed point on an arbitrary compact interval. -/
theorem exists_fixedPoint (hab : a ≤ b) (A : C(Icc a b, E →L[ℝ] E)) (x : E) :
    ∃ u : C(Icc a b, E), next hab A x u = u := by
  let K : ℝ≥0 := ‖A‖₊
  have hK (t : Icc a b) : ‖A t‖ ≤ K := ContinuousMap.norm_coe_le_norm A t
  obtain ⟨n, hn⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop
    ((K : ℝ) * (b - a))).eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hc : 0 ≤ ((K : ℝ) * (b - a)) ^ n / n.factorial := by positivity
  let c : ℝ≥0 := ⟨_, hc⟩
  have hcontract : ContractingWith c (next hab A x)^[n] := by
    refine ⟨hn, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    apply (ContinuousMap.dist_le (by positivity)).mpr
    intro t
    apply (iterate_bound hab A K hK x u v n t).trans
    change (↑K * |↑t - a|) ^ n / ↑n.factorial * dist u v ≤
      (↑K * (b - a)) ^ n / ↑n.factorial * dist u v
    gcongr
    rw [abs_of_nonneg (sub_nonneg.mpr t.2.1)]
    exact sub_le_sub_right t.2.2 a
  exact ⟨_, hcontract.isFixedPt_fixedPoint_iterate⟩

/-- A solution on an arbitrary compact time interval, constructed from the
actual continuous coefficient. The chosen extension also has the stated
ordinary derivative at both endpoints. -/
theorem exists_solution_Icc (hab : a ≤ b) (A : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A (Icc a b)) (x : E) :
    ∃ u : ℝ → E, Continuous u ∧ u a = x ∧
      ∀ t ∈ Icc a b, HasDerivAt u (A t (u t)) t := by
  let Ac : C(Icc a b, E →L[ℝ] E) := ⟨fun t => A t, hA.domRestrict⟩
  obtain ⟨v, hv⟩ := exists_fixedPoint hab Ac x
  let u : ℝ → E := fun t => x + ∫ s in a..t, integrand hab Ac v s
  have hcont := continuous_integrand hab Ac v
  have hderiv (t : ℝ) : HasDerivAt u (integrand hab Ac v t) t :=
    (integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt).const_add x
  have huv (t : Icc a b) : u t = v t := congrArg (fun w : C(Icc a b, E) => w t) hv
  refine ⟨u, continuous_iff_continuousAt.mpr (fun t => (hderiv t).continuousAt), by simp [u], ?_⟩
  intro t ht
  convert hderiv t using 1
  simp only [integrand, projIcc_of_mem hab ht, extend_of_mem hab _ ht]
  exact congrArg (A t) (huv ⟨t, ht⟩)

omit [CompleteSpace E] in
/-- Uniqueness on a compact interval uses only the actual linear coefficient. -/
theorem solution_eqOn_Icc (_hab : a ≤ b) (A : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A (Icc a b)) (u v : ℝ → E)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (A t (u t)) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (A t (v t)) t)
    (hinit : u a = v a) : EqOn u v (Icc a b) := by
  let Ac : C(Icc a b, E →L[ℝ] E) := ⟨fun t => A t, hA.domRestrict⟩
  let K : ℝ≥0 := ‖Ac‖₊
  have hK (t : ℝ) (ht : t ∈ Icc a b) : ‖A t‖ ≤ K :=
    ContinuousMap.norm_coe_le_norm Ac ⟨t, ht⟩
  apply ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (K := K) (v := fun t x => A t x)
  · intro t ht
    exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hK t ⟨ht.1, ht.2.le⟩)).lipschitzOnWith
  · exact fun t ht => (hu t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hu t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt
  · exact fun _ _ => mem_univ _
  · exact fun t ht => (hv t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hv t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt
  · exact fun _ _ => mem_univ _
  · exact hinit

/-- Every continuous, time-dependent bounded linear operator field has an
actual solution on the whole right half-line. No global bound on the field,
nor any pre-existing solution, is assumed. -/
theorem exists_solution_Ici (A : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A (Ici a)) (x : E) :
    ∃ u : ℝ → E, u a = x ∧ ContinuousOn u (Ici a) ∧
      ∀ t : ℝ, a < t → HasDerivAt u (A t (u t)) t := by
  classical
  have hex (b : ℝ) := exists_solution_Icc (le_max_left a b) A
    (hA.mono (fun _ ht => ht.1)) x
  choose sol hcont hinit hderiv using hex
  let u : ℝ → E := fun t => sol (t + 1) t
  have heq (b t : ℝ) (ht : a ≤ t) (htb : t ≤ max a b) : u t = sol b t := by
    have hsmall : Icc a t ⊆ Ici a := fun _ hs => hs.1
    have hleft (s : ℝ) (hs : s ∈ Icc a t) : s ∈ Icc a (max a (t + 1)) :=
      ⟨hs.1, hs.2.trans ((by linarith : t ≤ t + 1).trans (le_max_right _ _))⟩
    have hright (s : ℝ) (hs : s ∈ Icc a t) : s ∈ Icc a (max a b) :=
      ⟨hs.1, hs.2.trans htb⟩
    exact solution_eqOn_Icc ht A (hA.mono hsmall) (sol (t + 1)) (sol b)
      (fun s hs => hderiv (t + 1) s (hleft s hs))
      (fun s hs => hderiv b s (hright s hs))
      ((hinit _).trans (hinit _).symm) ⟨ht, le_rfl⟩
  have hevent (t : ℝ) (ht : a ≤ t) :
      u =ᶠ[𝓝[Ici a] t] sol (t + 1) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith : t < t + 1))] with s hs hs'
    exact heq (t + 1) s hs (hs'.le.trans (le_max_right _ _))
  refine ⟨u, ?_, ?_, ?_⟩
  · exact (heq (a + 1) a le_rfl (le_max_left _ _)).trans (hinit _)
  · intro t ht
    exact ((hcont (t + 1)).continuousAt.continuousWithinAt).congr_of_eventuallyEq
      (hevent t ht) (heq (t + 1) t ht (by exact (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)))
  · intro t ht
    have hlocal : u =ᶠ[𝓝 t] sol (t + 1) := by
      filter_upwards [Ioo_mem_nhds ht (by linarith : t < t + 1)] with s hs
      exact heq (t + 1) s hs.1.le (hs.2.le.trans (le_max_right _ _))
    have htmem : t ∈ Icc a (max a (t + 1)) :=
      ⟨ht.le, (by linarith : t ≤ t + 1).trans (le_max_right _ _)⟩
    have hd := (hderiv (t + 1) t htmem).congr_of_eventuallyEq hlocal
    rwa [← hlocal.eq_of_nhds] at hd

#print axioms exists_solution_Ici
#print axioms exists_solution_Icc
#print axioms solution_eqOn_Icc
#print axioms continuous_extend
#print axioms extend_of_mem
#print axioms continuous_integrand
#print axioms iterate_bound
#print axioms exists_fixedPoint
end WasowFuchsianODE
