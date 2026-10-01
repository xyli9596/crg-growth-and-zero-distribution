import CRGAsymptoticCoefficientMatrixTransfer
import Mathlib.Analysis.Analytic.Basic

/-! Algebra and analytic substitution for complete scalar asymptotic
expansions. The outer series in a composition is allowed to diverge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology BigOperators
open Filter Asymptotics
namespace CRGAsymptoticCoefficientScalarAlgebra
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientMatrixTransfer

/-- The finite partial sum of a scalar Taylor expansion. -/
theorem eval_trunc_eq_partialSum (s : FormalMultilinearSeries ℂ ℂ ℂ)
    (A : PowerSeries ℂ) (hc : ∀n,s.coeff n=PowerSeries.coeff n A) (N : ℕ) (z : ℂ) :
    (PowerSeries.trunc N A).eval z=s.partialSum N z := by
  change Polynomial.eval₂ (RingHom.id ℂ) z (PowerSeries.trunc N A)=_
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  unfold FormalMultilinearSeries.partialSum
  apply Finset.sum_congr rfl
  intro n _hn
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,hc]
  simp only [RingHom.id_apply,smul_eq_mul,mul_comm]

theorem completeExpansion_of_taylor {l : Filter ℂ} (hl : l ≤ 𝓝 (0:ℂ))
    {f : ℂ → ℂ} {s : FormalMultilinearSeries ℂ ℂ ℂ} (hf : HasFPowerSeriesAt f s 0)
    (A : PowerSeries ℂ) (hc : ∀n,s.coeff n=PowerSeries.coeff n A) :
    CompleteExpansion l f A := by
  intro N
  have ht : (fun z => f z-(PowerSeries.trunc N A).eval z) =O[𝓝 (0:ℂ)]
      (fun z : ℂ => ‖z‖^N) :=
    (hf.isBigO_sub_partialSum_pow N).congr_left (fun z => by
      rw [zero_add,eval_trunc_eq_partialSum s A hc])
  exact ht.mono hl

/-- A holomorphic germ supplies its actual fixed full coefficient expansion. -/
theorem exists_completeExpansion_of_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃A : PowerSeries ℂ, ∀l : Filter ℂ,l≤𝓝 (0:ℂ) → CompleteExpansion l f A := by
  obtain ⟨s,hs⟩ := hf
  refine ⟨PowerSeries.mk (fun n => s.coeff n),fun l hl => ?_⟩
  exact completeExpansion_of_taylor hl hs _ (fun n => (PowerSeries.coeff_mk _ _).symm)

theorem completeExpansion_const {l : Filter ℂ} (hl : l ≤ 𝓝 (0:ℂ)) (c : ℂ) :
    CompleteExpansion l (fun _ => c) (PowerSeries.C c) := by
  simpa only [Polynomial.eval_C,Polynomial.coe_C] using
    polynomial_completeExpansion hl (Polynomial.C c)

theorem completeExpansion_add {l : Filter ℂ} {f g : ℂ → ℂ} {A B : PowerSeries ℂ}
    (hf : CompleteExpansion l f A) (hg : CompleteExpansion l g B) :
    CompleteExpansion l (fun z => f z+g z) (A+B) := by
  intro N
  exact ((hf N).add (hg N)).congr_left (fun z => by rw [map_add,Polynomial.eval_add];ring)

theorem completeExpansion_sub {l : Filter ℂ} {f g : ℂ → ℂ} {A B : PowerSeries ℂ}
    (hf : CompleteExpansion l f A) (hg : CompleteExpansion l g B) :
    CompleteExpansion l (fun z => f z-g z) (A-B) := by
  simpa only [sub_eq_add_neg] using completeExpansion_add hf (completeExpansion_neg hg)

theorem completeExpansion_mul {l : Filter ℂ} (hl : l ≤ 𝓝 (0:ℂ))
    {f g : ℂ → ℂ} {A B : PowerSeries ℂ}
    (hf : CompleteExpansion l f A) (hg : CompleteExpansion l g B) :
    CompleteExpansion l (fun z => f z*g z) (A*B) := by
  intro N
  have hgb : g =O[l] (fun _ : ℂ => (1:ℝ)) :=
    isBigO_const_of_tendsto (tendsto_of_completeExpansion hl hg) (by norm_num)
  have hAb : (fun z : ℂ => (PowerSeries.trunc N A).eval z) =O[l]
      (fun _ : ℂ => (1:ℝ)) :=
    isBigO_const_of_tendsto (((PowerSeries.trunc N A).continuous.tendsto 0).mono_left hl) (by norm_num)
  have happrox : (fun z => f z*g z-(PowerSeries.trunc N A*PowerSeries.trunc N B).eval z) =O[l]
      (fun z : ℂ => ‖z‖^N) := by
    have hfirst : (fun z => (f z-(PowerSeries.trunc N A).eval z)*g z) =O[l]
        (fun z : ℂ => ‖z‖^N) := by simpa only [mul_one] using (hf N).mul hgb
    have hsecond : (fun z => (PowerSeries.trunc N A).eval z*(g z-(PowerSeries.trunc N B).eval z)) =O[l]
        (fun z : ℂ => ‖z‖^N) := by simpa only [one_mul] using hAb.mul (hg N)
    exact (hfirst.add hsecond).congr_left (fun z => by rw [Polynomial.eval_mul];ring)
  have hfinite : (fun z =>
      (PowerSeries.trunc N A*PowerSeries.trunc N B-PowerSeries.trunc N (A*B)).eval z) =O[l]
      (fun z : ℂ => ‖z‖^N) := by
    apply (isBigO_polynomial_of_X_pow_dvd _ N ?_).mono hl
    apply Polynomial.X_pow_dvd_iff.mpr
    intro k hk
    rw [Polynomial.coeff_sub,PowerSeries.coeff_trunc,if_pos hk]
    have he := PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc A B hk
    rw [←Polynomial.coe_mul,Polynomial.coeff_coe] at he
    rw [←he,sub_self]
  exact (happrox.add hfinite).congr_left (fun z => by rw [Polynomial.eval_sub];ring)

theorem completeExpansion_pow {l : Filter ℂ} (hl : l ≤ 𝓝 (0:ℂ))
    {g : ℂ → ℂ} {G : PowerSeries ℂ} (hg : CompleteExpansion l g G) (k : ℕ) :
    CompleteExpansion l (fun z => (g z)^k) (G^k) := by
  induction k with
  | zero => simpa only [pow_zero,map_one] using completeExpansion_const hl 1
  | succ k hk => simpa only [pow_succ] using completeExpansion_mul hl hk hg

theorem completeExpansion_sum {ι : Type*} (s : Finset ι) {l : Filter ℂ}
    {f : ι → ℂ → ℂ} {A : ι → PowerSeries ℂ}
    (hf : ∀i∈s,CompleteExpansion l (f i) (A i)) :
    CompleteExpansion l (fun z => ∑i∈s,f i z) (∑i∈s,A i) := by
  intro N
  have he := IsBigO.sum (fun i hi => hf i hi N)
  apply he.congr_left
  intro z
  rw [map_sum,Polynomial.eval_finsetSum]
  simp only [Finset.sum_apply,Finset.sum_sub_distrib]

/-- The formal composition coefficients are finite triangular sums. -/
def formalComposition (F G : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => ∑k∈Finset.range (n+1),PowerSeries.coeff k F*PowerSeries.coeff n (G^k))

def finiteComposition (N : ℕ) (F G : PowerSeries ℂ) : PowerSeries ℂ :=
  ∑k∈Finset.range N,PowerSeries.C (PowerSeries.coeff k F)*G^k

/-- A zero constant term makes all sufficiently high powers invisible to a
fixed formal coefficient; this is the exact reason substitution is defined. -/
theorem coeff_pow_eq_zero_of_lt {G : PowerSeries ℂ} (hG : PowerSeries.constantCoeff G=0)
    {n k : ℕ} (hn : n<k) : PowerSeries.coeff n (G^k)=0 := by
  apply PowerSeries.coeff_of_lt_order
  exact (by exact_mod_cast hn : (n:ENat)<k).trans_le
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero k hG)

theorem trunc_finiteComposition {F G : PowerSeries ℂ} (hG : PowerSeries.constantCoeff G=0) (N : ℕ) :
    PowerSeries.trunc N (finiteComposition N F G)=PowerSeries.trunc N (formalComposition F G) := by
  ext n
  rw [PowerSeries.coeff_trunc,PowerSeries.coeff_trunc]
  split_ifs with hn
  · simp only [finiteComposition,map_sum,PowerSeries.coeff_C_mul,formalComposition,PowerSeries.coeff_mk]
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _hk hkn
    have hnk : n<k := by
      simp only [Finset.mem_range,not_lt] at hkn
      omega
    rw [coeff_pow_eq_zero_of_lt hG hnk,mul_zero]
  · rfl

/-- Polynomial approximations with all-order errors can be substituted
directly. This form also applies to Watson expansions without constructing
an artificial outer function on a punctured neighborhood. -/
theorem completeExpansion_of_polynomial_approximations
    {l : Filter ℂ} (hl : l ≤ 𝓝 (0:ℂ))
    {K g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hg : CompleteExpansion l g G) (hG : PowerSeries.constantCoeff G=0)
    (happrox : ∀N : ℕ, (fun z => K z-(PowerSeries.trunc N F).eval (g z)) =O[l]
      (fun z => ‖g z‖^N)) :
    CompleteExpansion l K (formalComposition F G) := by
  intro N
  have hgO : g =O[l] (fun z : ℂ => ‖z‖) := by
    simpa only [PowerSeries.trunc_one_left,PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hG,Polynomial.eval_C,sub_zero,pow_one] using hg 1
  have hnorm : (fun z => ‖g z‖^N) =O[l] (fun z : ℂ => ‖z‖^N) := hgO.norm_left.pow N
  have hrem : (fun z => K z-(PowerSeries.trunc N F).eval (g z)) =O[l]
      (fun z : ℂ => ‖z‖^N) := by
    exact (happrox N).trans hnorm
  have hfinite : CompleteExpansion l (fun z => (PowerSeries.trunc N F).eval (g z))
      (finiteComposition N F G) := by
    have hsum := completeExpansion_sum (Finset.range N) (fun k _hk =>
      completeExpansion_mul hl (completeExpansion_const hl (PowerSeries.coeff k F))
        (completeExpansion_pow hl hg k))
    unfold finiteComposition
    convert hsum using 1
    funext z
    change Polynomial.eval₂ (RingHom.id ℂ) (g z) (PowerSeries.trunc N F)=_
    rw [PowerSeries.eval₂_trunc_eq_sum_range]
    simp only [RingHom.id_apply]
  have hsecond := hfinite N
  rw [trunc_finiteComposition hG N] at hsecond
  exact (hrem.add hsecond).congr_left (fun z => by ring)

/-- Substituting any complete zero-constant inner expansion into a complete
outer expansion preserves all orders. Neither formal series must converge. -/
theorem completeExpansion_composition
    {l l' : Filter ℂ} (hl : l ≤ 𝓝 (0:ℂ))
    {f g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hf : CompleteExpansion l' f F) (hg : CompleteExpansion l g G)
    (hG : PowerSeries.constantCoeff G=0) (ht : Tendsto g l l') :
    CompleteExpansion l (fun z => f (g z)) (formalComposition F G) := by
  apply completeExpansion_of_polynomial_approximations hl hg hG
  intro N
  have he := (hf N).comp_tendsto ht
  change (fun z => f (g z)-(PowerSeries.trunc N F).eval (g z)) =O[l] (fun z => ‖g z‖^N) at he
  exact he

#print axioms completeExpansion_of_taylor
#print axioms exists_completeExpansion_of_analyticAt
#print axioms completeExpansion_const
#print axioms completeExpansion_add
#print axioms completeExpansion_sub
#print axioms completeExpansion_mul
#print axioms completeExpansion_pow
#print axioms completeExpansion_sum
#print axioms coeff_pow_eq_zero_of_lt
#print axioms trunc_finiteComposition
#print axioms completeExpansion_of_polynomial_approximations
#print axioms completeExpansion_composition
end CRGAsymptoticCoefficientScalarAlgebra
