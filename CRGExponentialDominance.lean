import CRGPhaseAsymptotics
import CRGExponentialCoefficients
import CRGRayComparisonOrder

/-! Dominant normalized exponential groups on almost every ray. A single
positive linear decay constant works for every nondominant group. -/
set_option autoImplicit false
noncomputable section
open Polynomial Filter Set MeasureTheory
open scoped Topology
namespace CRGExponentialDominance
open CRGNormalFormGoal CRGPhaseDirections CRGPhaseAsymptotics

theorem leading_coefficient_on_ray (P : Polynomial ℂ) (θ:ℝ) :
    (P.leadingCoeff*(Complex.exp ((θ:ℂ)*Complex.I))^P.natDegree).re =
      leadingReal P.leadingCoeff P.natDegree θ := by
  unfold leadingReal
  rw [←Complex.exp_nat_mul]
  congr 3
  push_cast
  ring

/-- A nonconstant polynomial which is eventually nonpositive and has a
nonzero real leading coefficient decreases at least linearly. -/
theorem eventually_linear_negative (P : Polynomial ℂ) (θ:ℝ)
    (hd : 0<P.natDegree) (hl : leadingReal P.leadingCoeff P.natDegree θ≠0)
    (hn : ∀ᶠr in atTop,(P.eval (ray θ r)).re≤0) :
    ∃c:ℝ,0<c ∧ ∀ᶠr in atTop,(P.eval (ray θ r)).re≤-c*r := by
  let L := leadingReal P.leadingCoeff P.natDegree θ
  have hlead : (P.leadingCoeff*(Complex.exp ((θ:ℂ)*Complex.I))^P.natDegree).re≠0 := by
    rwa [leading_coefficient_on_ray]
  have ht : Tendsto (fun r:ℝ=>(P.eval (ray θ r)).re/r^P.natDegree) atTop (𝓝 L) := by
    simpa only [ray,leading_coefficient_on_ray,L] using polynomial_normalized_limit P _ hlead
  have hL : L≤0 := le_of_tendsto ht (by
    filter_upwards [hn,eventually_ge_atTop (0:ℝ)] with r hr hr0
    exact div_nonpos_of_nonpos_of_nonneg hr (pow_nonneg hr0 _))
  have hLn : L<0 := lt_of_le_of_ne hL hl
  have hh : ∀ᶠr in atTop,(P.eval (ray θ r)).re/r^P.natDegree≤L/2 :=
    (ht.eventually (gt_mem_nhds (show L<L/2 by linarith))).mono (fun _ h=>h.le)
  refine ⟨-L/2,by linarith,?_⟩
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with r hr hr1
  have hrp : 0<r := zero_lt_one.trans_le hr1
  have hp : r≤r^P.natDegree := by
    simpa only [pow_one] using pow_le_pow_right₀ hr1 (show 1≤P.natDegree from hd)
  have hmul := (div_le_iff₀ (pow_pos hrp _)).mp hr
  calc
    (P.eval (ray θ r)).re ≤ L/2*r^P.natDegree := hmul
    _ ≤ L/2*r := mul_le_mul_of_nonpos_left hp (by linarith)
    _ = -(-L/2)*r := by ring

def GoodDirection {ι:Type*} (Q:ι→Polynomial ℂ) (θ:ℝ) : Prop :=
  ∀i j,i≠j→leadingReal (Q i-Q j).leadingCoeff (Q i-Q j).natDegree θ≠0

theorem ae_goodDirection {ι:Type*} [Fintype ι]
    (Q:ι→Polynomial ℂ) (hz:∀i,(Q i).coeff 0=0) (hQ:Function.Injective Q) :
    ∀ᵐθ:ℝ,GoodDirection Q θ := by
  have hpair (i j:ι) : ∀ᵐθ:ℝ,i≠j→
      leadingReal (Q i-Q j).leadingCoeff (Q i-Q j).natDegree θ≠0 := by
    by_cases hij:i=j
    · exact Filter.Eventually.of_forall (by simp [hij])
    · have hne:Q i≠Q j := fun he=>hij (hQ he)
      have hd := CRGExponentialCoefficients.distinct_normalized_nonconstant (hz i) (hz j) hne
      filter_upwards [leadingReal_ae_ne_zero
        (Polynomial.leadingCoeff_ne_zero.mpr (sub_ne_zero.mpr hne))
        (by exact_mod_cast hd.ne' : ((Q i-Q j).natDegree:ℝ)≠0)] with θ hθ
      exact fun _=>hθ
  have hh := ae_all_iff.mpr (fun i=>ae_all_iff.mpr (hpair i))
  exact hh

/-- The maximum group is selected once, and every other group is suppressed
by exp(-c r), with one common c>0 on one common ray tail. -/
theorem exists_dominant_group {ι:Type*} [Fintype ι] [Nonempty ι]
    (Q:ι→Polynomial ℂ) (hz:∀i,(Q i).coeff 0=0) (hQ:Function.Injective Q)
    (θ:ℝ) (hθ:GoodDirection Q θ) :
    ∃j:ι, ∃c:ℝ,0<c ∧ ∀ᶠr in atTop,∀i:ι,i≠j→
      ((Q i-Q j).eval (ray θ r)).re≤-c*r := by
  classical
  have hcomp (i j:ι) : (∀ᶠr in atTop,((Q i).eval (ray θ r)).re≤((Q j).eval (ray θ r)).re) ∨
      (∀ᶠr in atTop,((Q j).eval (ray θ r)).re≤((Q i).eval (ray θ r)).re) := by
    simpa only [phaseOnRay,WasowPolynomialPhase.rootOnRay_one] using
      CRGRayComparisonOrder.phase_eventually_comparable 1 (by omega) (Q i) (Q j) θ 0
  obtain ⟨j,_hj,hm⟩ := CRGRayComparisonOrder.finite_eventual_max Finset.univ
    Finset.univ_nonempty (fun i r=>((Q i).eval (ray θ r)).re) (fun i _ j _=>hcomp i j)
  have hci (i:ι) : ∃c:ℝ,0<c ∧ ∀ᶠr in atTop,i≠j→
      ((Q i-Q j).eval (ray θ r)).re≤-c*r := by
    by_cases hij:i=j
    · exact ⟨1,zero_lt_one,Filter.Eventually.of_forall (by simp [hij])⟩
    · have hne : Q i≠Q j := fun he=>hij (hQ he)
      obtain ⟨c,hc,hdec⟩ := eventually_linear_negative (Q i-Q j) θ
        (CRGExponentialCoefficients.distinct_normalized_nonconstant (hz i) (hz j) hne)
        (hθ i j hij) (by
          filter_upwards [hm] with r hr
          simpa only [eval_sub,Complex.sub_re,sub_nonpos] using hr i (Finset.mem_univ i))
      exact ⟨c,hc,hdec.mono (fun _ hr _=>hr)⟩
  choose c hc hdec using hci
  let s := Finset.univ.image c
  have hs:s.Nonempty := Finset.univ_nonempty.image c
  let C := s.min' hs
  have hC : 0<C := by
    obtain ⟨i,_hi,he⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
    dsimp [C]
    rw [←he]
    exact hc i
  have hCi (i:ι) : C≤c i := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  refine ⟨j,C,hC,?_⟩
  filter_upwards [Filter.eventually_all.mpr hdec,eventually_ge_atTop (0:ℝ)] with r hr hr0
  intro i hij
  exact (hr i hij).trans (mul_le_mul_of_nonneg_right (neg_le_neg (hCi i)) hr0)

theorem ae_exists_dominant_group {ι:Type*} [Fintype ι] [Nonempty ι]
    (Q:ι→Polynomial ℂ) (hz:∀i,(Q i).coeff 0=0) (hQ:Function.Injective Q) :
    ∀ᵐθ:ℝ,∃j:ι,∃c:ℝ,0<c ∧ ∀ᶠr in atTop,∀i:ι,i≠j→
      ((Q i-Q j).eval (ray θ r)).re≤-c*r := by
  filter_upwards [ae_goodDirection Q hz hQ] with θ hθ
  exact exists_dominant_group Q hz hQ θ hθ

#print axioms leading_coefficient_on_ray
#print axioms eventually_linear_negative
#print axioms ae_goodDirection
#print axioms exists_dominant_group
#print axioms ae_exists_dominant_group
end CRGExponentialDominance
