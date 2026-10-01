import CRGExponentialExpansionGroupsBuilder
import CRGExponentialCoefficientGroups
import CRGPolynomialKernelClearing

/-! Finite assembly of genuine endpoint packets and exponential-polynomial
heads. Distinct supporting lines can meet only at the zero exponent;
the monic head protects that exponent against all negative-power tails. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set Polynomial Asymptotics
open scoped Topology BigOperators
namespace CRGLinearKernelGroupAssembly
open CRGExponentialCoefficientGroups CRGExponentialExpansionGroupsBuilder
open CRGExponentialExpansionSector CRGPolynomialKernel
open CRGAsymptoticCoefficientQuotient CRGAsymptoticCoefficientScalarAlgebra
open CRGAsymptoticCoefficientMatrixTransfer CRGPuiseuxCoordinates
open CRGAsymptoticCoefficientRayTail
open CRGNormalFormGoal WasowGlobalRayData WasowLaurentRayEquation
variable {n : ℕ} {ι : Type*} [Fintype ι]

def head {a : Fin n → ℂ → ℂ} (E : MonicGroups a)
    (q : Polynomial ℂ) (j : Fin (n+1)) : Polynomial ℂ :=
  if q∈E.exponents then E.coeff q j else 0

def clearing {a : Fin n → ℂ → ℂ} (E : MonicGroups a) : ℕ :=
  E.exponents.sup fun q=>Finset.univ.sup fun j : Fin (n+1)=>(E.coeff q j).natDegree

theorem head_degree_le {a : Fin n → ℂ → ℂ} (E : MonicGroups a)
    (q : Polynomial ℂ) (j : Fin (n+1)) : (head E q j).natDegree≤clearing E := by
  classical
  by_cases hq : q∈E.exponents
  · simp only [head,if_pos hq,clearing]
    exact (Finset.le_sup (f:=fun j : Fin (n+1)=>(E.coeff q j).natDegree)
      (Finset.mem_univ j)).trans (Finset.le_sup
        (f:=fun q=>Finset.univ.sup fun j : Fin (n+1)=>(E.coeff q j).natDegree) hq)
  · simp [head,hq]

def phases {a : Fin n → ℂ → ℂ} (E : MonicGroups a)
    (η : ι → Polynomial ℂ) : Finset (Polynomial ℂ) :=
  E.exponents ∪ Finset.univ.image η

def retained {a : Fin n → ℂ → ℂ} (E : MonicGroups a)
    (η : ι → Polynomial ℂ) : Finset (Polynomial ℂ) := by
  classical
  exact (phases E η).filter fun q=>q=0 ∨ (∃j,head E q j≠0) ∨ ∃i,η i=q

def fiber (η : ι → Polynomial ℂ) (q : Polynomial ℂ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i=>η i=q

def amplitude {a : Fin n → ℂ → ℂ} (E : MonicGroups a)
    (η : ι → Polynomial ℂ) (U : ι → Fin (n+1) → ℂ → ℂ)
    (q : Polynomial ℂ) (j : Fin (n+1)) (x : ℂ) : ℂ :=
  (head E q j).eval (originalPoint 1 x)+∑i∈fiber η q,U i j x

def series {a : Fin n → ℂ → ℂ} (E : MonicGroups a)
    (η : ι → Polynomial ℂ) (A : ι → Fin (n+1) → PowerSeries ℂ)
    (q : Polynomial ℂ) (j : Fin (n+1)) : PowerSeries ℂ :=
  (clearedPolynomial (head E q j) 1 (clearing E) : PowerSeries ℂ)+
    PowerSeries.X^(clearing E)*(∑i∈fiber η q,A i j)

theorem exists_groups_of_packets
    {a : Fin n → ℂ → ℂ} (E : MonicGroups a)
    (b : Fin (n+1) → ℂ → ℂ) (angles : Set ℝ)
    (η : ι → Polynomial ℂ) (hη : ∀i,(η i).coeff 0=0)
    (hinj : ∀i k,η i≠0 → η i=η k → i=k)
    (U : ι → Fin (n+1) → ℂ → ℂ)
    (A : ι → Fin (n+1) → PowerSeries ℂ)
    (hA0 : ∀i j,PowerSeries.constantCoeff (A i j)=0)
    (hAn : ∀i,∃j,A i j≠0)
    (hrep : ∀θ∈angles,∀j,∀ᶠx in rayFilter (direction θ),
      b j (originalPoint 1 x)=
        (∑q∈E.exponents,Complex.exp (q.eval (originalPoint 1 x))*(E.coeff q j).eval (originalPoint 1 x))+
        ∑i,U i j x*Complex.exp ((η i).eval (originalPoint 1 x)))
    (hexp : ∀θ∈angles,∀i j,CompleteExpansion (rayFilter (direction θ)) (U i j) (A i j)) :
    ∃G : Groups b,G.denominator=1 ∧ G.clearing=clearing E ∧ G.angles=angles := by
  classical
  let S := phases E η
  let T := retained E η
  have hTS : T⊆S := Finset.filter_subset _ _
  have hS0 : (0 : Polynomial ℂ)∈S := Finset.mem_union_left _ E.zero_mem
  have hT0 : (0 : Polynomial ℂ)∈T := by
    apply Finset.mem_filter.mpr
    exact ⟨hS0,Or.inl rfl⟩
  have hphase : ∀q∈S,q.coeff 0=0 := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq|hq
    · exact E.normalized q hq
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
      exact hη i
  have hidentity (j : Fin (n+1)) (x : ℂ) :
      (∑q∈S,amplitude E η U q j x*Complex.exp (q.eval (originalPoint 1 x)))=
        (∑q∈E.exponents,Complex.exp (q.eval (originalPoint 1 x))*(E.coeff q j).eval (originalPoint 1 x))+
          ∑i,U i j x*Complex.exp ((η i).eval (originalPoint 1 x)) := by
    simp only [amplitude,add_mul,Finset.sum_add_distrib,Finset.sum_mul]
    congr 1
    · have hh : (∑q∈E.exponents,(head E q j).eval (originalPoint 1 x)*Complex.exp (q.eval (originalPoint 1 x)))=
          ∑q∈S,(head E q j).eval (originalPoint 1 x)*Complex.exp (q.eval (originalPoint 1 x)) := by
        apply Finset.sum_subset (Finset.subset_union_left)
        intro q hq hqe
        simp [head,hqe]
      rw [←hh]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [head,if_pos hq,mul_comm]
    · rw [←Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=S) (g:=η)
        (fun i hi=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
        (fun i=>U i j x*Complex.exp ((η i).eval (originalPoint 1 x)))]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro i hi
      have he : η i=q := (Finset.mem_filter.mp hi).2
      rw [he]
  have hzero : ∀q∈S,q∉T → ∀j x,amplitude E η U q j x=0 := by
    intro q hq hqt j x
    have hn : ¬(q=0 ∨ (∃j,head E q j≠0) ∨ ∃i,η i=q) := by
      intro hh
      exact hqt (Finset.mem_filter.mpr ⟨hq,hh⟩)
    have hp : head E q j=0 := by by_contra hh;exact hn (Or.inr (Or.inl ⟨j,hh⟩))
    have hf : fiber η q=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hn (Or.inr (Or.inr ⟨i,(Finset.mem_filter.mp hi).2⟩))
    simp [amplitude,hp,hf]
  have he : ∀θ∈angles,∀q∈T,∀j,CompleteExpansion (rayFilter (direction (θ/(1:ℕ))))
      (fun x=>x^(clearing E)*amplitude E η U q j x) (series E η A q j) := by
    intro θ hθ q _hq j
    simp only [Nat.cast_one,div_one]
    let l := rayFilter (direction θ)
    have hl : l≤𝓝 (0:ℂ) := (rayFilter_le_punctured (direction_ne_zero _)).trans nhdsWithin_le_nhds
    have hpun : ∀ᶠx : ℂ in 𝓝[≠] (0:ℂ),x≠0 := self_mem_nhdsWithin
    have hx : ∀ᶠx in l,x≠0 := hpun.filter_mono (rayFilter_le_punctured (direction_ne_zero _))
    have hmono : CompleteExpansion l (fun x:ℂ=>x^(clearing E)) (PowerSeries.X^(clearing E)) := by
      simpa only [Polynomial.coe_pow,Polynomial.coe_X,Polynomial.eval_pow,Polynomial.eval_X] using
        polynomial_completeExpansion hl (Polynomial.X^(clearing E))
    have ht := completeExpansion_mul hl hmono (completeExpansion_sum (fiber η q) (fun i _=>hexp θ hθ i j))
    have hh := completeExpansion_add (polynomial_completeExpansion hl (clearedPolynomial (head E q j) 1 (clearing E))) ht
    intro N
    apply (hh N).congr' ?_ EventuallyEq.rfl
    filter_upwards [hx] with x hx
    dsimp only [amplitude]
    rw [clearedPolynomial_eval (by simpa using head_degree_le E q j) hx]
    change x^clearing E*(head E q j).eval (originalPoint 1 x)+
      x^clearing E*(∑i∈fiber η q,U i j x)-_=_
    unfold series
    ring
  have hhead : ∀q∈T,∃j,series E η A q j≠0 := by
    intro q hq
    have hr := (Finset.mem_filter.mp hq).2
    have htail0 (j : Fin (n+1)) : PowerSeries.constantCoeff (∑i∈fiber η q,A i j)=0 := by
      simp only [map_sum]
      exact Finset.sum_eq_zero (fun i _=>hA0 i j)
    have hnon (j : Fin (n+1))
        (hn : head E q j≠0 ∨ (∑i∈fiber η q,A i j)≠0) : series E η A q j≠0 := by
      apply polynomial_head_tail_nonzero _ _ (clearing E)
      · intro k hk
        simpa only [Polynomial.coeff_coe] using clearedPolynomial_coeff_above (head E q j) 1 (clearing E) k hk
      · exact cleared_zero_head_coeff (htail0 j) (clearing E)
      · rcases hn with hp|ht
        · left
          intro hz
          apply clearedPolynomial_ne_zero hp (by norm_num : 0<(1:ℕ)) (by simpa using head_degree_le E q j)
          apply Polynomial.coe_injective
          simpa only [Polynomial.coe_zero] using hz
        · exact Or.inr (mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) ht)
    rcases hr with hq0|hp|⟨i,hi⟩
    · subst q
      refine ⟨Fin.last n,hnon _ (Or.inl ?_)⟩
      simp only [head,if_pos E.zero_mem,E.top]
      exact one_ne_zero
    · obtain ⟨j,hj⟩ := hp
      exact ⟨j,hnon j (Or.inl hj)⟩
    · by_cases hq0 : q=0
      · subst q
        refine ⟨Fin.last n,hnon _ (Or.inl ?_)⟩
        rw [hq0]
        simp only [head,if_pos E.zero_mem,E.top]
        exact one_ne_zero
      · obtain ⟨j,hj⟩ := hAn i
        refine ⟨j,hnon j (Or.inr ?_)⟩
        have hf : fiber η q={i} := by
          ext k
          simp only [fiber,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
          constructor
          · intro hk
            exact hinj k i (by simpa only [hk] using hq0) (hk.trans hi.symm)
          · intro hk
            simpa only [hk] using hi
        simpa only [hf,Finset.sum_singleton] using hj
  apply exists_groups b 1 (by norm_num) (clearing E) angles S T hTS ⟨0,hT0⟩ hphase
    (amplitude E η U) (series E η A) ?_ hzero he hhead
  intro θ hθ j
  simpa only [Nat.cast_one,div_one] using (hrep θ hθ j).mono (fun x hx=>hx.trans (hidentity j x).symm)

#print axioms head_degree_le
#print axioms exists_groups_of_packets
end CRGLinearKernelGroupAssembly
