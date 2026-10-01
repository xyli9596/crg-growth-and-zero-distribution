import WasowPhaseOrdering

/-! A fixed index attains the eventual maximum of a finite family of actual
Puiseux phases on a ray. Purely imaginary phase differences are allowed. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace CRGRayComparisonOrder
open CRGNormalFormGoal WasowPhaseOrdering

theorem eventually_eval_sign (P : Polynomial ℝ) :
    (∀ᶠr:ℝ in atTop, 0 ≤ P.eval r) ∨ (∀ᶠr:ℝ in atTop, P.eval r ≤ 0) := by
  rcases le_or_gt 0 P.leadingCoeff with h | h
  · exact Or.inl (eventually_eval_nonneg P h)
  · exact Or.inr (by simpa using eventually_eval_nonneg (-P) (by simpa using h.le))

theorem phase_eventually_comparable (p : ℕ) (hp : 0<p)
    (G H : Polynomial ℂ) (θ : ℝ) (ℓ : Fin p) :
    (∀ᶠr:ℝ in atTop, (phaseOnRay p G θ ℓ r).re ≤ (phaseOnRay p H θ ℓ r).re) ∨
    (∀ᶠr:ℝ in atTop, (phaseOnRay p H θ ℓ r).re ≤ (phaseOnRay p G θ ℓ r).re) := by
  let c : ℂ := Complex.exp (((θ+2*Real.pi*(ℓ:ℝ))/(p:ℝ):ℝ)*Complex.I)
  have he (r:ℝ) : (realPhasePolynomial (H-G) c).eval (r^(1/(p:ℝ))) =
      (phaseOnRay p H θ ℓ r).re - (phaseOnRay p G θ ℓ r).re := by
    rw [eval_realPhasePolynomial, eval_sub, Complex.sub_re]
    rfl
  have ht := tendsto_rpow_atTop (one_div_pos.mpr (by exact_mod_cast hp) : 0<1/(p:ℝ))
  rcases eventually_eval_sign (realPhasePolynomial (H-G) c) with h | h
  · exact Or.inl (by simpa only [he, sub_nonneg] using ht.eventually h)
  · exact Or.inr (by simpa only [he, sub_nonpos] using ht.eventually h)

/-- Finiteness and pairwise eventual comparison select one fixed maximizer. -/
theorem finite_eventual_max {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (q : ι → ℝ → ℝ)
    (h : ∀i∈s, ∀j∈s,
      (∀ᶠr in atTop, q i r ≤ q j r) ∨ (∀ᶠr in atTop, q j r ≤ q i r)) :
    ∃j∈s, ∀ᶠr in atTop, ∀i∈s, q i r ≤ q j r := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    by_cases hse : s.Nonempty
    · obtain ⟨j,hj,hm⟩ := ih hse (fun i hi j hj => h i (Finset.mem_insert_of_mem hi)
        j (Finset.mem_insert_of_mem hj))
      rcases h a (Finset.mem_insert_self ..) j (Finset.mem_insert_of_mem hj) with hjbig | habig
      · refine ⟨j,Finset.mem_insert_of_mem hj,?_⟩
        filter_upwards [hm,hjbig] with r hr har
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact har
        · exact hr i hi
      · refine ⟨a,Finset.mem_insert_self ..,?_⟩
        filter_upwards [hm,habig] with r hr har
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact le_rfl
        · exact (hr i hi).trans har
    · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hse
      subst s
      exact ⟨a,by simp,Filter.Eventually.of_forall (by simp)⟩

theorem exists_dominant_phase {m : ℕ} (p : ℕ) (hp : 0<p)
    (G : Fin m → Polynomial ℂ) (θ : ℝ) (ℓ : Fin p)
    (c : Fin m → ℂ) (hc : c≠0) :
    ∃j : Fin m, c j≠0 ∧ ∀ᶠr in atTop, ∀i, c i≠0 →
      (phaseOnRay p (G i) θ ℓ r).re ≤ (phaseOnRay p (G j) θ ℓ r).re := by
  classical
  have hn : (Finset.univ.filter (fun i=>c i≠0)).Nonempty := by
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hc
    exact ⟨i,by simpa using hi⟩
  obtain ⟨j,hj,hm⟩ := finite_eventual_max (Finset.univ.filter (fun i=>c i≠0)) hn
    (fun i r=>(phaseOnRay p (G i) θ ℓ r).re)
    (fun i _ j _=>phase_eventually_comparable p hp (G i) (G j) θ ℓ)
  exact ⟨j,by simpa using hj,by simpa using hm⟩

#print axioms eventually_eval_sign
#print axioms phase_eventually_comparable
#print axioms finite_eventual_max
#print axioms exists_dominant_phase
end CRGRayComparisonOrder
