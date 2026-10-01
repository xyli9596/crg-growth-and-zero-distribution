import LevinGrid

/-! Finite assembly of genuine local disk families. Dependent finite local
index sets are reindexed by a single `Fin m`, preserving the exact radius sum. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Metric Real Complex
open scoped Topology
namespace LevinFiniteCover

/-- Concatenate finite local disk families over a finite covering index set. -/
theorem combine_finite_covers {ι : Type*} [Fintype ι] {P : ℂ → Prop}
    (q : ι → ℂ) (τ B : ℝ) (A : Set ℂ)
    (hcover : ∀ z ∈ A, ∃ i : ι, ‖z - q i‖ ≤ τ)
    (hlocal : ∀ i : ι, ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ r : Fin m → ℝ,
      (∀ k, 0 ≤ r k) ∧ (∑ k, r k) ≤ B ∧
      ∀ z : ℂ, ‖z - q i‖ ≤ τ →
        (∀ k, z ∉ ball (c k) (r k)) → P z) :
    ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ r : Fin m → ℝ,
      (∀ k, 0 ≤ r k) ∧ (∑ k, r k) ≤ (Fintype.card ι : ℝ) * B ∧
      ∀ z ∈ A, (∀ k, z ∉ ball (c k) (r k)) → P z := by
  classical
  choose m c r hr hsum hgood using hlocal
  let I := (i : ι) × Fin (m i)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let C : Fin (Fintype.card I) → ℂ := fun k => c (e k).1 (e k).2
  let R : Fin (Fintype.card I) → ℝ := fun k => r (e k).1 (e k).2
  have htotal : (∑ k, R k) = ∑ i : ι, ∑ j : Fin (m i), r i j := by
    calc
      _ = ∑ p : I, r p.1 p.2 := e.sum_comp (fun p : I => r p.1 p.2)
      _ = _ := Fintype.sum_sigma _
  refine ⟨Fintype.card I, C, R, fun k => hr (e k).1 (e k).2, ?_, ?_⟩
  · rw [htotal]
    exact (Finset.sum_le_sum (fun i _ => hsum i)).trans_eq (by simp)
  · intro z hz hout
    obtain ⟨i, hi⟩ := hcover z hz
    apply hgood i z hi
    intro j
    have hb := hout (e.symm ⟨i, j⟩)
    change z ∉ ball (c (e (e.symm ⟨i, j⟩)).1 (e (e.symm ⟨i, j⟩)).2)
      (r (e (e.symm ⟨i, j⟩)).1 (e (e.symm ⟨i, j⟩)).2) at hb
    have he : e (e.symm ⟨i, j⟩) = (⟨i, j⟩ : I) := e.apply_symm_apply _
    rw [he] at hb
    exact hb

/-- A perturbed quadratic grid combines all local Cartan disk certificates.
The radius cost `1000 * η / δ` is explicit and uniform in the mesh. -/
theorem combine_annular_local_disks {P : ℂ → Prop} {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (Γ : Finset ℂ)
    (hcard : (Γ.card : ℝ) * δ ^ 2 ≤ 100)
    (hcover : ∀ z : ℂ, ‖z‖ ∈ Icc (1 : ℝ) 2 → ∃ c ∈ Γ, ‖z - c‖ ≤ δ)
    (q : Γ → ℂ) (hq : ∀ c : Γ, ‖q c - (c : ℂ)‖ ≤ δ)
    (hlocal : ∀ i : Γ, ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ r : Fin m → ℝ,
      (∀ k, 0 ≤ r k) ∧ (∑ k, r k) ≤ 10 * η * δ ∧
      ∀ z : ℂ, ‖z - q i‖ ≤ 2 * δ →
        (∀ k, z ∉ ball (c k) (r k)) → P z) :
    ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ r : Fin m → ℝ,
      (∀ k, 0 ≤ r k) ∧ (∑ k, r k) ≤ 1000 * η / δ ∧
      ∀ z : ℂ, ‖z‖ ∈ Icc (1 : ℝ) 2 →
        (∀ k, z ∉ ball (c k) (r k)) → P z := by
  have hcover' : ∀ z ∈ {z : ℂ | ‖z‖ ∈ Icc (1 : ℝ) 2}, ∃ i : Γ, ‖z - q i‖ ≤ 2 * δ := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := hcover z hz
    refine ⟨⟨c, hc⟩, ?_⟩
    have htri := dist_triangle z c (q ⟨c, hc⟩)
    simp only [dist_eq_norm] at htri
    have hq' := hq ⟨c, hc⟩
    rw [norm_sub_rev] at hq'
    linarith
  obtain ⟨m, c, r, hr, hsum, hgood⟩ :=
    combine_finite_covers q (2 * δ) (10 * η * δ)
      {z : ℂ | ‖z‖ ∈ Icc (1 : ℝ) 2} hcover' hlocal
  refine ⟨m, c, r, hr, hsum.trans ?_, hgood⟩
  rw [Fintype.card_coe]
  apply (le_div_iff₀ hδ).mpr
  have hb := mul_le_mul_of_nonneg_right hcard (show 0 ≤ 10 * η by positivity)
  nlinarith

#print axioms combine_finite_covers
#print axioms combine_annular_local_disks
end LevinFiniteCover
