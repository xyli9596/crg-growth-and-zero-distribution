import CRGPuiseuxAngularCells
import CRGPuiseuxBranchSector
import CRGPolynomialKernelCells

/-! The finite geometry packets of the polynomial-kernel corollary are
constructed from its actual source phases and common power ramification. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial Asymptotics MeasureTheory
open scoped Topology
namespace CRGPuiseuxPolynomialKernelCells
open CRGNormalFormGoal CRGPhaseDirections CRGPolynomialKernel
open CRGExponentialCoefficients CRGPuiseuxCoordinates CRGPuiseuxBranchSector
open CRGPuiseuxPolynomialCone CRGAsymptoticCoefficientRayTail
open WasowGlobalRayData WasowLaurentRayEquation

theorem normalized_degree_leading (Q : Polynomial ℂ) (hd : 0<Q.natDegree) :
    (normalizedExponent Q).natDegree=Q.natDegree ∧
      (normalizedExponent Q).leadingCoeff=Q.leadingCoeff := by
  have hdeg : (normalizedExponent Q).natDegree=Q.natDegree :=
    Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simpa only [Polynomial.natDegree_C] using hd)
  refine ⟨hdeg,?_⟩
  rw [Polynomial.leadingCoeff,hdeg]
  simp only [normalizedExponent,Polynomial.coeff_sub,Polynomial.coeff_C,if_neg hd.ne',
    sub_zero,Polynomial.coeff_natDegree]

theorem local_ray_geometry (Q : Polynomial ℂ) (p : ℕ) (hp : 0<p) (θ : ℝ)
    (hd : 0<Q.natDegree) (hL : 0<leadingReal Q.leadingCoeff Q.natDegree θ) :
    Tendsto (fun x : ℂ=>‖Q.eval (originalPoint p x)‖) (rayFilter (direction (θ/p))) atTop ∧
    ∃c : ℝ,0<c ∧ ∀ᶠx in rayFilter (direction (θ/p)),
      c*‖Q.eval (originalPoint p x)‖≤(Q.eval (originalPoint p x)).re := by
  obtain ⟨c,hc,hcone,ht⟩ := positive_ray_cone Q θ hd hL
  have hpow : Tendsto (fun s : ℝ=>s^p) atTop atTop := tendsto_pow_atTop hp.ne'
  refine ⟨?_,c,hc,?_⟩
  · change Tendsto (fun s : ℝ=>‖Q.eval (originalPoint p (inverseRay (direction (θ/p)) s))‖) atTop atTop
    have hh := ht.comp hpow
    change Tendsto (fun s : ℝ=>‖Q.eval (ray θ (s^p))‖) atTop atTop at hh
    simpa only [originalPoint_inverseRay p hp] using hh
  · change ∀ᶠs : ℝ in atTop,c*‖Q.eval (originalPoint p (inverseRay (direction (θ/p)) s))‖≤
      (Q.eval (originalPoint p (inverseRay (direction (θ/p)) s))).re
    simpa only [originalPoint_inverseRay p hp] using hpow.eventually hcone

def AngularIndex {n : ℕ} (D : CoefficientData n) :=
  CRGPuiseuxAngularCells.Cell (CRGPuiseuxAngularCells.phaseCutFinset D.phase D.phase_nonconstant)

instance {n : ℕ} (D : CoefficientData n) : Fintype (AngularIndex D) := by
  unfold AngularIndex
  infer_instance

theorem exists_geometry_cell {n : ℕ} (D : CoefficientData n) (C : AngularIndex D) :
    ∃K : CRGPolynomialKernel.Cell D,K.angles=C.angles ∧ K.denominator=D.ramification := by
  classical
  let positive (ell : Fin D.count) :=
    ∀θ∈C.angles,0<leadingReal (D.phase ell).leadingCoeff (D.phase ell).natDegree θ
  let grow (ell : Fin D.count) : Bool := decide (positive ell)
  have hgrow (ell : Fin D.count) (hg : grow ell=true) : positive ell := of_decide_eq_true hg
  have hdecay (ell : Fin D.count) (hg : grow ell=false) :
      ∀θ∈C.angles,leadingReal (D.phase ell).leadingCoeff (D.phase ell).natDegree θ<0 := by
    have hn : ¬positive ell := of_decide_eq_false hg
    exact (CRGPuiseuxAngularCells.leading_sign_on_cell D.phase D.phase_nonconstant C ell).resolve_left hn
  have hroots : ∀ell : Fin D.count,∃g : ℂ → ℂ,
      (grow ell=false → AnalyticAt ℂ g 0 ∧ g 0=0 ∧
        ∀θ∈C.angles,∀ᶠx in rayFilter (direction (θ/D.ramification)),
          g x=(-(D.phase ell).eval (originalPoint D.ramification x))^(-(D.power ell:ℂ)⁻¹)) := by
    intro ell
    by_cases hg : grow ell=false
    · let Q := -(D.phase ell)
      have hd : 0<Q.natDegree := by simpa only [Q,Polynomial.natDegree_neg] using D.phase_nonconstant ell
      have hQ : Q≠0 := by intro hz;simpa only [hz,Polynomial.natDegree_zero,lt_self_iff_false] using hd
      have hdiv : D.power ell ∣ D.ramification*Q.natDegree :=
        (D.power_dvd_ramification ell).mul_right _
      have hL : ∀θ∈Ioo C.left C.right,0<leadingReal Q.leadingCoeff Q.natDegree θ := by
        intro θ hθ
        simpa only [Q,Polynomial.leadingCoeff_neg,Polynomial.natDegree_neg,leadingReal,
          neg_mul,Complex.neg_re] using neg_pos.mpr (hdecay ell hg θ hθ)
      obtain ⟨η,hη,hbranch⟩ := exists_fixed_principal_root_factor Q hQ hd D.ramification
        (D.power ell) D.ramification_positive (D.power_positive ell) hdiv C.left C.right C.property.1 hL
      refine ⟨fun x=>η*inversePhaseRoot Q D.ramification (D.power ell) x,fun _=>⟨?_,?_,?_⟩⟩
      · exact analyticAt_const.mul (analyticAt_inversePhaseRoot hQ D.ramification_positive _)
      · change η*inversePhaseRoot Q D.ramification (D.power ell) 0=0
        rw [inversePhaseRoot_zero hd D.ramification_positive (D.power_positive ell) hdiv,mul_zero]
      · intro θ hθ
        change ∀ᶠs : ℝ in atTop,η*inversePhaseRoot Q D.ramification (D.power ell)
          (inverseRay (direction (θ/D.ramification)) s)=
          (-(D.phase ell).eval (originalPoint D.ramification (inverseRay (direction (θ/D.ramification)) s)))^(-(D.power ell:ℂ)⁻¹)
        exact (hbranch θ hθ).mono (fun _ he=>by simpa only [Q,Polynomial.eval_neg] using he.symm)
    · exact ⟨fun _=>0,fun h=>False.elim (hg h)⟩
  choose root hroot using hroots
  refine ⟨{
    denominator := D.ramification
    positive := D.ramification_positive
    angles := C.angles
    growing := grow
    root := root
    root_analytic := fun ell hg=>(hroot ell hg).1
    root_zero := fun ell hg=>(hroot ell hg).2.1
    growing_geometry := ?_
    decaying_geometry := ?_},rfl,rfl⟩
  · intro ell hg θ hθ
    have he := normalized_degree_leading (D.phase ell) (D.phase_nonconstant ell)
    exact local_ray_geometry (normalizedExponent (D.phase ell)) D.ramification D.ramification_positive θ
      (normalizedExponent_nonconstant (D.phase_nonconstant ell))
      (by simpa only [he.1,he.2] using hgrow ell hg θ hθ)
  · intro ell hg θ hθ
    have hL : 0<leadingReal (-(D.phase ell)).leadingCoeff (-(D.phase ell)).natDegree θ := by
      simpa only [Polynomial.leadingCoeff_neg,Polynomial.natDegree_neg,leadingReal,
        neg_mul,Complex.neg_re] using neg_pos.mpr (hdecay ell hg θ hθ)
    have hgeom := local_ray_geometry (-(D.phase ell)) D.ramification D.ramification_positive θ
      (by simpa only [Polynomial.natDegree_neg] using D.phase_nonconstant ell) hL
    exact ⟨by simpa only [Polynomial.eval_neg] using hgeom.1,
      by simpa only [Polynomial.eval_neg] using hgeom.2,(hroot ell hg).2.2 θ hθ⟩

/-- Finitely many source-derived geometric cells cover the argument window
almost everywhere. Every decaying root has one fixed analytic germ. -/
theorem exists_finite_geometry_cells {n : ℕ} (D : CoefficientData n) :
    ∃K : AngularIndex D → CRGPolynomialKernel.Cell D,
      (∀C,(K C).angles=C.angles) ∧ (∀C,(K C).denominator=D.ramification) ∧
      ∀ᵐθ : ℝ,θ∈Icc 0 (2*Real.pi) → ∃C,θ∈(K C).angles := by
  choose K hK using exists_geometry_cell D
  refine ⟨K,fun C=>(hK C).1,fun C=>(hK C).2,?_⟩
  filter_upwards [CRGPuiseuxAngularCells.ae_phase_cell D.phase D.phase_nonconstant] with θ hθ
  intro hw
  obtain ⟨C,hC⟩ := hθ hw
  exact ⟨C,by simpa only [(hK C).1] using hC⟩

#print axioms normalized_degree_leading
#print axioms local_ray_geometry
#print axioms exists_geometry_cell
#print axioms exists_finite_geometry_cells
end CRGPuiseuxPolynomialKernelCells
