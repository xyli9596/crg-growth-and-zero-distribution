import CRGPuiseuxAngularCells
import CRGPuiseuxPolynomialKernelCells
import CRGLinearKernelLineEndpoints

/-! Finite source-derived sign cells for the genuine supporting-line
packets of Corollary 5.2. Each cell fixes its selected endpoint on every
line before any ray or ODE solution is chosen. -/
set_option autoImplicit false
noncomputable section
open Filter Set Polynomial Asymptotics MeasureTheory
open scoped Topology
namespace CRGPuiseuxLinearKernelCells
open CRGNormalFormGoal CRGPhaseDirections CRGLinearKernel
open CRGLinearKernelLineEndpoints CRGLinearKernelLinePackets CRGLinearKernelLines
open CRGLinearKernelLineGeometry CRGPuiseuxCoordinates
open CRGPuiseuxPolynomialKernelCells CRGPuiseuxPolynomialCone
open CRGAsymptoticCoefficientRayTail WasowGlobalRayData WasowLaurentRayEquation
variable {n : ℕ}

abbrev LineIndex (D : CoefficientData n) := {q : ℂ // q∈activeLines D}

theorem activeLine_representation (D : CoefficientData n) (q : LineIndex D) :
    ∃ell : Fin D.count,line (D.slope ell)=q.val := by
  have hlines := ((mem_activeLines D q.val).mp q.property).1
  exact Finset.mem_image.mp hlines |>.imp (fun _ h=>h.2)

theorem activeLine_ne_zero (D : CoefficientData n) (q : LineIndex D) : q.val≠0 := by
  obtain ⟨ell,he⟩ := activeLine_representation D q
  rw [←he]
  exact line_ne_zero _

def slopePhase (D : CoefficientData n) (q : LineIndex D) : Polynomial ℂ := Polynomial.C q.val*Polynomial.X

theorem slopePhase_degree (D : CoefficientData n) (q : LineIndex D) : (slopePhase D q).natDegree=1 :=
  Polynomial.natDegree_C_mul_X q.val (activeLine_ne_zero D q)

theorem slopePhase_leading (D : CoefficientData n) (q : LineIndex D) : (slopePhase D q).leadingCoeff=q.val := by
  rw [Polynomial.leadingCoeff,slopePhase_degree]
  simp only [slopePhase,Polynomial.coeff_C_mul_X,ite_true]

structure Cell (D : CoefficientData n) where
  angles : Set ℝ
  upper : LineIndex D → Bool
  norm_escape : ∀q : LineIndex D,∀θ∈angles,
    Tendsto (fun x : ℂ=>‖q.val*originalPoint 1 x‖) (rayFilter (direction θ)) atTop
  upper_cone : ∀q : LineIndex D,upper q=true → ∀θ∈angles,
    ∃c : ℝ,0<c ∧ ∀ᶠx in rayFilter (direction θ),c*‖q.val*originalPoint 1 x‖≤
      (q.val*originalPoint 1 x).re
  lower_cone : ∀q : LineIndex D,upper q=false → ∀θ∈angles,
    ∃c : ℝ,0<c ∧ ∀ᶠx in rayFilter (direction θ),c*‖q.val*originalPoint 1 x‖≤
      -(q.val*originalPoint 1 x).re

def Cell.endpoint {D : CoefficientData n} (C : Cell D) (q : LineIndex D) : ℝ :=
  if C.upper q then upperEnd D q.val else lowerEnd D q.val

def Cell.phase {D : CoefficientData n} (C : Cell D) (q : LineIndex D) : Polynomial ℂ :=
  Polynomial.C (q.val*(C.endpoint q:ℂ))*Polynomial.X

theorem Cell.phase_normalized {D : CoefficientData n} (C : Cell D) (q : LineIndex D) :
    (C.phase q).coeff 0=0 := by simp [Cell.phase,Polynomial.coeff_C_mul_X]

theorem Cell.phase_eval {D : CoefficientData n} (C : Cell D) (q : LineIndex D) (z : ℂ) :
    (C.phase q).eval z=(q.val*z)*(C.endpoint q:ℂ) := by
  simp only [Cell.phase,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  ring

/-- Selected endpoints of two genuine distinct supporting lines can
coincide only at zero. -/
theorem Cell.endpoint_coefficient_injective {D : CoefficientData n} (C : Cell D)
    {q r : LineIndex D}
    (he : q.val*(C.endpoint q:ℂ)=r.val*(C.endpoint r:ℂ))
    (hne : q.val*(C.endpoint q:ℂ)≠0) : q=r := by
  obtain ⟨ell,hq⟩ := activeLine_representation D q
  obtain ⟨ell',hr⟩ := activeLine_representation D r
  apply Subtype.ext
  rw [←hq,←hr]
  apply line_eq_of_nonzero_intersection (s:=C.endpoint q) (t:=C.endpoint r)
  · simpa only [hq,hr] using he
  · simpa only [hq] using hne

theorem Cell.phase_injective_away_zero {D : CoefficientData n} (C : Cell D)
    {q r : LineIndex D} (he : C.phase q=C.phase r) (hne : C.phase q≠0) : q=r := by
  have hcoef := congrArg (fun P : Polynomial ℂ=>P.coeff 1) he
  simp only [Cell.phase,Polynomial.coeff_C_mul_X,if_pos rfl] at hcoef
  apply C.endpoint_coefficient_injective hcoef
  intro hz
  apply hne
  simp only [Cell.phase,hz,Polynomial.C_0,zero_mul]

def AngularIndex (D : CoefficientData n) :=
  CRGPuiseuxAngularCells.Cell (CRGPuiseuxAngularCells.phaseCutFinset (slopePhase D)
    (fun q=>by rw [slopePhase_degree];norm_num))

instance (D : CoefficientData n) : Fintype (AngularIndex D) := by
  unfold AngularIndex
  infer_instance

theorem exists_cell (D : CoefficientData n) (A : AngularIndex D) :
    ∃C : Cell D,C.angles=A.angles := by
  classical
  let positive (q : LineIndex D) := ∀θ∈A.angles,0<leadingReal q.val 1 θ
  let up (q : LineIndex D) : Bool := decide (positive q)
  have hpos (q : LineIndex D) (hu : up q=true) : positive q := of_decide_eq_true hu
  have hneg (q : LineIndex D) (hu : up q=false) : ∀θ∈A.angles,leadingReal q.val 1 θ<0 := by
    have hn : ¬positive q := of_decide_eq_false hu
    have hsign := CRGPuiseuxAngularCells.leading_sign_on_cell (slopePhase D)
      (fun q=>by rw [slopePhase_degree];norm_num) A q
    simp only [slopePhase_degree,slopePhase_leading,Nat.cast_one] at hsign
    exact hsign.resolve_left hn
  have hgeom (q : LineIndex D) (θ : ℝ) (hθ : θ∈A.angles) :
      Tendsto (fun x : ℂ=>‖q.val*originalPoint 1 x‖) (rayFilter (direction θ)) atTop ∧
      (up q=true → ∃c : ℝ,0<c ∧ ∀ᶠx in rayFilter (direction θ),
        c*‖q.val*originalPoint 1 x‖≤(q.val*originalPoint 1 x).re) ∧
      (up q=false → ∃c : ℝ,0<c ∧ ∀ᶠx in rayFilter (direction θ),
        c*‖q.val*originalPoint 1 x‖≤-(q.val*originalPoint 1 x).re) := by
    by_cases hu : up q=true
    · have hh := local_ray_geometry (slopePhase D q) 1 zero_lt_one θ
        (by rw [slopePhase_degree];norm_num)
        (by simpa only [slopePhase_degree,slopePhase_leading,Nat.cast_one] using hpos q hu θ hθ)
      simp only [slopePhase,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,div_one,Nat.cast_one] at hh
      exact ⟨hh.1,fun _=>hh.2,fun hf=>False.elim (Bool.noConfusion (hu.symm.trans hf))⟩
    · have hf : up q=false := Bool.eq_false_iff.mpr hu
      have hL : 0<leadingReal (-(slopePhase D q)).leadingCoeff (-(slopePhase D q)).natDegree θ := by
        simpa only [Polynomial.leadingCoeff_neg,Polynomial.natDegree_neg,slopePhase_degree,
          slopePhase_leading,Nat.cast_one,leadingReal,neg_mul,Complex.neg_re] using neg_pos.mpr (hneg q hf θ hθ)
      have hh := local_ray_geometry (-(slopePhase D q)) 1 zero_lt_one θ
        (by rw [Polynomial.natDegree_neg,slopePhase_degree];norm_num) hL
      simp only [Polynomial.eval_neg,norm_neg,slopePhase,Polynomial.eval_mul,Polynomial.eval_C,
        Polynomial.eval_X,Complex.neg_re,div_one,Nat.cast_one] at hh
      exact ⟨hh.1,fun ht=>False.elim (hu ht),fun _=>hh.2⟩
  refine ⟨{
    angles := A.angles
    upper := up
    norm_escape := fun q θ hθ=>(hgeom q θ hθ).1
    upper_cone := fun q hu θ hθ=>(hgeom q θ hθ).2.1 hu
    lower_cone := fun q hu θ hθ=>(hgeom q θ hθ).2.2 hu},rfl⟩

theorem exists_finite_cells (D : CoefficientData n) :
    ∃C : AngularIndex D → Cell D,(∀A,(C A).angles=A.angles) ∧
      ∀ᵐθ : ℝ,θ∈Icc 0 (2*Real.pi) → ∃A,θ∈(C A).angles := by
  choose C hC using exists_cell D
  refine ⟨C,hC,?_⟩
  filter_upwards [CRGPuiseuxAngularCells.ae_phase_cell (slopePhase D)
    (fun q=>by rw [slopePhase_degree];norm_num)] with θ hθ
  intro hw
  obtain ⟨A,hA⟩ := hθ hw
  exact ⟨A,by simpa only [hC A] using hA⟩

#print axioms activeLine_ne_zero
#print axioms Cell.phase_injective_away_zero
#print axioms exists_cell
#print axioms exists_finite_cells
end CRGPuiseuxLinearKernelCells
