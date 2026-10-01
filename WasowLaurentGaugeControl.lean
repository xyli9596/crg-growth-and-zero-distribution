import WasowLaurentRayEquation
import WasowPolynomialTail
import WasowLaurentExactAssemblyData

/-! The actual finite Laurent gauge supplies polynomial control, true inverse
identities and real-ray derivatives needed for final Volterra assembly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology Matrix.Norms.Operator
namespace WasowLaurentGaugeControl
open WasowLaurentGauge WasowLaurentTruncation WasowLaurentFiniteRealization
open WasowLaurentRayEquation
variable {m : ℕ}

def rayGauge (h : ℕ) (G H : Matrix (Fin m) (Fin m) L) (k : ℕ) (u : ℂ) :
    ℝ → Matrix (Fin m) (Fin m) ℂ := onRay (gauge h G H k) u

def rayInverse (h : ℕ) (G H : Matrix (Fin m) (Fin m) L) (k : ℕ) (u : ℂ) :
    ℝ → Matrix (Fin m) (Fin m) ℂ := fun r => (rayGauge h G H k u r)⁻¹

/-- The growth exponent is fixed by the full formal inverse pair, before the
truncation order or direction. The constant and radius may depend on them. -/
theorem exists_control (G H : Matrix (Fin m) (Fin m) L)
    (hGH : G*H=1) (hHG : H*G=1) (h k : ℕ) (hh : 0<h)
    {u : ℂ} (hu : ‖u‖=1) :
    ∃ ctrl : WasowPolynomialTail.Control (rayGauge h G H k u)
      (rayInverse h G H k u) (poleOrder G+poleOrder H),
      (∀ r>ctrl.R, ∀ i j, HasDerivAt (fun t => rayGauge h G H k u t i j)
        (deriv (rayGauge h G H k u) r i j) r) ∧
      (∀ r>ctrl.R, rayInverse h G H k u r * rayGauge h G H k u r=1) ∧
      (∀ r>ctrl.R, rayGauge h G H k u r * rayInverse h G H k u r=1) := by
  have hN : poleOrder G+poleOrder H < truncationOrder h G H k := by
    unfold truncationOrder
    omega
  obtain ⟨C,hC,hb⟩ := WasowLaurentInverse.eventually_inverse_bounds_of_laurent G H
    hGH hHG (truncationOrder h G H k) hN
  have hi := WasowLaurentInverse.eventually_inverse_continuousAt (cleared G) (cleared H)
    (poleOrder G) (poleOrder H) (truncationOrder h G H k) (cleared_mul G H hGH) hN
  have hune : u≠0 := by intro he; simp [he] at hu
  have ht := WasowLaurentTail.ray_tendsto_punctured hune
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp (ht.eventually (hb.and hi))
  let R := max 1 R₀
  have hR : 1≤R := le_max_left _ _
  have htail (r : ℝ) (hr : R≤r) := hR₀ r ((le_max_right _ _).trans hr)
  have hder (r : ℝ) (hr : R≤r) : DifferentiableAt ℝ (rayGauge h G H k u) r :=
    (finiteGauge_onRay_hasDerivAt h G H k hune
      (ne_of_gt (zero_lt_one.trans_le (hR.trans hr)))).differentiableAt
  have htcont : ContinuousOn (rayGauge h G H k u) (Ici R) :=
    fun r hr => (hder r hr).continuousAt.continuousWithinAt
  have hscont : ContinuousOn (rayInverse h G H k u) (Ici R) := by
    intro r hr
    have hrne := ne_of_gt (zero_lt_one.trans_le (hR.trans hr))
    have hc := (inverseRay_hasDerivAt u hrne).continuousAt
    have hcont : ContinuousAt (rayInverse h G H k u) r :=
      ContinuousAt.comp (f := inverseRay u) (x := r) (htail r hr).2 hc
    exact hcont.continuousWithinAt
  have hbound (r : ℝ) (hr : R≤r) :
      ‖rayGauge h G H k u r‖ ≤ C*r^(poleOrder G+poleOrder H) ∧
      ‖rayInverse h G H k u r‖ ≤ C*r^(poleOrder G+poleOrder H) := by
    have hr1 := hR.trans hr
    have hb' := (htail r hr).1
    have hG : ‖rayGauge h G H k u r‖ ≤ C*r^poleOrder G := by
      simpa only [rayGauge,WasowLaurentFiniteRealization.gauge,onRay,inverseRay,norm_mul,hu,one_mul,norm_inv,Complex.norm_real,
        Real.norm_of_nonneg (zero_le_one.trans hr1),inv_pow,div_inv_eq_mul] using hb'.2.2.2.1
    have hH : ‖rayInverse h G H k u r‖ ≤ C*r^poleOrder H := by
      simpa only [rayInverse,rayGauge,WasowLaurentFiniteRealization.gauge,onRay,inverseRay,norm_mul,hu,one_mul,norm_inv,Complex.norm_real,
        Real.norm_of_nonneg (zero_le_one.trans hr1),inv_pow,div_inv_eq_mul] using hb'.2.2.2.2
    constructor
    · exact hG.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 (by omega)) hC.le)
    · exact hH.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 (by omega)) hC.le)
  let ctrl : WasowPolynomialTail.Control (rayGauge h G H k u)
      (rayInverse h G H k u) (poleOrder G+poleOrder H) := {
    C := C, C_pos := hC, R := R, R_one := hR
    T_continuous := htcont, S_continuous := hscont
    T_bound := fun r hr => (hbound r hr).1
    S_bound := fun r hr => (hbound r hr).2 }
  refine ⟨ctrl,?_,?_,?_⟩
  · intro r hr i j
    exact hasDerivAt_pi.mp (hasDerivAt_pi.mp (hder r hr.le).hasDerivAt i) j
  · intro r hr
    exact (htail r hr.le).1.2.1
  · intro r hr
    exact (htail r hr.le).1.2.2.1

/-- The genuine finite Laurent gauge automatically supplies the concrete
analytic input type of exact Volterra assembly. -/
theorem exists_finiteGauge (G H : Matrix (Fin m) (Fin m) L)
    (hGH : G*H=1) (hHG : H*G=1) (h k : ℕ) (hh : 0<h)
    {u : ℂ} (hu : ‖u‖=1) :
    Nonempty (WasowLaurentExactAssembly.FiniteGauge (rayGauge h G H k u)
      (rayInverse h G H k u) (deriv (rayGauge h G H k u)) (poleOrder G+poleOrder H)) := by
  obtain ⟨ctrl,hd,hl,hr⟩ := exists_control G H hGH hHG h k hh hu
  exact ⟨⟨ctrl,hd,hl,hr⟩⟩

#print axioms exists_control
#print axioms exists_finiteGauge
end WasowLaurentGaugeControl
