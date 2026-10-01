import CRGRay
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
A concrete mixed forward/backward Volterra operator on a complete space of
bounded continuous vectors. The integration variable and parameter use the same
ordered domain. In the manuscript take α = Set.Ici r₀ with its subtype volume.
The kernel is written explicitly; continuity, boundedness, the contraction
estimate and existence of its fixed point are proved, not passed as hypotheses.
No ODE differentiation or fundamental matrix theorem is claimed here.
-/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction
namespace MixedVolterra
variable {α ι : Type*}
variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
variable [FirstCountableTopology α] [MeasurableSpace α] [BorelSpace α]
variable [Fintype ι]

/-- Forward kernels include s ≤ r; backward kernels include r ≤ s and the minus sign.
Equal phases use the backward choice with q = 0. -/
def kernel (forward : Bool) (q : α → ℂ) (r s : α) : ℂ :=
  if forward then
    if s ≤ r then Complex.exp (q r - q s) else 0
  else
    if r ≤ s then -Complex.exp (q r - q s) else 0

lemma kernel_bound (forward : Bool) (q : α → ℂ)
    (hord : if forward then Antitone (fun t => (q t).re)
      else Monotone (fun t => (q t).re)) (r s : α) :
    ‖kernel forward q r s‖ ≤ 1 := by
  cases h : forward
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hord ⊢
    unfold kernel
    simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with hrs
    · simpa only [norm_neg] using CRGRay.exponential_kernel_bound (q r) (q s) (hord hrs)
    · simp
  · simp only [h, ↓reduceIte] at hord ⊢
    unfold kernel
    simp only [↓reduceIte]
    split_ifs with hsr
    · exact CRGRay.exponential_kernel_bound (q r) (q s) (hord hsr)
    · simp

lemma kernel_measurable (forward : Bool) (q : α → ℂ) (hq : Continuous q) (r : α) :
    Measurable (kernel forward q r) := by
  have hExp : Measurable (fun s => Complex.exp (q r - q s)) :=
    (continuous_const.sub hq).cexp.measurable
  cases forward
  · change Measurable (fun s => if r ≤ s then -Complex.exp (q r - q s) else 0)
    exact hExp.neg.ite measurableSet_Ici measurable_const
  · change Measurable (fun s => if s ≤ r then Complex.exp (q r - q s) else 0)
    exact hExp.ite measurableSet_Iic measurable_const

lemma kernel_continuousAt (forward : Bool) (q : α → ℂ) (hq : Continuous q)
    (r s : α) (hs : s ≠ r) : ContinuousAt (fun t => kernel forward q t s) r := by
  have hExp : ContinuousAt (fun t => Complex.exp (q t - q s)) r :=
    (hq.continuousAt.sub continuousAt_const).cexp
  rcases lt_or_gt_of_ne hs with hsr | hrs
  · have he : ∀ᶠ t in 𝓝 r, s < t := Ioi_mem_nhds hsr
    cases forward
    · apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [he] with t ht
      simp [kernel, not_le.mpr ht]
    · apply hExp.congr_of_eventuallyEq
      filter_upwards [he] with t ht
      simp [kernel, ht.le]
  · have he : ∀ᶠ t in 𝓝 r, t < s := Iio_mem_nhds hrs
    cases forward
    · apply hExp.neg.congr_of_eventuallyEq
      filter_upwards [he] with t ht
      simp [kernel, ht.le]
    · apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [he] with t ht
      simp [kernel, not_le.mpr ht]

variable (μ : Measure α) [NullSingletonClass μ]
variable (mode : ι → Bool) (q : ι → α → ℂ)
variable (hq : ∀ i, Continuous (q i))
variable (hord : ∀ i, if mode i then Antitone (fun t => (q i t).re)
      else Monotone (fun t => (q i t).re))
variable (R : α → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hR : Continuous R)
variable (b : α → ℝ) (hb : Integrable b μ)
variable (hRb : ∀ s, ‖R s‖ ≤ b s)

/-- The literal componentwise integral, before bundling it as a continuous function. -/
def integralVector (u : α →ᵇ (ι → ℂ)) (r : α) (i : ι) : ℂ :=
  ∫ s, kernel (mode i) (q i) r s * (R s (u s)) i ∂μ

include hord hRb in
lemma integrand_bound (u : α →ᵇ (ι → ℂ)) (r : α) (i : ι) (s : α) :
    ‖kernel (mode i) (q i) r s * (R s (u s)) i‖ ≤ b s * ‖u‖ := by
  calc
    _ = ‖kernel (mode i) (q i) r s‖ * ‖(R s (u s)) i‖ := norm_mul _ _
    _ ≤ 1 * ‖(R s (u s)) i‖ := mul_le_mul_of_nonneg_right
      (kernel_bound _ _ (hord i) r s) (norm_nonneg _)
    _ ≤ ‖R s (u s)‖ := by simpa using norm_le_pi_norm (R s (u s)) i
    _ ≤ ‖R s‖ * ‖u s‖ := (R s).le_opNorm _
    _ ≤ b s * ‖u‖ := mul_le_mul (hRb s) (u.norm_coe_le_norm s)
      (norm_nonneg _) ((norm_nonneg _).trans (hRb s))

include hq hR in
lemma integrand_measurable (u : α →ᵇ (ι → ℂ)) (r : α) (i : ι) :
    AEStronglyMeasurable (fun s => kernel (mode i) (q i) r s * (R s (u s)) i) μ := by
  have hc : Continuous (fun s => (R s (u s)) i) := by fun_prop
  exact ((kernel_measurable _ _ (hq i) r).mul hc.measurable).aestronglyMeasurable

include hq hord hR hb hRb in
lemma integrand_integrable (u : α →ᵇ (ι → ℂ)) (r : α) (i : ι) :
    Integrable (fun s => kernel (mode i) (q i) r s * (R s (u s)) i) μ := by
  exact (hb.mul_const ‖u‖).mono'
    (integrand_measurable μ mode q hq R hR u r i)
    (ae_of_all μ (integrand_bound mode q hord R b hRb u r i))

include hq hord hR hb hRb in
lemma integralVector_continuous (u : α →ᵇ (ι → ℂ)) :
    Continuous (integralVector μ mode q R u) := by
  apply continuous_pi
  intro i
  apply continuous_iff_continuousAt.mpr
  intro r
  apply continuousAt_of_dominated
    (bound := fun s => b s * ‖u‖)
    (Eventually.of_forall fun t => integrand_measurable μ mode q hq R hR u t i)
    (Eventually.of_forall fun t => ae_of_all μ (integrand_bound mode q hord R b hRb u t i))
    (hb.mul_const ‖u‖)
  filter_upwards [μ.ae_ne r] with s hs
  exact (kernel_continuousAt _ _ (hq i) r s hs).mul continuousAt_const

include hq hord hR hb hRb in
lemma integralVector_bound (u : α →ᵇ (ι → ℂ)) (r : α) :
    ‖integralVector μ mode q R u r‖ ≤ (∫ s, b s ∂μ) * ‖u‖ := by
  have hbpos : 0 ≤ ∫ s, b s ∂μ := integral_nonneg fun s => (norm_nonneg _).trans (hRb s)
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hbpos (norm_nonneg _))).mpr
  intro i
  calc
    _ ≤ ∫ s, b s * ‖u‖ ∂μ := norm_integral_le_of_norm_le (hb.mul_const ‖u‖)
      (ae_of_all μ (integrand_bound mode q hord R b hRb u r i))
    _ = _ := integral_mul_const _ _

/-- The mixed integral operator is genuinely a self-map of bounded continuous vectors. -/
def integralOperator (u : α →ᵇ (ι → ℂ)) : α →ᵇ (ι → ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (integralVector μ mode q R u)
    (integralVector_continuous μ mode q hq hord R hR b hb hRb u)
    ((∫ s, b s ∂μ) * ‖u‖)
    (integralVector_bound μ mode q hq hord R hR b hb hRb u)

include hq hord hR hb hRb in
lemma integralVector_sub (u v : α →ᵇ (ι → ℂ)) (r : α) :
    integralVector μ mode q R (u - v) r =
    integralVector μ mode q R u r - integralVector μ mode q R v r := by
  ext i
  simp only [integralVector, BoundedContinuousFunction.sub_apply, map_sub, Pi.sub_apply, mul_sub]
  exact integral_sub
    (integrand_integrable μ mode q hq hord R hR b hb hRb u r i)
    (integrand_integrable μ mode q hq hord R hR b hb hRb v r i)

lemma integralOperator_lipschitz (u v : α →ᵇ (ι → ℂ)) :
    ‖integralOperator μ mode q hq hord R hR b hb hRb u -
      integralOperator μ mode q hq hord R hR b hb hRb v‖ ≤
      (∫ s, b s ∂μ) * ‖u - v‖ := by
  have hbpos : 0 ≤ ∫ s, b s ∂μ := integral_nonneg fun s => (norm_nonneg _).trans (hRb s)
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hbpos (norm_nonneg _))).mpr
  intro r
  change ‖integralVector μ mode q R u r - integralVector μ mode q R v r‖ ≤ _
  rw [← integralVector_sub μ mode q hq hord R hR b hb hRb u v r]
  exact integralVector_bound μ mode q hq hord R hR b hb hRb (u - v) r

/-- The manuscript's integral equation has a unique bounded continuous solution
when the L1 tail mass is < 1. The affine forcing is arbitrary; for column j it
is the constant vector whose components are δij in the equal-phase block and 0 elsewhere. -/
theorem exists_unique_fixed_point (c : α →ᵇ (ι → ℂ))
    (hsmall : (∫ s, b s ∂μ) < 1) :
    ∃! u : α →ᵇ (ι → ℂ),
      u = c + integralOperator μ mode q hq hord R hR b hb hRb u := by
  have hbpos : 0 ≤ ∫ s, b s ∂μ := integral_nonneg fun s => (norm_nonneg _).trans (hRb s)
  let a : NNReal := ⟨∫ s, b s ∂μ, hbpos⟩
  have ha : a < 1 := hsmall
  have hae : (a : ℝ) = ∫ s, b s ∂μ := rfl
  have hF : ∀ u v : α →ᵇ (ι → ℂ),
      ‖(c + integralOperator μ mode q hq hord R hR b hb hRb u) -
        (c + integralOperator μ mode q hq hord R hR b hb hRb v)‖ ≤
        (a : ℝ) * ‖u - v‖ := by
    intro u v
    rw [hae, add_sub_add_left_eq_sub]
    exact integralOperator_lipschitz μ mode q hq hord R hR b hb hRb u v
  obtain ⟨u, hu, huniq⟩ := CRGRay.fixed_point_of_norm_bound
    (fun u => c + integralOperator μ mode q hq hord R hR b hb hRb u) a ha hF
  exact ⟨u, hu.symm, fun v hv => huniq v hv.symm⟩

/-- The forward exponential kernel tends to zero for a phase with real part → -∞. -/
lemma forward_kernel_tendsto_zero (q₀ : α → ℂ)
    (hdecay : Tendsto (fun r => (q₀ r).re) atTop atBot) (s : α) :
    Tendsto (fun r => kernel true q₀ r s) atTop (𝓝 0) := by
  have hd : Tendsto (fun r => (q₀ r).re - (q₀ s).re) atTop atBot := by
    apply tendsto_atBot.mpr
    intro B
    filter_upwards [tendsto_atBot.mp hdecay (B + (q₀ s).re)] with r hr
    linarith
  have hexp : Tendsto (fun r => Complex.exp (q₀ r - q₀ s)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Complex.norm_exp, Complex.sub_re, Function.comp_def] using Real.tendsto_exp_atBot.comp hd
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop s] with r hr
  simp [kernel, hr]

/-- The backward kernel has empty support at a fixed s once r has passed s. -/
lemma backward_kernel_tendsto_zero [NoMaxOrder α] (q₀ : α → ℂ) (s : α) :
    Tendsto (fun r => kernel false q₀ r s) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop s] with r hr
  simp [kernel, not_le.mpr hr]

include hq hord hR hb hRb in
/-- This proves the forward split-integral limit and all backward tail limits
for the actual cutoff kernels, using dominated convergence. -/
lemma integralVector_tendsto_zero [NoMaxOrder α]
    [(atTop : Filter α).IsCountablyGenerated]
    (hdecay : ∀ i, mode i = true → Tendsto (fun r => (q i r).re) atTop atBot)
    (u : α →ᵇ (ι → ℂ)) :
    Tendsto (integralVector μ mode q R u) atTop (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hpoint : ∀ᵐ s ∂μ, Tendsto
      (fun r => kernel (mode i) (q i) r s * (R s (u s)) i) atTop (𝓝 (0 : ℂ)) := by
    apply ae_of_all
    intro s
    have hk : Tendsto (fun r => kernel (mode i) (q i) r s) atTop (𝓝 0) := by
      cases h : mode i
      · exact backward_kernel_tendsto_zero (q i) s
      · exact forward_kernel_tendsto_zero (q i) (hdecay i h) s
    simpa only [zero_mul] using hk.mul_const ((R s (u s)) i)
  simpa only [integralVector, integral_zero, Pi.zero_apply] using
    tendsto_integral_filter_of_dominated_convergence (fun s => b s * ‖u‖)
      (Eventually.of_forall fun r => integrand_measurable μ mode q hq R hR u r i)
      (Eventually.of_forall fun r => ae_of_all μ (integrand_bound mode q hord R b hRb u r i))
      (hb.mul_const ‖u‖) hpoint

/-- A fixed point with constant forcing converges to that constant vector. -/
theorem fixed_point_tendsto [NoMaxOrder α]
    [(atTop : Filter α).IsCountablyGenerated]
    (hdecay : ∀ i, mode i = true → Tendsto (fun r => (q i r).re) atTop atBot)
    (v : ι → ℂ) (u : α →ᵇ (ι → ℂ))
    (hu : u = BoundedContinuousFunction.const α v +
      integralOperator μ mode q hq hord R hR b hb hRb u) :
    Tendsto u atTop (𝓝 v) := by
  have hlim := (integralVector_tendsto_zero μ mode q hq hord R hR b hb hRb hdecay u).const_add v
  simpa only [add_zero] using hlim.congr' (Eventually.of_forall fun r => by
    have hx := congrArg (fun f : α →ᵇ (ι → ℂ) => f r) hu
    exact hx.symm)

#print axioms kernel_bound
#print axioms kernel_measurable
#print axioms kernel_continuousAt
#print axioms integrand_bound
#print axioms integrand_measurable
#print axioms integrand_integrable
#print axioms integralVector_continuous
#print axioms integralVector_bound
#print axioms integralVector_sub
#print axioms integralOperator_lipschitz
#print axioms exists_unique_fixed_point
#print axioms forward_kernel_tendsto_zero
#print axioms backward_kernel_tendsto_zero
#print axioms integralVector_tendsto_zero
#print axioms fixed_point_tendsto
end MixedVolterra
