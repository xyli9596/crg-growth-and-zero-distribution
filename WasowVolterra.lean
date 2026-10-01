import Halfline
import VolterraCalculus

/-!
# Differentiation of the concrete mixed Volterra fixed point

The constant forcing is retained exactly: its derivative equation contains
`q' * (u - v)`. The homogeneous normalized system follows only under the
explicit compatibility `q' * v = 0`, discharged for phase differences and a
coordinate basis vector.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
attribute [local instance] Measure.Subtype.measureSpace
namespace WasowVolterra

def retract (a r : ℝ) : Ici a := ⟨max a r, by change a ≤ max a r; exact le_max_left a r⟩

theorem continuous_retract (a : ℝ) : Continuous (retract a) := by
  exact ((continuous_const : Continuous (fun _ : ℝ => a)).max continuous_id).subtype_mk _

@[simp] theorem retract_coe (a : ℝ) (r : Ici a) : retract a r = r := by
  apply Subtype.ext
  exact max_eq_right (show a ≤ (r : ℝ) from r.property)

def extend {α : Type*} (a : ℝ) (u : Ici a → α) (r : ℝ) : α := u (retract a r)

theorem continuous_extend {α : Type*} [TopologicalSpace α] {a : ℝ} {u : Ici a → α}
    (hu : Continuous u) : Continuous (extend a u) := hu.comp (continuous_retract a)

@[simp] theorem extend_coe {α : Type*} (a : ℝ) (u : Ici a → α) (r : Ici a) :
    extend a u r = u r := by simp [extend]

theorem forward_integral_eq (q h : ℝ → ℂ) {a r : ℝ} (hr : a ≤ r) :
    (∫ s in Ici a, MixedVolterra.kernel true q r s * h s) =
      Complex.exp (q r) * ∫ s in a..r, Complex.exp (-q s) * h s := by
  have heq : (fun s => MixedVolterra.kernel true q r s * h s) =
      (Iic r).indicator (fun s => Complex.exp (q r) * (Complex.exp (-q s) * h s)) := by
    funext s
    by_cases hs : s ≤ r
    · simp [MixedVolterra.kernel, hs, Complex.exp_sub, Complex.exp_neg, div_eq_mul_inv,
        mul_assoc]
    · simp [MixedVolterra.kernel, hs]
  rw [heq, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic r ∩ Ici a = Icc a r := by ext s; simp only [mem_inter_iff, mem_Iic, mem_Ici, mem_Icc]; tauto
  rw [hset, integral_const_mul, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hr]

theorem backward_integral_eq (q h : ℝ → ℂ) {a r : ℝ} (hr : a ≤ r) :
    (∫ s in Ici a, MixedVolterra.kernel false q r s * h s) =
      -Complex.exp (q r) * ∫ s in Ici r, Complex.exp (-q s) * h s := by
  have heq : (fun s => MixedVolterra.kernel false q r s * h s) =
      (Ici r).indicator (fun s => -Complex.exp (q r) * (Complex.exp (-q s) * h s)) := by
    funext s
    by_cases hs : r ≤ s
    · simp [MixedVolterra.kernel, hs, Complex.exp_sub, Complex.exp_neg, div_eq_mul_inv,
        mul_assoc]
    · simp [MixedVolterra.kernel, hs]
  rw [heq, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    inter_eq_left.mpr (Ici_subset_Ici.mpr hr), integral_const_mul]


/-- The literal subtype integral is the real integral restricted to the half-line. -/
theorem subtype_integral_eq (forward : Bool) (q : ℝ → ℂ) {a : ℝ}
    (h : Ici a → ℂ) (r : Ici a) :
    (∫ s : Ici a, MixedVolterra.kernel forward (fun t : Ici a => q t) r s * h s) =
      ∫ s in Ici a, MixedVolterra.kernel forward q r s * extend a h s := by
  rw [← integral_subtype measurableSet_Ici]
  apply integral_congr_ae
  exact ae_of_all _ (fun s => by simp [MixedVolterra.kernel])

/-- Backward monotonicity makes the weighted forcing integrable on the whole
half-line. No extra weighted L1 hypothesis is added to the fixed-point inputs. -/
theorem backward_weighted_integrable {ι : Type*} [Fintype ι] {a : ℝ}
    (q : ℝ → ℂ) (hq : Continuous q)
    (hmono : Monotone (fun s : Ici a => (q s).re))
    (R : Ici a → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hR : Continuous R)
    (hL1 : Integrable (fun s : Ici a => ‖R s‖))
    (u : Ici a →ᵇ (ι → ℂ)) (i : ι) :
    IntegrableOn (fun s => Complex.exp (-q s) * extend a (fun t => (R t (u t)) i) s)
      (Ici a) := by
  apply (integrableOn_iff_comap_subtypeVal measurableSet_Ici).2
  change Integrable (fun s : Ici a =>
    Complex.exp (-q s) * extend a (fun t => (R t (u t)) i) s)
  simp only [extend_coe]
  have hC : 0 ≤ Real.exp (-(q a).re) := (Real.exp_pos _).le
  have hm : Continuous (fun s : Ici a => Complex.exp (-q s) * (R s (u s)) i) := by
    have hc : Continuous (fun s : Ici a => q s) := hq.comp continuous_subtype_val
    fun_prop
  apply (hL1.const_mul (Real.exp (-(q a).re) * ‖u‖)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro s
  have hanchor : retract a a ≤ s := by
    change max a a ≤ (s : ℝ)
    rw [max_self]
    exact s.property
  have hqle : (q a).re ≤ (q s).re := by
    simpa [retract] using hmono hanchor
  have hexp : ‖Complex.exp (-q s)‖ ≤ Real.exp (-(q a).re) := by
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_exp.mpr (neg_le_neg hqle)
  have hRu : ‖(R s (u s)) i‖ ≤ ‖R s‖ * ‖u‖ :=
    (norm_le_pi_norm _ i).trans (((R s).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (u.norm_coe_le_norm s) (norm_nonneg _)))
  rw [norm_mul]
  calc
    _ ≤ Real.exp (-(q a).re) * (‖R s‖ * ‖u‖) :=
      mul_le_mul hexp hRu (norm_nonneg _) hC
    _ = _ := by ring


/-- Differentiation of both cutoff kernels on the open half-line. -/
theorem mixed_integral_hasDerivAt (forward : Bool) (q h : ℝ → ℂ)
    {a r : ℝ} {d : ℂ} (hr : a < r) (hq : HasDerivAt q d r)
    (hc : Continuous (fun s => Complex.exp (-q s) * h s))
    (hback : forward = false → IntegrableOn (fun s => Complex.exp (-q s) * h s) (Ici a)) :
    HasDerivAt (fun t => ∫ s in Ici a, MixedVolterra.kernel forward q t s * h s)
      (d * (∫ s in Ici a, MixedVolterra.kernel forward q r s * h s) + h r) r := by
  cases forward
  · rw [backward_integral_eq q h hr.le]
    apply (VolterraCalculus.backward_hasDerivAt q h a r d hq hr hc (hback rfl)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact backward_integral_eq q h ht.le
  · rw [forward_integral_eq q h hr.le]
    apply (VolterraCalculus.forward_hasDerivAt q h a r d hq hc).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact forward_integral_eq q h ht.le

@[simp] theorem extend_of_mem {α : Type*} (a : ℝ) (u : Ici a → α)
    {r : ℝ} (hr : a ≤ r) : extend a u r = u ⟨r, hr⟩ := by
  simp [extend, retract, max_eq_right hr]

/-- The actual bounded continuous fixed point is differentiable in every
component on the interior of its real half-line. For arbitrary forcing `v`,
the diagonal term is exactly `q' * (u - v)`. -/
theorem fixed_point_component_hasDerivAt {ι : Type*} [Fintype ι] {a : ℝ}
    (mode : ι → Bool) (q : ι → ℝ → ℂ) (hq : ∀ i, Continuous (q i))
    (hord : ∀ i, if mode i then Antitone (fun t : Ici a => (q i t).re)
      else Monotone (fun t : Ici a => (q i t).re))
    (R : Ici a → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hR : Continuous R)
    (hL1 : Integrable (fun s : Ici a => ‖R s‖))
    (v : ι → ℂ) (u : Ici a →ᵇ (ι → ℂ))
    (hu : ∀ r i, u r i = v i + ∫ s : Ici a,
      MixedVolterra.kernel (mode i) (fun t : Ici a => q i t) r s * (R s (u s)) i)
    {r : ℝ} (hr : a < r) (i : ι) {d : ℂ} (hd : HasDerivAt (q i) d r) :
    HasDerivAt (fun t => extend a u t i)
      (d * (extend a u r i - v i) + (extend a R r (extend a u r)) i) r := by
  let h : ℝ → ℂ := extend a (fun s => (R s (u s)) i)
  have hhc : Continuous h := continuous_extend (by fun_prop)
  have hwc : Continuous (fun s => Complex.exp (-q i s) * h s) := by fun_prop
  have hback : mode i = false →
      IntegrableOn (fun s => Complex.exp (-q i s) * h s) (Ici a) := by
    intro hi
    have hm := hord i
    simp only [hi, Bool.false_eq_true, ↓reduceIte] at hm
    exact backward_weighted_integrable (q i) (hq i) hm R hR hL1 u i
  have heq (t : ℝ) (ht : a ≤ t) : extend a u t i = v i +
      ∫ s in Ici a, MixedVolterra.kernel (mode i) (q i) t s * h s := by
    rw [extend_of_mem a u ht]
    have ht' := hu ⟨t, ht⟩ i
    rw [subtype_integral_eq (mode i) (q i) (fun s => (R s (u s)) i)] at ht'
    exact ht'
  have hj := (mixed_integral_hasDerivAt (mode i) (q i) h hr hd hwc hback).const_add (v i)
  have hj' : HasDerivAt (fun t => extend a u t i)
      (d * (∫ s in Ici a, MixedVolterra.kernel (mode i) (q i) r s * h s) + h r) r := by
    apply hj.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact heq t ht.le
  convert hj' using 1
  rw [heq r hr.le]
  simp only [add_sub_cancel_left]
  rfl


/-- The vector ODE obtained from the actual mixed fixed point. -/
theorem fixed_point_hasDerivAt {ι : Type*} [Fintype ι] {a : ℝ}
    (mode : ι → Bool) (q : ι → ℝ → ℂ) (hq : ∀ i, Continuous (q i))
    (hord : ∀ i, if mode i then Antitone (fun t : Ici a => (q i t).re)
      else Monotone (fun t : Ici a => (q i t).re))
    (R : Ici a → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hR : Continuous R)
    (hL1 : Integrable (fun s : Ici a => ‖R s‖))
    (v : ι → ℂ) (u : Ici a →ᵇ (ι → ℂ))
    (hu : ∀ r i, u r i = v i + ∫ s : Ici a,
      MixedVolterra.kernel (mode i) (fun t : Ici a => q i t) r s * (R s (u s)) i)
    {r : ℝ} (hr : a < r) (d : ι → ℂ) (hd : ∀ i, HasDerivAt (q i) (d i) r) :
    HasDerivAt (extend a u)
      (fun i => d i * (extend a u r i - v i) + (extend a R r (extend a u r)) i) r := by
  apply hasDerivAt_pi.mpr
  intro i
  exact fixed_point_component_hasDerivAt mode q hq hord R hR hL1 v u hu hr i (hd i)

/-- Compatibility of the forcing with the diagonal derivative removes the
inhomogeneous diagonal term. -/
theorem fixed_point_normalized_ode {ι : Type*} [Fintype ι] {a : ℝ}
    (mode : ι → Bool) (q : ι → ℝ → ℂ) (hq : ∀ i, Continuous (q i))
    (hord : ∀ i, if mode i then Antitone (fun t : Ici a => (q i t).re)
      else Monotone (fun t : Ici a => (q i t).re))
    (R : Ici a → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hR : Continuous R)
    (hL1 : Integrable (fun s : Ici a => ‖R s‖))
    (v : ι → ℂ) (u : Ici a →ᵇ (ι → ℂ))
    (hu : ∀ r i, u r i = v i + ∫ s : Ici a,
      MixedVolterra.kernel (mode i) (fun t : Ici a => q i t) r s * (R s (u s)) i)
    {r : ℝ} (hr : a < r) (d : ι → ℂ) (hd : ∀ i, HasDerivAt (q i) (d i) r)
    (hcompat : ∀ i, d i * v i = 0) :
    HasDerivAt (extend a u)
      (fun i => d i * extend a u r i + (extend a R r (extend a u r)) i) r := by
  have hd' := fixed_point_hasDerivAt mode q hq hord R hR hL1 v u hu hr d hd
  simpa only [mul_sub, hcompat, sub_zero] using hd'

/-- Existence, the literal integral equation, its asymptotic limit, and the
interior ODE for one concrete half-line column. -/
theorem exists_column_ode (m : ℕ) (a : ℝ)
    (mode : Fin m → Bool) (q : Fin m → ℝ → ℂ) (hq : ∀ i, Continuous (q i))
    (dq : Fin m → ℝ → ℂ) (hdq : ∀ i r, a < r → HasDerivAt (q i) (dq i r) r)
    (hord : ∀ i, if mode i then Antitone (fun t : Ici a => (q i t).re)
      else Monotone (fun t : Ici a => (q i t).re))
    (hdecay : ∀ i, mode i = true →
      Tendsto (fun r : Ici a => (q i r).re) atTop atBot)
    (R : Ici a → (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) (hR : Continuous R)
    (hL1 : Integrable (fun s : Ici a => ‖R s‖))
    (hsmall : (∫ s : Ici a, ‖R s‖) < 1)
    (v : Fin m → ℂ) (hcompat : ∀ i r, a < r → dq i r * v i = 0) :
    ∃ u : Ici a →ᵇ (Fin m → ℂ),
      (∀ r i, u r i = v i + ∫ s : Ici a,
        MixedVolterra.kernel (mode i) (fun t : Ici a => q i t) r s * (R s (u s)) i) ∧
      Tendsto u atTop (𝓝 v) ∧
      ∀ r : ℝ, a < r → HasDerivAt (extend a u)
        (fun i => dq i r * extend a u r i + (extend a R r (extend a u r)) i) r := by
  obtain ⟨u, hu, hlim⟩ := CRGHalfline.exists_column m a mode
    (fun i t => q i t) (fun i => (hq i).comp continuous_subtype_val)
    hord hdecay R hR hL1 hsmall v
  refine ⟨u, hu, hlim, fun r hr => ?_⟩
  exact fixed_point_normalized_ode mode q hq hord R hR hL1 v u hu hr
    (fun i => dq i r) (fun i => hdq i r hr) (fun i => hcompat i r hr)

/-- The diagonal compatibility is automatic for a normalized column: the
phase on component `i` is `Qᵢ-Qⱼ`, and the constant forcing is `eⱼ`. -/
theorem exists_phase_difference_column_ode (m : ℕ) (a : ℝ) (j : Fin m)
    (mode : Fin m → Bool) (Q dQ : Fin m → ℝ → ℂ)
    (hQ : ∀ i, Continuous (Q i))
    (hdQ : ∀ i r, a < r → HasDerivAt (Q i) (dQ i r) r)
    (hord : ∀ i, if mode i then
      Antitone (fun t : Ici a => (Q i t-Q j t).re)
      else Monotone (fun t : Ici a => (Q i t-Q j t).re))
    (hdecay : ∀ i, mode i = true →
      Tendsto (fun r : Ici a => (Q i r-Q j r).re) atTop atBot)
    (R : Ici a → (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) (hR : Continuous R)
    (hL1 : Integrable (fun s : Ici a => ‖R s‖))
    (hsmall : (∫ s : Ici a, ‖R s‖) < 1) :
    ∃ u : Ici a →ᵇ (Fin m → ℂ),
      (∀ r i, u r i = (Pi.single j (1 : ℂ) : Fin m → ℂ) i + ∫ s : Ici a,
        MixedVolterra.kernel (mode i) (fun t : Ici a => Q i t-Q j t) r s * (R s (u s)) i) ∧
      Tendsto u atTop (𝓝 (Pi.single j (1 : ℂ) : Fin m → ℂ)) ∧
      ∀ r : ℝ, a < r → HasDerivAt (extend a u)
        (fun i => (dQ i r-dQ j r) * extend a u r i +
          (extend a R r (extend a u r)) i) r := by
  apply exists_column_ode m a mode (fun i r => Q i r-Q j r)
    (fun i => (hQ i).sub (hQ j)) (fun i r => dQ i r-dQ j r)
    (fun i r hr => (hdQ i r hr).sub (hdQ j r hr)) hord hdecay R hR hL1 hsmall
    (Pi.single j (1 : ℂ) : Fin m → ℂ)
  intro i r _
  by_cases hij : i = j
  · simp [hij]
  · simp [Pi.single_eq_of_ne hij]


/-- Multiplying a normalized phase-difference column by `exp Qⱼ` gives the
original diagonal-plus-remainder ODE. This is the actual product rule for the
constructed functions, not a formal matrix identity. -/
theorem denormalize_hasDerivAt {ι : Type*} [Fintype ι]
    (u : ℝ → ι → ℂ) (Q : ℝ → ℂ) (D : ι → ℂ)
    (R : (ι → ℂ) →L[ℂ] (ι → ℂ)) (j : ι) {r : ℝ}
    (hQ : HasDerivAt Q (D j) r)
    (hu : HasDerivAt u (fun i => (D i-D j)*u r i+(R (u r)) i) r) :
    HasDerivAt (fun t => Complex.exp (Q t) • u t)
      (fun i => D i * (Complex.exp (Q r) • u r) i +
        (R (Complex.exp (Q r) • u r)) i) r := by
  apply hasDerivAt_pi.mpr
  intro i
  have hd := hQ.cexp.mul (hasDerivAt_pi.mp hu i)
  convert hd using 1 <;> try rfl
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  ring

end WasowVolterra

#print axioms WasowVolterra.continuous_retract
#print axioms WasowVolterra.retract_coe
#print axioms WasowVolterra.continuous_extend
#print axioms WasowVolterra.extend_coe
#print axioms WasowVolterra.forward_integral_eq
#print axioms WasowVolterra.backward_integral_eq

#print axioms WasowVolterra.subtype_integral_eq
#print axioms WasowVolterra.backward_weighted_integrable

#print axioms WasowVolterra.mixed_integral_hasDerivAt
#print axioms WasowVolterra.extend_of_mem
#print axioms WasowVolterra.fixed_point_component_hasDerivAt

#print axioms WasowVolterra.fixed_point_hasDerivAt
#print axioms WasowVolterra.fixed_point_normalized_ode
#print axioms WasowVolterra.exists_column_ode
#print axioms WasowVolterra.exists_phase_difference_column_ode

#print axioms WasowVolterra.denormalize_hasDerivAt
