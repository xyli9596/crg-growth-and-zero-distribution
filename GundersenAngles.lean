import LevinGrowth
import NormalFormGoal
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Angular bookkeeping with the actual Lebesgue measure. In particular the
zero-free ray condition is obtained directly from the countable zero set, so it
does not confuse Lean's totalized division with a pole at a zero. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GundersenAngles
open CRGNormalFormGoal

/-- All real representatives of the arguments of zeros. The possible zero at the
origin is harmless: excluding its argument only enlarges a countable set. -/
def zeroAngles (f : ℂ → ℂ) : Set ℝ :=
  ⋃ n : ℤ, (fun z : ℂ => z.arg + (n : ℝ) * (2 * Real.pi)) '' {z | f z = 0}

theorem zeroAngles_countable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∃ z, f z ≠ 0) : (zeroAngles f).Countable := by
  exact Set.countable_iUnion fun n => (LevinGrowth.entire_zeroSet_countable hf hn).image _

theorem zeroAngles_measure_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∃ z, f z ≠ 0) : volume (zeroAngles f) = 0 :=
  (zeroAngles_countable hf hn).measure_zero volume

theorem nonzero_on_ray_of_not_zeroAngles {f : ℂ → ℂ} {θ r : ℝ}
    (hθ : θ ∉ zeroAngles f) (hr : 0 < r) : f (ray θ r) ≠ 0 := by
  intro hz
  apply hθ
  have he : Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp ((Complex.arg (ray θ r) : ℂ) * Complex.I) := by
    apply mul_left_cancel₀ (show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne')
    calc
      (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = ray θ r := rfl
      _ = (‖ray θ r‖ : ℂ) * Complex.exp ((Complex.arg (ray θ r) : ℂ) * Complex.I) :=
        (Complex.norm_mul_exp_arg_mul_I _).symm
      _ = _ := by simp [ray, Complex.norm_exp, Real.norm_of_nonneg hr.le]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have harg : θ = (ray θ r).arg + (n : ℝ) * (2 * Real.pi) := by
    have hi := congrArg Complex.im hn
    simpa using hi
  exact mem_iUnion.mpr ⟨n, ⟨ray θ r, hz, harg.symm⟩⟩

/-- Outside one null angular set a nonzero entire function has no zeros at ANY
positive radius. This is stronger than the eventual nonvanishing needed in the
main proof and does not use the unproved logarithmic derivative estimate. -/
theorem ae_nonzero_on_positive_ray {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∃ z, f z ≠ 0) : ∀ᵐ θ : ℝ, ∀ r : ℝ, 0 < r → f (ray θ r) ≠ 0 := by
  have he : ∀ᵐ θ : ℝ, θ ∉ zeroAngles f := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using zeroAngles_measure_zero hf hn
  filter_upwards [he] with θ hθ
  exact fun r hr => nonzero_on_ray_of_not_zeroAngles hθ hr

/-- Sharp finite-jet estimate on a complete ray tail. This definition does not
assert Gundersen's analytic theorem. -/
def RayDerivativeBound (f : ℂ → ℂ) (ρ : ℝ) (n : ℕ) (δ θ : ℝ) : Prop :=
  ∀ᶠ r : ℝ in atTop, ∀ k : ℕ, 1 ≤ k → k ≤ n →
    ‖iteratedDeriv k f (ray θ r) / f (ray θ r)‖ ≤ r ^ ((k : ℝ) * (ρ - 1 + δ))

theorem rayDerivativeBound_mono_error {f : ℂ → ℂ} {ρ δ ε θ : ℝ} {n : ℕ}
    (hδε : δ ≤ ε) (h : RayDerivativeBound f ρ n δ θ) :
    RayDerivativeBound f ρ n ε θ := by
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with r hr hr1
  intro k hk hkn
  exact (hr k hk hkn).trans (Real.rpow_le_rpow_of_exponent_le hr1
    (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg k)))

/-- The countable union step in the manuscript: a separate angular null set for
each positive error gives one null set valid for every positive error. The
analytic bound itself is an explicit premise, not supplied by this theorem. -/
theorem simultaneous_errors {f : ℂ → ℂ} {ρ : ℝ} {n : ℕ}
    (h : ∀ δ : ℝ, 0 < δ → ∀ᵐ θ : ℝ, RayDerivativeBound f ρ n δ θ) :
    ∀ᵐ θ : ℝ, ∀ δ : ℝ, 0 < δ → RayDerivativeBound f ρ n δ θ := by
  have hh : ∀ᵐ θ : ℝ, ∀ j : ℕ, RayDerivativeBound f ρ n (1 / ((j : ℝ) + 1)) θ := by
    rw [ae_all_iff]
    intro j
    exact h _ (by positivity)
  filter_upwards [hh] with θ hθ
  intro δ hδ
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  exact rayDerivativeBound_mono_error (le_of_lt hj) (hθ j)

#print axioms zeroAngles_countable
#print axioms zeroAngles_measure_zero
#print axioms nonzero_on_ray_of_not_zeroAngles
#print axioms ae_nonzero_on_positive_ray
#print axioms rayDerivativeBound_mono_error
#print axioms simultaneous_errors
end GundersenAngles
