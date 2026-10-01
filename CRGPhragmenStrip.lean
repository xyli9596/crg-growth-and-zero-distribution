import CRGOrder
import Mathlib.Analysis.Complex.PhragmenLindelof

/-! Phragmén--Lindelöf on an angular interval, using the exponential covering
of a horizontal strip. No sectorwise boundedness conclusion is assumed. -/

noncomputable section
open Set Filter Complex Asymptotics
open scoped Topology
namespace CRGPhragmenStrip

def damped (f : ℂ → ℂ) (τ K c : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-(K : ℂ) * Complex.exp ((τ : ℂ) * (w - (c : ℂ) * Complex.I))) *
    f (Complex.exp w)

theorem norm_damped (f : ℂ → ℂ) (τ K c : ℝ) (w : ℂ) :
    ‖damped f τ K c w‖ =
      Real.exp (-K * (Real.exp (τ * w.re) * Real.cos (τ * (w.im - c)))) *
        ‖f (Complex.exp w)‖ := by
  simp [damped, Complex.norm_exp, Complex.exp_re, Complex.mul_re,
    Complex.mul_im]

/-- An actual angular PL estimate. The first exponent is merely an a priori
finite growth exponent; the smaller exponent on the two sides is propagated
through the whole angular interval. -/
theorem angular_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a b c τ κ A B C K : ℝ} (hκ : κ < Real.pi / (b - a))
    (hτ : 0 ≤ τ) (hτκ : τ ≤ κ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hglobal : ∀ w : ℂ,
      ‖f (Complex.exp w)‖ ≤ A * Real.exp (B * Real.exp (κ * |w.re|)))
    (hboundary : ∀ w : ℂ, w.im = a ∨ w.im = b →
      ‖f (Complex.exp w)‖ ≤ A * Real.exp (C * Real.exp (τ * w.re)))
    (hcos : ∀ y : ℝ, y = a ∨ y = b → C ≤ K * Real.cos (τ * (y - c)))
    (w : ℂ) (hwa : a ≤ w.im) (hwb : w.im ≤ b) :
    ‖f (Complex.exp w)‖ ≤ A * Real.exp (K * Real.exp (τ * w.re)) := by
  have hd : Differentiable ℂ (damped f τ K c) := by
    unfold damped
    fun_prop
  have hdg : ∀ v : ℂ,
      ‖damped f τ K c v‖ ≤ A * Real.exp ((B + K) * Real.exp (κ * |v.re|)) := by
    intro v
    rw [norm_damped]
    calc
      _ ≤ Real.exp (K * Real.exp (κ * |v.re|)) *
          (A * Real.exp (B * Real.exp (κ * |v.re|))) := by
        apply mul_le_mul _ (hglobal v) (norm_nonneg _) (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        have hc := Real.neg_one_le_cos (τ * (v.im - c))
        have he : Real.exp (τ * v.re) ≤ Real.exp (κ * |v.re|) := by
          apply Real.exp_le_exp.mpr
          calc
            τ * v.re ≤ τ * |v.re| := mul_le_mul_of_nonneg_left (le_abs_self _) hτ
            _ ≤ κ * |v.re| := mul_le_mul_of_nonneg_right hτκ (abs_nonneg _)
        calc
          -K * (Real.exp (τ * v.re) * Real.cos (τ * (v.im - c))) =
              K * (Real.exp (τ * v.re) * -Real.cos (τ * (v.im - c))) := by ring
          _ ≤ K * (Real.exp (τ * v.re) * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith :
              -Real.cos (τ * (v.im - c)) ≤ 1) (Real.exp_pos _).le) hK
          _ ≤ K * Real.exp (κ * |v.re|) := by
            simpa using mul_le_mul_of_nonneg_left he hK
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hbd : ∀ v : ℂ, v.im = a ∨ v.im = b → ‖damped f τ K c v‖ ≤ A := by
    intro v hv
    rw [norm_damped]
    calc
      _ ≤ Real.exp (-K * (Real.exp (τ * v.re) * Real.cos (τ * (v.im - c)))) *
          (A * Real.exp (C * Real.exp (τ * v.re))) :=
        mul_le_mul_of_nonneg_left (hboundary v hv) (Real.exp_pos _).le
      _ = A * Real.exp ((C - K * Real.cos (τ * (v.im - c))) * Real.exp (τ * v.re)) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      _ ≤ A := by
        apply mul_le_of_le_one_right hA
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hcos v.im hv))
          (Real.exp_pos _).le
  have hPL : ‖damped f τ K c w‖ ≤ A := by
    apply PhragmenLindelof.horizontal_strip hd.diffContOnCl
      ⟨κ, hκ, B + K, ?_⟩ (fun v hv => hbd v (Or.inl hv))
      (fun v hv => hbd v (Or.inr hv)) hwa hwb
    apply Asymptotics.IsBigO.of_bound A
    exact Filter.Eventually.of_forall (fun v => by simpa using hdg v)
  rw [norm_damped] at hPL
  have hrecover : ‖f (Complex.exp w)‖ ≤
      A * Real.exp (K * (Real.exp (τ * w.re) * Real.cos (τ * (w.im - c)))) := by
    have hp := Real.exp_pos (-K * (Real.exp (τ * w.re) * Real.cos (τ * (w.im - c))))
    have hh := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hPL)
    simpa [div_eq_mul_inv, ← Real.exp_neg] using hh
  apply hrecover.trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply Real.exp_le_exp.mpr
  have hc := Real.cos_le_one (τ * (w.im - c))
  calc
    K * (Real.exp (τ * w.re) * Real.cos (τ * (w.im - c))) ≤
        K * (Real.exp (τ * w.re) * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) hK
    _ = _ := by ring

#print axioms norm_damped
#print axioms angular_bound
end CRGPhragmenStrip
