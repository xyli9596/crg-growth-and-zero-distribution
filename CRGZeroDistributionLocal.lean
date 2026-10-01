import LevinAnalytic

/-! The local zero-counting estimate used to turn a harmonic asymptotic
profile into negligible zero density. The actual divisor and multiplicities
are retained. No global zero-density conclusion is an input. -/
set_option autoImplicit false
noncomputable section
open Set Metric Real Complex MeromorphicOn
namespace CRGZeroDistributionLocal

/-- Multiplication by the exponential of an analytic function leaves every
zero multiplicity unchanged, including in the presence of identically zero
germs (the existing totalized divisor convention is preserved). -/
theorem divisor_mul_exp {f H : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hH : AnalyticOnNhd ℂ H U) :
    MeromorphicOn.divisor (f * fun z => Complex.exp (H z)) U =
      MeromorphicOn.divisor f U := by
  have hg : AnalyticOnNhd ℂ (fun z => Complex.exp (H z)) U :=
    fun z hz => (hH z hz).cexp
  have hprod : AnalyticOnNhd ℂ (f * fun z => Complex.exp (H z)) U := hf.mul hg
  ext z
  by_cases hz : z ∈ U
  · rw [hprod.divisor_apply hz, hf.divisor_apply hz,
      analyticOrderAt_mul (hf z hz) (hg z hz),
      (hg z hz).analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero (H z)), add_zero]
  · simp only [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-- Jensen after cancelling an actual analytic profile: if the upper
logarithmic profile error is at most `e` on the outer circle and the center
error is at most `e`, the inner zero count is at most `2e/log 2`. -/
theorem zero_count_of_analytic_profile {f H : ℂ → ℂ} {c : ℂ} {r e : ℝ}
    (hr : 0 < r) (he : 0 ≤ e)
    (hf : AnalyticOnNhd ℂ f (closedBall c (2*r)))
    (hH : AnalyticOnNhd ℂ H (closedBall c (2*r))) (hc : f c ≠ 0)
    (hupper : ∀ z ∈ sphere c (2*r), ‖f z‖ ≤ Real.exp ((H z).re + e))
    (hlower : (H c).re - e ≤ Real.log ‖f c‖) :
    (∑ᶠ z, MeromorphicOn.divisor f (closedBall c r) z : ℤ) ≤
      2*e / Real.log 2 := by
  let g : ℂ → ℂ := f * fun z => Complex.exp (-H z)
  have hexp : AnalyticOnNhd ℂ (fun z => Complex.exp (-H z)) (closedBall c (2*r)) :=
    fun z hz => (hH z hz).neg.cexp
  have hg : AnalyticOnNhd ℂ g (closedBall c (2*r)) := hf.mul hexp
  have hgc : g c ≠ 0 := mul_ne_zero hc (Complex.exp_ne_zero _)
  have hgbound : ∀ z ∈ sphere c (2*r), ‖g z‖ ≤ Real.exp e := by
    intro z hz
    dsimp [g]
    rw [norm_mul, Complex.norm_exp]
    calc
      _ ≤ Real.exp ((H z).re + e) * Real.exp (-H z).re :=
        mul_le_mul_of_nonneg_right (hupper z hz) (Real.exp_pos _).le
      _ = Real.exp e := by rw [← Real.exp_add]; simp
  have hlog : Real.log ‖g c‖ = Real.log ‖f c‖ - (H c).re := by
    dsimp [g]
    rw [norm_mul, Complex.norm_exp,
      Real.log_mul (norm_ne_zero_iff.mpr hc) (Real.exp_pos _).ne', Real.log_exp]
    simp [sub_eq_add_neg]
  have hcount := CRGLevinAnalytic.zero_count_exp_bound hr he hg hgc hgbound
  have hsub : closedBall c r ⊆ closedBall c (2*r) :=
    closedBall_subset_closedBall (by linarith)
  have hd : MeromorphicOn.divisor g (closedBall c r) =
      MeromorphicOn.divisor f (closedBall c r) :=
    divisor_mul_exp (hf.mono hsub) (hH.neg.mono hsub)
  rw [hd, hlog] at hcount
  exact hcount.trans (div_le_div_of_nonneg_right (by linarith) (Real.log_pos (by norm_num)).le)

/-- The same local count estimate for a harmonic profile. The holomorphic
factor used to cancel it is constructed by harmonic conjugacy on the ball. -/
theorem zero_count_of_harmonic_profile {f : ℂ → ℂ} {H : ℂ → ℝ} {c : ℂ} {r e : ℝ}
    (hr : 0 < r) (he : 0 ≤ e)
    (hf : AnalyticOnNhd ℂ f (closedBall c (2*r)))
    (hH : InnerProductSpace.HarmonicOnNhd H (ball c (4*r))) (hc : f c ≠ 0)
    (hupper : ∀ z ∈ sphere c (2*r), ‖f z‖ ≤ Real.exp (H z + e))
    (hlower : H c - e ≤ Real.log ‖f c‖) :
    (∑ᶠ z, MeromorphicOn.divisor f (closedBall c r) z : ℤ) ≤
      2*e / Real.log 2 := by
  obtain ⟨G, hG, hGre⟩ := hH.exists_analyticOnNhd_ball_re_eq
  have hsub : closedBall c (2*r) ⊆ ball c (4*r) :=
    closedBall_subset_ball (by linarith)
  have hcc : c ∈ ball c (4*r) := by simp only [mem_ball, dist_self]; positivity
  apply zero_count_of_analytic_profile hr he hf (hG.mono hsub) hc
  · intro z hz
    have hzre : (G z).re = H z := hGre (hsub (sphere_subset_closedBall hz))
    rw [hzre]
    exact hupper z hz
  · have hcre : (G c).re = H c := hGre hcc
    rw [hcre]
    exact hlower

#print axioms divisor_mul_exp
#print axioms zero_count_of_analytic_profile
#print axioms zero_count_of_harmonic_profile
end CRGZeroDistributionLocal
