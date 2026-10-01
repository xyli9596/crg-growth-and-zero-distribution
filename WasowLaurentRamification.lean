import WasowLaurentGauge
import Mathlib.RingTheory.PowerSeries.Expand

/-! Actual Laurent substitution by a positive integral power, its chain rule,
and pullback of differential gauge equations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace WasowLaurentRamification
open WasowLaurentGauge

def exponentMap (p : ℕ) : ℤ →+ ℤ where
  toFun n := (p : ℤ)*n
  map_zero' := mul_zero _
  map_add' := mul_add _

/-- The genuine Laurent-series ring homomorphism `f(t) ↦ f(t^p)`. -/
def ramify (p : ℕ) (hp : 0 < p) : L →+* L :=
  HahnSeries.embDomainRingHom (exponentMap p)
    (fun a b h => (mul_left_cancel₀ (by exact_mod_cast hp.ne') h))
    (fun a b => by change (p : ℤ)*a ≤ (p : ℤ)*b ↔ a ≤ b; exact mul_le_mul_iff_right₀ (by exact_mod_cast hp))

@[simp] theorem ramify_coeff_mul (p : ℕ) (hp : 0 < p) (f : L) (n : ℤ) :
    (ramify p hp f).coeff ((p : ℤ)*n) = f.coeff n :=
  HahnSeries.embDomain_coeff

theorem ramify_coeff_of_not_dvd (p : ℕ) (hp : 0 < p) (f : L) (n : ℤ)
    (hn : ¬(p : ℤ) ∣ n) : (ramify p hp f).coeff n = 0 := by
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨k, hk⟩
  exact hn ⟨k, hk.symm⟩

@[simp] theorem ramify_single (p : ℕ) (hp : 0 < p) (n : ℤ) (c : ℂ) :
    ramify p hp (HahnSeries.single n c) = HahnSeries.single ((p : ℤ)*n) c :=
  HahnSeries.embDomain_single

@[simp] theorem ramify_one (f : L) : ramify 1 (by omega) f = f := by
  ext n
  simpa using ramify_coeff_mul 1 (by omega) f n

theorem ramify_comp (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (f : L) :
    ramify p hp (ramify q hq f) = ramify (p*q) (Nat.mul_pos hp hq) f := by
  ext n
  by_cases hn : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [ramify_coeff_mul]
    by_cases hk : (q : ℤ) ∣ k
    · obtain ⟨l, rfl⟩ := hk
      rw [ramify_coeff_mul, ← mul_assoc, ← Nat.cast_mul, ramify_coeff_mul]
    · rw [ramify_coeff_of_not_dvd _ _ _ _ hk, ramify_coeff_of_not_dvd]
      intro h
      obtain ⟨l, hl⟩ := h
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
      apply hk
      refine ⟨l, mul_left_cancel₀ hp0 ?_⟩
      simpa only [Nat.cast_mul, mul_assoc] using hl
  · rw [ramify_coeff_of_not_dvd _ _ _ _ hn, ramify_coeff_of_not_dvd]
    intro h
    apply hn
    exact dvd_trans (by exact ⟨(q : ℤ), by simp⟩) h

/-- The derivative of the substituted variable `t^p`, as a true Laurent series. -/
def jacobian (p : ℕ) : L := HahnSeries.single ((p : ℤ)-1) (p : ℂ)

/-- The chain rule holds for all Laurent series, including series with poles. -/
theorem derivative_ramify (p : ℕ) (hp : 0 < p) (f : L) :
    D (ramify p hp f) = jacobian p * ramify p hp (D f) := by
  ext n
  rw [derivative_coeff, jacobian, HahnSeries.coeff_single_mul]
  by_cases hn : (p : ℤ) ∣ n+1
  · obtain ⟨k, hk⟩ := hn
    have hs : n-((p : ℤ)-1) = (p : ℤ)*(k-1) := by rw [mul_sub, mul_one]; omega
    rw [hk, ramify_coeff_mul, hs, ramify_coeff_mul, derivative_coeff]
    have hk' : k-1+1 = k := by omega
    rw [hk']
    have hc := congrArg (fun z : ℤ => (z : ℂ)) hk
    push_cast at hc ⊢
    rw [hc]
    ring
  · rw [ramify_coeff_of_not_dvd _ _ _ _ hn, ramify_coeff_of_not_dvd]
    · simp
    · intro h
      apply hn
      have := dvd_add h (show (p : ℤ) ∣ (p : ℤ) by exact dvd_rfl)
      have he : n-((p : ℤ)-1)+(p : ℤ)=n+1 := by ring
      rwa [he] at this

theorem ramify_powerSeries (p : ℕ) (hp : 0 < p) (f : PowerSeries ℂ) :
    ramify p hp (f : L) = (PowerSeries.expand p hp.ne' f : L) := by
  ext n
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [LaurentSeries.coeff_coe_powerSeries]
    by_cases hm : p ∣ m
    · obtain ⟨k, rfl⟩ := hm
      rw [Nat.cast_mul, ramify_coeff_mul, LaurentSeries.coeff_coe_powerSeries,
        PowerSeries.coeff_expand_mul]
    · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hm, ramify_coeff_of_not_dvd]
      exact_mod_cast hm
  · rw [PowerSeries.coeff_coe, if_pos (by omega)]
    by_cases hd : (p : ℤ) ∣ n
    · obtain ⟨k, rfl⟩ := hd
      rw [ramify_coeff_mul, PowerSeries.coeff_coe, if_pos]
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp
      nlinarith
    · exact ramify_coeff_of_not_dvd p hp _ _ hd

variable {ι κ ν : Type*}

def ramifyMatrix (p : ℕ) (hp : 0 < p) (A : Matrix ι κ L) : Matrix ι κ L :=
  fun i j => ramify p hp (A i j)

def pullback (p : ℕ) (hp : 0 < p) (A : Matrix ι κ L) : Matrix ι κ L :=
  fun i j => jacobian p * ramify p hp (A i j)

theorem ramifyMatrix_mul [Fintype κ] (p : ℕ) (hp : 0 < p)
    (A : Matrix ι κ L) (B : Matrix κ ν L) :
    ramifyMatrix p hp (A*B) = ramifyMatrix p hp A * ramifyMatrix p hp B := by
  apply Matrix.ext
  intro i j
  simp only [ramifyMatrix, Matrix.mul_apply, map_sum, map_mul]

theorem matrixDerivative_ramify (p : ℕ) (hp : 0 < p) (A : Matrix ι κ L) :
    matrixDerivative (ramifyMatrix p hp A) = pullback p hp (matrixDerivative A) := by
  apply Matrix.ext
  intro i j
  exact derivative_ramify p hp (A i j)

theorem gaugeEquation_ramify [Fintype ι] [Fintype κ]
    (p : ℕ) (hp : 0 < p) (A : Matrix ι ι L) (G : Matrix ι κ L)
    (B : Matrix κ κ L) (h : GaugeEquation A G B) :
    GaugeEquation (pullback p hp A) (ramifyMatrix p hp G) (pullback p hp B) := by
  unfold GaugeEquation at *
  apply Matrix.ext
  intro i j
  have hij := congrArg (fun M : Matrix ι κ L => ramify p hp (M i j)) h
  simp only [Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul] at hij
  simp only [Matrix.sub_apply, Matrix.mul_apply, pullback, ramifyMatrix, matrixDerivative]
  rw [derivative_ramify]
  simp_rw [mul_assoc, mul_left_comm (ramify p hp (G i _))]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub, hij]
  rfl

theorem ramifyMatrix_inverses [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (p : ℕ) (hp : 0 < p) (P : Matrix ι κ L) (Q : Matrix κ ι L)
    (hPQ : P*Q=1) (hQP : Q*P=1) :
    ramifyMatrix p hp P * ramifyMatrix p hp Q = 1 ∧
    ramifyMatrix p hp Q * ramifyMatrix p hp P = 1 := by
  constructor
  · rw [← ramifyMatrix_mul, hPQ]
    apply Matrix.ext
    intro i j
    simp [ramifyMatrix, Matrix.one_apply]
  · rw [← ramifyMatrix_mul, hQP]
    apply Matrix.ext
    intro i j
    simp [ramifyMatrix, Matrix.one_apply]

theorem jacobian_comp (p q : ℕ) (hp : 0 < p) :
    jacobian (p*q) = jacobian p * ramify p hp (jacobian q) := by
  simp only [jacobian, ramify_single, HahnSeries.single_mul_single, Nat.cast_mul]
  congr 1
  ring

theorem ramifyMatrix_comp (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (A : Matrix ι κ L) :
    ramifyMatrix p hp (ramifyMatrix q hq A) =
      ramifyMatrix (p*q) (Nat.mul_pos hp hq) A := by
  apply Matrix.ext
  intro i j
  exact ramify_comp p q hp hq (A i j)

theorem pullback_comp (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (A : Matrix ι κ L) :
    pullback p hp (pullback q hq A) = pullback (p*q) (Nat.mul_pos hp hq) A := by
  apply Matrix.ext
  intro i j
  simp only [pullback, map_mul, ramify_comp, jacobian_comp p q hp, mul_assoc]

#print axioms jacobian_comp
#print axioms ramifyMatrix_comp
#print axioms pullback_comp

#print axioms ramify_coeff_mul
#print axioms ramify_coeff_of_not_dvd
#print axioms ramify_single
#print axioms ramify_one
#print axioms ramify_comp
#print axioms derivative_ramify
#print axioms ramify_powerSeries
#print axioms ramifyMatrix_mul
#print axioms matrixDerivative_ramify
#print axioms gaugeEquation_ramify
#print axioms ramifyMatrix_inverses
end WasowLaurentRamification
