import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.WallisRecurrence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Parts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.PiPeriod
import Mathlib.Data.Nat.Choose.Central
import Batteries.Tactic.OpenPrivate

/-!
Finite Wallis integral identities (K03.18.wallis). All integrations use the
upstream proper Darboux integral. Continuity gives integrability, the upstream
Newton–Leibniz theorem gives the two initial values, and upstream integration
by parts gives the recurrence. The two closed formulas then follow by natural
induction using Mathlib's elementary central-binomial identity. No Beta/Gamma,
measure-integral comparison, or limiting Wallis product is used here.
-/
noncomputable section
namespace SingleVariableAnalysis.Wallis
open Set Riemann
open private parts_continuous_real_integrable from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Parts
open Specs.SingleVariableAnalysis.Ch18.WallisRecurrence

/-- The proper Wallis integral; its Darboux integrability is proved below. -/
def wallisIntegral : ℕ → ℝ := integralValue
/-- The normalized central binomial coefficient. -/
def wallisCoefficient : ℕ → ℝ := coefficientValue

private theorem integrable_power (n : ℕ) :
    RealIntegrable (sinePower n) 0 (Real.pi / 2) :=
  parts_continuous_real_integrable Real.pi_div_two_pos.le
    (Real.continuous_sin.pow n).continuousOn

private theorem integral_eq (n : ℕ) (h : RealIntegrable (sinePower n) 0 (Real.pi / 2)) :
    wallisIntegral n = realIntegral _ h := by
  exact (realIntegral_common_value _ h Real.pi_div_two_pos.le (sinePowerBounded n)).1.symm

theorem wallis_integrability : integrability := by
  intro n
  exact ⟨integrable_power n, integral_eq n (integrable_power n)⟩

theorem wallis_series_representation : seriesRepresentation := by
  have hs : Specs.SingleVariableAnalysis.Ch07.SinCos.realSeriesSinValue = Real.sin :=
    funext fun x => (sinCosSeries_eq_real x).1
  have hp : Specs.SingleVariableAnalysis.Ch07.PiPeriod.analyticPiValue = Real.pi :=
    PiPeriod.analyticPi_eq_pi
  unfold seriesRepresentation
  rw [hs, hp]
  intro n
  exact ⟨integrable_power n, integral_eq n (integrable_power n)⟩

theorem wallis_zero : initialZero := by
  have h := real_ftc_second (fun x : ℝ => x) (sinePower 0) 0 (Real.pi / 2)
    Real.pi_div_two_pos.le continuousOn_id
    (fun x _ => by simpa [sinePower] using! hasDerivAt_id x) (integrable_power 0)
  change wallisIntegral 0 = Real.pi / 2
  exact (integral_eq 0 (integrable_power 0)).trans (by simpa using h)

theorem wallis_one : initialOne := by
  have h := real_ftc_second (fun x : ℝ => -Real.cos x) (sinePower 1) 0 (Real.pi / 2)
    Real.pi_div_two_pos.le Real.continuous_cos.neg.continuousOn
    (fun x _ => by simpa [sinePower] using! (Real.hasDerivAt_cos x).neg) (integrable_power 1)
  change wallisIntegral 1 = 1
  exact (integral_eq 1 (integrable_power 1)).trans (by simpa using h)


private theorem integral_congr {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b) (he : f = g) :
    realIntegral f hf = realIntegral g hg := by
  subst g
  rfl

/-- Integration by parts, with the vanishing boundary terms kept explicit. -/
theorem wallis_step (k : ℕ) :
    wallisIntegral (k + 2) = ((k : ℝ) + 1) * wallisIntegral k / ((k : ℝ) + 2) := by
  let u : ℝ → ℝ := fun x => Real.sin x ^ (k + 1)
  let v : ℝ → ℝ := fun x => -Real.cos x
  let du : ℝ → ℝ := fun x => ((k : ℝ) + 1) * Real.sin x ^ k * Real.cos x
  let dv : ℝ → ℝ := Real.sin
  have hdu : Continuous du :=
    (continuous_const.mul (Real.continuous_sin.pow k)).mul Real.continuous_cos
  obtain ⟨h₁, h₂, hp⟩ := real_parts u v du dv 0 (Real.pi / 2) Real.pi_div_two_pos.le
    (Real.continuous_sin.pow (k + 1)).continuousOn
    Real.continuous_cos.neg.continuousOn
    (fun x _ => by simpa [u, du] using! (Real.hasDerivAt_sin x).pow (k + 1))
    (fun x _ => by simpa [v, dv] using! (Real.hasDerivAt_cos x).neg)
    (parts_continuous_real_integrable Real.pi_div_two_pos.le hdu.continuousOn)
    (parts_continuous_real_integrable Real.pi_div_two_pos.le Real.continuous_sin.continuousOn)
  have he₁ : realIntegral _ h₁ = wallisIntegral (k + 2) := by
    exact (integral_congr h₁ (integrable_power (k + 2))
      (by funext x; simp [u, dv, sinePower, pow_succ])).trans
      (integral_eq _ _).symm
  obtain ⟨hn, hen⟩ := real_mul_value (integrable_power (k + 2)) (-1)
  obtain ⟨hs, hes⟩ := real_add_value (integrable_power k) hn
  obtain ⟨hm, hem⟩ := real_mul_value hs (-((k : ℝ) + 1))
  have he₂ : realIntegral _ h₂ =
      -((k : ℝ) + 1) * (wallisIntegral k - wallisIntegral (k + 2)) := by
    calc
      realIntegral _ h₂ = realIntegral _ hm := integral_congr h₂ hm (by
        funext x
        dsimp [du, v, sinePower]
        have hc : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
          nlinarith [Real.sin_sq_add_cos_sq x]
        rw [pow_add]
        calc
          _ = -((k : ℝ) + 1) * Real.sin x ^ k * Real.cos x ^ 2 := by ring
          _ = _ := by rw [hc]; ring
        )
      _ = -((k : ℝ) + 1) * (wallisIntegral k - wallisIntegral (k + 2)) := by
        rw [hem, hes, hen, ← integral_eq k, ← integral_eq (k + 2)]
        ring
  change realIntegral _ h₁ = _ - realIntegral _ h₂ at hp
  rw [he₁, he₂] at hp
  have hb : u (Real.pi / 2) * v (Real.pi / 2) - u 0 * v 0 = 0 := by
    simp [u, v]
  rw [hb] at hp
  apply (eq_div_iff (by positivity : (k : ℝ) + 2 ≠ 0)).mpr
  nlinarith [hp]

theorem wallis_recurrence : recurrence := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have he : 2 + k = k + 2 := by omega
  rw [he]
  simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat, add_sub_cancel_right,
    show (k : ℝ) + 2 - 1 = (k : ℝ) + 1 by ring, wallisIntegral] using wallis_step k


/-- Positivity includes the zeroth coefficient. -/
theorem wallisCoefficient_positive (n : ℕ) : 0 < wallisCoefficient n :=
  div_pos (Nat.cast_pos.mpr (Nat.centralBinom_pos n)) (by positivity)

/-- The elementary central-binomial identity after normalization by 4ⁿ. -/
theorem wallisCoefficient_step (n : ℕ) :
    (2 * (n : ℝ) + 2) * wallisCoefficient (n + 1) =
      (2 * n + 1) * wallisCoefficient n := by
  have h : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  change (2 * (n : ℝ) + 2) * ((Nat.centralBinom (n + 1) : ℝ) / 4 ^ (n + 1)) =
    (2 * n + 1) * ((Nat.centralBinom n : ℝ) / 4 ^ n)
  rw [pow_succ]
  field_simp
  nlinarith [h]

theorem wallis_even : evenFormula := by
  change ∀ n, wallisIntegral (2 * n) = (Real.pi / 2) * wallisCoefficient n
  intro n
  induction n with
  | zero => simpa [wallisCoefficient, coefficientValue, wallisIntegral, initialZero] using wallis_zero
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, wallis_step, ih]
    push_cast
    apply (div_eq_iff (by positivity : 2 * (n : ℝ) + 2 ≠ 0)).mpr
    linear_combination -(Real.pi / 2) * (wallisCoefficient_step n)

theorem wallis_odd : oddFormula := by
  change ∀ n, wallisIntegral (2 * n + 1) = 1 / ((2 * (n : ℝ) + 1) * wallisCoefficient n)
  intro n
  induction n with
  | zero => simpa [wallisCoefficient, coefficientValue, wallisIntegral, initialOne] using wallis_one
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, wallis_step, ih]
    push_cast
    have hc : wallisCoefficient n ≠ 0 := (wallisCoefficient_positive n).ne'
    have hc' : wallisCoefficient (n + 1) ≠ 0 := (wallisCoefficient_positive (n + 1)).ne'
    field_simp
    nlinarith [wallisCoefficient_step n]

/-- Increasing the power decreases the integrand on the first quadrant. -/
theorem wallis_succ_le (n : ℕ) : wallisIntegral (n + 1) ≤ wallisIntegral n := by
  rw [integral_eq (n + 1) (integrable_power (n + 1)), integral_eq n (integrable_power n)]
  apply realIntegral_mono _ _ (integrable_power (n + 1)) (integrable_power n)
  intro x hx
  exact pow_le_pow_of_le_one
    (Real.sin_nonneg_of_mem_Icc ⟨hx.1, hx.2.trans (by linarith [Real.pi_pos])⟩)
    (Real.sin_le_one x) (Nat.le_succ n)

theorem wallis_sandwich : sandwich := by
  intro n
  exact ⟨wallis_succ_le (2 * n + 1), wallis_succ_le (2 * n)⟩

end SingleVariableAnalysis.Wallis


