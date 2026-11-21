import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch09.Frobenius
import MathGenome.Internal.ODEDynamics.D13Unified.Ch09.Indicial
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section

namespace D13Unified.Ch09.Frobenius

open Specs.D13Unified.Ch09.Indicial
open Specs.D13Unified.Ch09.Frobenius
open scoped BigOperators
open scoped Topology

/-- The normalized coefficients, defined by recursion on the entire finite
history. The attached sum supplies the strict decrease of every recursive call.
No convergence or differential-equation conclusion is used in this definition. -/
def coefficients (E : Equation) (r : ℂ) (n : ℕ) : ℂ :=
  Nat.strongRecOn n fun n prev =>
    if n = 0 then 1 else
      -(∑ k ∈ (Finset.Icc 1 n).attach,
        ((r + (n : ℂ) - (k.val : ℂ)) * taylorCoefficientValue E.p k.val +
          taylorCoefficientValue E.q k.val) *
          prev (n - k.val) (by
            have hk := Finset.mem_Icc.mp k.property
            omega)) / indicialValue E (r + (n : ℂ))

theorem coefficients_zero (E : Equation) (r : ℂ) : coefficients E r 0 = 1 := by
  rw [coefficients, Nat.strongRecOn_eq]
  simp

theorem coefficients_step (E : Equation) (r : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    coefficients E r n =
      -(∑ k ∈ Finset.Icc 1 n,
        ((r + (n : ℂ) - (k : ℂ)) * taylorCoefficientValue E.p k +
          taylorCoefficientValue E.q k) * coefficients E r (n - k)) /
        indicialValue E (r + (n : ℂ)) := by
  conv_lhs => rw [coefficients, Nat.strongRecOn_eq]
  simp only [ite_eq_right (by omega : n ≠ 0)]
  apply congrArg (fun x : ℂ => -x / indicialValue E (r + (n : ℂ)))
  exact Finset.sum_attach (Finset.Icc 1 n) (fun k =>
    ((r + (n : ℂ) - (k : ℂ)) * taylorCoefficientValue E.p k +
      taylorCoefficientValue E.q k) * coefficients E r (n - k))

theorem coefficients_recurrence (E : Equation) (r : ℂ) (h : Nonresonant E r) :
    IsCoefficientSequence E r (coefficients E r) := by
  refine ⟨coefficients_zero E r, ?_⟩
  intro n hn
  rw [coefficients_step E r n hn]
  exact mul_div_cancel₀ _ (h n hn)

theorem coefficientSequence_unique (E : Equation) (r : ℂ)
    (h : Nonresonant E r) {a c : ℕ → ℂ}
    (ha : IsCoefficientSequence E r a) (hc : IsCoefficientSequence E r c) : a = c := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      exact ha.1.trans hc.1.symm
    · apply mul_left_cancel₀ (h n (by omega))
      rw [ha.2 n (by omega), hc.2 n (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih (n - k) (by
        have := Finset.mem_Icc.mp hk
        omega)]

theorem coefficientUniqueness : coefficientUniquenessType := by
  intro E r h
  exact ⟨coefficients E r, coefficients_recurrence E r h,
    fun _ ha => coefficientSequence_unique E r h ha (coefficients_recurrence E r h)⟩

/-- Factorization for two distinct roots of the actual monic indicial quadratic. -/
theorem indicial_factorization (E : Equation) (r₁ r₂ : ℂ)
    (h₁ : indicialValue E r₁ = 0) (h₂ : indicialValue E r₂ = 0)
    (hne : r₁ ≠ r₂) (z : ℂ) :
    indicialValue E z = (z - r₁) * (z - r₂) := by
  have hprod : (r₁ - r₂) * (r₁ + r₂ + pZeroValue E - 1) = 0 := by
    unfold indicialValue at h₁ h₂
    linear_combination h₁ - h₂
  have hs := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
  have hp : pZeroValue E = 1 - r₁ - r₂ := by
    linear_combination hs
  have hq : qZeroValue E = r₁ * r₂ := by
    unfold indicialValue at h₁
    linear_combination h₁ - r₁ * hs
  rw [indicialValue, hp, hq]
  ring

theorem rootSeparation : rootSeparationType := by
  intro E r₁ r₂ h₁ h₂ hnon
  have hne : r₁ ≠ r₂ := by
    intro heq
    exact hnon 0 (by simp [heq])
  refine ⟨hne, ?_, ?_⟩
  · intro n hn
    rw [indicial_factorization E r₁ r₂ h₁ h₂ hne]
    apply mul_ne_zero
    · simpa only [add_sub_cancel_left] using
        (Nat.cast_ne_zero.mpr (by omega : n ≠ 0) : (n : ℂ) ≠ 0)
    · intro hz
      apply hnon (-(n : ℤ))
      push_cast
      linear_combination hz
  · intro n hn
    rw [indicial_factorization E r₁ r₂ h₁ h₂ hne]
    apply mul_ne_zero
    · intro hz
      apply hnon (n : ℤ)
      push_cast
      linear_combination -hz
    · simpa only [add_sub_cancel_left] using
        (Nat.cast_ne_zero.mpr (by omega : n ≠ 0) : (n : ℂ) ≠ 0)

/-- A derivative formula for the freely chosen branch, derived from its
exponential identity rather than identifying it with the principal logarithm. -/
theorem hasDerivAt_branchLog (E : Equation) (b : LogBranch E.radius)
    {z : ℂ} (hz : z ∈ slitDiscValue E.radius b.angle) :
    HasDerivAt b.log z⁻¹ z := by
  have hgeom := D13Unified.Ch09.Indicial.setup.2.2.1 E.radius b.angle E.radius_pos
  have hd := (b.holomorphic z hz).differentiableAt (hgeom.1.mem_nhds hz)
  have heq : (fun w => Complex.exp (b.log w)) =ᶠ[𝓝 z] (fun w : ℂ => w) :=
    Filter.Eventually.mono (hgeom.1.mem_nhds hz) (fun w hw => b.exp_log w hw)
  have hcomp := hd.hasDerivAt.cexp.congr_of_eventuallyEq heq.symm
  have hm : z * deriv b.log z = 1 := by
    simpa only [b.exp_log z hz] using hcomp.unique (hasDerivAt_id z)
  have hn : z ≠ 0 := hgeom.2.2.2 z hz
  have hv : deriv b.log z = z⁻¹ := by
    apply mul_left_cancel₀ hn
    simpa only [mul_inv_cancel₀ hn] using hm
  exact hd.hasDerivAt.congr_deriv hv

theorem hasDerivAt_branchPower (E : Equation) (b : LogBranch E.radius)
    (r : ℂ) {z : ℂ} (hz : z ∈ slitDiscValue E.radius b.angle) :
    HasDerivAt (powerValue b r) (powerValue b r z * r / z) z := by
  have hd := (Complex.hasDerivAt_exp (r * b.log z)).comp z
    ((hasDerivAt_branchLog E b hz).const_mul r)
  convert hd using 1 <;> first | rfl | simp [powerValue, div_eq_mul_inv, mul_assoc]

/-- Every neighborhood of zero meets the actual branch domain. -/
theorem exists_slitDisc_near_zero (E : Equation) (b : LogBranch E.radius)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ slitDiscValue E.radius b.angle, z ∈ Metric.ball (0 : ℂ) ε := by
  let t : ℝ := min E.radius ε / 2
  have ht : 0 < t := half_pos (lt_min E.radius_pos hε)
  have htR : t < E.radius :=
    (half_lt_self (lt_min E.radius_pos hε)).trans_le (min_le_left _ _)
  have htε : t < ε :=
    (half_lt_self (lt_min E.radius_pos hε)).trans_le (min_le_right _ _)
  have hn : ‖rotation b.angle (t : ℂ)‖ = t := by
    simp [rotation, Complex.norm_exp, abs_of_pos ht]
  refine ⟨rotation b.angle (t : ℂ), ?_, ?_⟩
  · refine ⟨(t : ℂ), ⟨?_, Complex.ofReal_mem_slitPlane.mpr ht⟩, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht] using htR
  · simpa only [Metric.mem_ball, dist_zero_right, hn] using htε

/-- The elementary Wronskian criterion on an open domain. This concerns
restrictions to the domain, not independence of arbitrary ambient values. -/
theorem independent_of_wronskian (E : Equation) (b : LogBranch E.radius)
    (y₁ y₂ : ℂ → ℂ) {z : ℂ} (hz : z ∈ slitDiscValue E.radius b.angle)
    (h₁ : DifferentiableAt ℂ y₁ z) (h₂ : DifferentiableAt ℂ y₂ z)
    (hW : y₁ z * deriv y₂ z - deriv y₁ z * y₂ z ≠ 0) :
    independentValue b y₁ y₂ := by
  intro c₁ c₂ hrel
  have hopen :=
    (D13Unified.Ch09.Indicial.setup.2.2.1 E.radius b.angle E.radius_pos).1
  have heq : (fun w => c₁ * y₁ w + c₂ * y₂ w) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
    Filter.Eventually.mono (hopen.mem_nhds hz) (fun w hw => hrel w hw)
  have hd := ((h₁.hasDerivAt.const_mul c₁).add
    (h₂.hasDerivAt.const_mul c₂)).congr_of_eventuallyEq heq.symm
  have hdv : c₁ * deriv y₁ z + c₂ * deriv y₂ z = 0 :=
    hd.unique (hasDerivAt_const z 0)
  have hv := hrel z hz
  constructor
  · apply (mul_eq_zero.mp (show c₁ *
      (y₁ z * deriv y₂ z - deriv y₁ z * y₂ z) = 0 by
      linear_combination deriv y₂ z * hv - y₂ z * hdv)).resolve_right hW
  · apply (mul_eq_zero.mp (show c₂ *
      (y₁ z * deriv y₂ z - deriv y₁ z * y₂ z) = 0 by
      linear_combination -deriv y₁ z * hv + y₁ z * hdv)).resolve_right hW

/-- Distinct powers times holomorphic multipliers normalized to one are
independent on any of the allowed branch domains. In particular the branch
need not be principal, and no order on the real parts of the exponents is used. -/
theorem independent_normalized_multipliers (E : Equation) (b : LogBranch E.radius)
    (r₁ r₂ : ℂ) (hne : r₁ ≠ r₂) (f₁ f₂ : ℂ → ℂ)
    (hf₁ : DifferentiableOn ℂ f₁ (Metric.ball 0 E.radius))
    (hf₂ : DifferentiableOn ℂ f₂ (Metric.ball 0 E.radius))
    (h₁₀ : f₁ 0 = 1) (h₂₀ : f₂ 0 = 1) :
    independentValue b (fun z => powerValue b r₁ z * f₁ z)
      (fun z => powerValue b r₂ z * f₂ z) := by
  let G : ℂ → ℂ := fun z =>
    (r₂ - r₁) * f₁ z * f₂ z + z * (f₁ z * deriv f₂ z - deriv f₁ z * f₂ z)
  have h0 : (0 : ℂ) ∈ Metric.ball 0 E.radius := Metric.mem_ball_self E.radius_pos
  have hc₁ := hf₁.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds h0)
  have hc₂ := hf₂.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds h0)
  have hcd₁ := (hf₁.deriv Metric.isOpen_ball).continuousOn.continuousAt
    (Metric.isOpen_ball.mem_nhds h0)
  have hcd₂ := (hf₂.deriv Metric.isOpen_ball).continuousOn.continuousAt
    (Metric.isOpen_ball.mem_nhds h0)
  have hcG : ContinuousAt G 0 :=
    ((continuousAt_const.mul hc₁).mul hc₂).add
      (continuousAt_id.mul ((hc₁.mul hcd₂).sub (hcd₁.mul hc₂)))
  have hG0 : G 0 ≠ 0 := by simpa [G, h₁₀, h₂₀] using sub_ne_zero.mpr hne.symm
  obtain ⟨ε, hε, hεG⟩ := Metric.eventually_nhds_iff_ball.mp (hcG.eventually_ne hG0)
  obtain ⟨z, hz, hzε⟩ := exists_slitDisc_near_zero E b hε
  have hGz : G z ≠ 0 := hεG z hzε
  have hgeom := D13Unified.Ch09.Indicial.setup.2.2.1 E.radius b.angle E.radius_pos
  have hzR := hgeom.2.2.1 hz
  have hz0 := hgeom.2.2.2 z hz
  have hd₁ := (hf₁ z hzR).differentiableAt (Metric.isOpen_ball.mem_nhds hzR)
  have hd₂ := (hf₂ z hzR).differentiableAt (Metric.isOpen_ball.mem_nhds hzR)
  have hp₁ := hasDerivAt_branchPower E b r₁ hz
  have hp₂ := hasDerivAt_branchPower E b r₂ hz
  have hy₁ := hp₁.mul hd₁.hasDerivAt
  have hy₂ := hp₂.mul hd₂.hasDerivAt
  apply independent_of_wronskian E b _ _ hz hy₁.differentiableAt hy₂.differentiableAt
  rw [hy₁.deriv, hy₂.deriv]
  simp only [Pi.mul_apply]
  have hW :
      (powerValue b r₁ z * f₁ z) *
          (powerValue b r₂ z * r₂ / z * f₂ z + powerValue b r₂ z * deriv f₂ z) -
        (powerValue b r₁ z * r₁ / z * f₁ z + powerValue b r₁ z * deriv f₁ z) *
          (powerValue b r₂ z * f₂ z) =
      powerValue b r₁ z * powerValue b r₂ z / z * G z := by
    dsimp [G]
    field_simp
    ring
  rw [hW]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _)
    (Complex.exp_ne_zero _)) hz0) hGz

theorem independentMultipliers : independentMultipliersType :=
  independent_normalized_multipliers

/-- The derivative of the derivative of a branch power times an analytic
multiplier, in a form convenient for clearing denominators in the equation. -/
theorem hasDerivAt_deriv_power_mul (E : Equation) (b : LogBranch E.radius)
    (r : ℂ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 E.radius))
    {z : ℂ} (hz : z ∈ slitDiscValue E.radius b.angle) :
    HasDerivAt (deriv (fun w => powerValue b r w * f w))
      (((powerValue b r z * r / z * r * z - powerValue b r z * r) / z ^ 2) * f z +
        powerValue b r z * r / z * deriv f z +
        (powerValue b r z * r / z * deriv f z +
          powerValue b r z * deriv (deriv f) z)) z := by
  have hgeom := D13Unified.Ch09.Indicial.setup.2.2.1 E.radius b.angle E.radius_pos
  have hzR := hgeom.2.2.1 hz
  have hz0 := hgeom.2.2.2 z hz
  have hd := (hf z hzR).differentiableAt (Metric.isOpen_ball.mem_nhds hzR)
  have hdd := (hf.deriv Metric.isOpen_ball z hzR).differentiableAt
    (Metric.isOpen_ball.mem_nhds hzR)
  have hp := hasDerivAt_branchPower E b r hz
  have hdquot := (hp.mul_const r).div (hasDerivAt_id z) hz0
  have hD := (hdquot.mul hd.hasDerivAt).add (hp.mul hdd.hasDerivAt)
  have heq : deriv (fun w => powerValue b r w * f w) =ᶠ[𝓝 z]
      (fun w => powerValue b r w * r / w * f w + powerValue b r w * deriv f w) := by
    apply Filter.Eventually.mono (hgeom.1.mem_nhds hz)
    intro w hw
    have hwR := hgeom.2.2.1 hw
    have hdf := (hf w hwR).differentiableAt (Metric.isOpen_ball.mem_nhds hwR)
    exact ((hasDerivAt_branchPower E b r hw).mul hdf.hasDerivAt).deriv
  convert hD.congr_of_eventuallyEq heq using 1
  simp

/-- A genuine analytic substitution lemma, with all derivatives on the
specified open branch domain. The multiplier identity is supplied separately
by the convergent power-series argument. -/
theorem powerSolutionBridge : powerSolutionBridgeType := by
  intro E b r f hf heq
  have hgeom := D13Unified.Ch09.Indicial.setup.2.2.1 E.radius b.angle E.radius_pos
  have hfirst : ∀ z ∈ slitDiscValue E.radius b.angle,
      HasDerivAt (fun w => powerValue b r w * f w)
        (powerValue b r z * r / z * f z + powerValue b r z * deriv f z) z := by
    intro z hz
    have hzR := hgeom.2.2.1 hz
    have hd := (hf z hzR).differentiableAt (Metric.isOpen_ball.mem_nhds hzR)
    exact (hasDerivAt_branchPower E b r hz).mul hd.hasDerivAt
  refine ⟨fun z hz => (hfirst z hz).differentiableAt.differentiableWithinAt,
    fun z hz => (hasDerivAt_deriv_power_mul E b r f hf hz).differentiableAt.differentiableWithinAt,
    ?_⟩
  intro z hz
  rw [(hfirst z hz).deriv, (hasDerivAt_deriv_power_mul E b r f hf hz).deriv]
  have hz0 := hgeom.2.2.2 z hz
  have hid : z ^ 2 *
      (((powerValue b r z * r / z * r * z - powerValue b r z * r) / z ^ 2) * f z +
        powerValue b r z * r / z * deriv f z +
        (powerValue b r z * r / z * deriv f z + powerValue b r z * deriv (deriv f) z)) +
      z * E.p z * (powerValue b r z * r / z * f z + powerValue b r z * deriv f z) +
      E.q z * (powerValue b r z * f z) =
      powerValue b r z * (z ^ 2 * deriv (deriv f) z +
        z * (2 * r + E.p z) * deriv f z +
        (r * (r - 1) + r * E.p z + E.q z) * f z) := by
    field_simp
    ring
  rw [hid, heq z (hgeom.2.2.1 hz), mul_zero]


/-- At an indicial root the shifted denominator has exactly quadratic growth. -/
theorem indicial_shift (E : Equation) (r : ℂ) (hr : indicialValue E r = 0)
    (n : ℕ) :
    indicialValue E (r + n) = (n : ℂ) * ((n : ℂ) + (2 * r + pZeroValue E - 1)) := by
  unfold indicialValue at *
  linear_combination hr

/-- A quantitative lower bound, retaining the complex absolute value. -/
theorem indicial_norm_lower (E : Equation) (r : ℂ) (hr : indicialValue E r = 0)
    (n : ℕ) (hn : 2 * ‖2 * r + pZeroValue E - 1‖ ≤ (n : ℝ)) :
    (n : ℝ) ^ 2 / 2 ≤ ‖indicialValue E (r + n)‖ := by
  rw [indicial_shift E r hr, norm_mul, Complex.norm_natCast]
  have htri := norm_sub_le ((n : ℂ) + (2 * r + pZeroValue E - 1))
    (2 * r + pZeroValue E - 1)
  simp only [add_sub_cancel_right, Complex.norm_natCast] at htri
  nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    (show 0 ≤ ‖(n : ℂ) + (2 * r + pZeroValue E - 1)‖ - (n : ℝ) / 2 by linarith)]

/-- Absolute summability of the coefficient kernel at every interior positive radius.
This uses the actual Taylor expansions of the supplied holomorphic coefficients. -/
theorem summable_coefficient_kernel (E : Equation) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρR : ρ < E.radius) :
    Summable (fun k : ℕ =>
      (‖taylorCoefficientValue E.p k‖ + ‖taylorCoefficientValue E.q k‖) * ρ ^ k) := by
  have hz : (ρ : ℂ) ∈ Metric.ball (0 : ℂ) E.radius := by
    simpa [Metric.mem_ball, Complex.norm_real, abs_of_nonneg hρ] using hρR
  have hpq := D13Unified.Ch09.Indicial.coefficientExpansion E (ρ : ℂ) hz
  have hp := hpq.1.summable.norm
  have hq := hpq.2.summable.norm
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hρ, add_mul] using hp.add hq

/-- The weighted recurrence estimate used to control the entire coefficient history. -/
theorem weighted_recurrence_bound (E : Equation) (r : ℂ) {a : ℕ → ℂ}
    (ha : IsCoefficientSequence E r a) {ρ B : ℝ} (hρ : 0 ≤ ρ) (_hB : 0 ≤ B)
    (n : ℕ) (hn : 1 ≤ n)
    (hprev : ∀ j < n, ‖a j‖ * ρ ^ j ≤ B) :
    ‖indicialValue E (r + n)‖ * (‖a n‖ * ρ ^ n) ≤
      ((‖r‖ + (n : ℝ) + 1) * B) *
        ∑ k ∈ Finset.Icc 1 n,
          (‖taylorCoefficientValue E.p k‖ + ‖taylorCoefficientValue E.q k‖) * ρ ^ k := by
  have hrec := congrArg norm (ha.2 n hn)
  simp only [norm_mul, norm_neg] at hrec
  calc
    _ = ‖∑ k ∈ Finset.Icc 1 n,
        ((r + (n : ℂ) - k) * taylorCoefficientValue E.p k +
          taylorCoefficientValue E.q k) * a (n - k)‖ * ρ ^ n := by
      rw [← mul_assoc, hrec]
    _ ≤ (∑ k ∈ Finset.Icc 1 n,
        ‖((r + (n : ℂ) - k) * taylorCoefficientValue E.p k +
          taylorCoefficientValue E.q k) * a (n - k)‖) * ρ ^ n :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hρ _)
    _ = ∑ k ∈ Finset.Icc 1 n,
        ‖((r + (n : ℂ) - k) * taylorCoefficientValue E.p k +
          taylorCoefficientValue E.q k) * a (n - k)‖ * ρ ^ n :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 n,
        ((‖r‖ + (n : ℝ) + 1) * B) *
          ((‖taylorCoefficientValue E.p k‖ + ‖taylorCoefficientValue E.q k‖) * ρ ^ k) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
      have hidx : n - k < n := by omega
      have hnr : ‖r + (n : ℂ) - k‖ ≤ ‖r‖ + (n : ℝ) := by
        calc
          _ = ‖r + ((n - k : ℕ) : ℂ)‖ := by rw [Nat.cast_sub hkn]; congr 1; ring
          _ ≤ ‖r‖ + ‖((n - k : ℕ) : ℂ)‖ := norm_add_le _ _
          _ ≤ ‖r‖ + (n : ℝ) := by simp only [Complex.norm_natCast]; gcongr
      have hf :
          ‖(r + (n : ℂ) - k) * taylorCoefficientValue E.p k + taylorCoefficientValue E.q k‖ ≤
          (‖r‖ + (n : ℝ) + 1) *
            (‖taylorCoefficientValue E.p k‖ + ‖taylorCoefficientValue E.q k‖) := by
        calc
          _ ≤ ‖r + (n : ℂ) - k‖ * ‖taylorCoefficientValue E.p k‖ +
              ‖taylorCoefficientValue E.q k‖ := by simpa only [norm_mul] using norm_add_le ((r + (n : ℂ) - k) * taylorCoefficientValue E.p k) (taylorCoefficientValue E.q k)
          _ ≤ (‖r‖ + (n : ℝ)) * ‖taylorCoefficientValue E.p k‖ +
              ‖taylorCoefficientValue E.q k‖ := by gcongr
          _ ≤ _ := by nlinarith [norm_nonneg (taylorCoefficientValue E.p k),
              norm_nonneg (taylorCoefficientValue E.q k), norm_nonneg r,
              mul_nonneg (norm_nonneg r) (norm_nonneg (taylorCoefficientValue E.q k)),
              mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (norm_nonneg (taylorCoefficientValue E.q k))]
      have hpown : ρ ^ n = ρ ^ (n - k) * ρ ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hkn]
      rw [norm_mul, hpown]
      calc
        _ = ‖(r + (n : ℂ) - k) * taylorCoefficientValue E.p k +
              taylorCoefficientValue E.q k‖ * (‖a (n - k)‖ * ρ ^ (n - k)) * ρ ^ k := by ring
        _ ≤ ((‖r‖ + (n : ℝ) + 1) *
            (‖taylorCoefficientValue E.p k‖ + ‖taylorCoefficientValue E.q k‖)) * B * ρ ^ k := by
          gcongr
          exact hprev (n - k) hidx
        _ = _ := by ring
    _ = _ := (Finset.mul_sum _ _ _).symm


/-- Weighted coefficients are bounded at every smaller radius. The finite initial
segment absorbs all small indicial denominators; no uniform nonresonance bound
is added to the hypotheses. -/
theorem weighted_coefficients_bounded (E : Equation) (r : ℂ)
    (hr : indicialValue E r = 0) {a : ℕ → ℂ} (ha : IsCoefficientSequence E r a)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < E.radius) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ‖a n‖ * ρ ^ n ≤ B := by
  let c : ℕ → ℝ := fun k =>
    (‖taylorCoefficientValue E.p k‖ + ‖taylorCoefficientValue E.q k‖) * ρ ^ k
  have hc := summable_coefficient_kernel E hρ hρR
  have hc0 : ∀ k, 0 ≤ c k := fun k =>
    mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg hρ k)
  let S : ℝ := ∑' k, c k
  have hS : 0 ≤ S := tsum_nonneg hc0
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max 1 (max (2 * ‖2 * r + pZeroValue E - 1‖) (2 * (‖r‖ + 2) * S)))
  let B : ℝ := ∑ j ∈ Finset.range N, ‖a j‖ * ρ ^ j
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (pow_nonneg hρ j)
  refine ⟨B, hB, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hnN : n < N
    · exact Finset.single_le_sum (fun j _ => mul_nonneg (norm_nonneg _) (pow_nonneg hρ j))
        (Finset.mem_range.mpr hnN)
    · have hNn : (N : ℝ) ≤ n := by exact_mod_cast (by omega : N ≤ n)
      have hn1 : 1 ≤ (n : ℝ) := (le_max_left _ _).trans (hN.le.trans hNn)
      have hn : 1 ≤ n := by exact_mod_cast hn1
      have hnpos : (0 : ℝ) < n := by linarith
      have halpha : 2 * ‖2 * r + pZeroValue E - 1‖ ≤ (n : ℝ) :=
        (le_max_left _ _).trans ((le_max_right _ _).trans (hN.le.trans hNn))
      have hcut : 2 * (‖r‖ + 2) * S ≤ (n : ℝ) :=
        (le_max_right _ _).trans ((le_max_right _ _).trans (hN.le.trans hNn))
      have hrec := weighted_recurrence_bound E r ha hρ hB n hn ih
      have hpartial : ∑ k ∈ Finset.Icc 1 n, c k ≤ S :=
        hc.sum_le_tsum _ (fun k _ => hc0 k)
      have hrec' : (n : ℝ) ^ 2 / 2 * (‖a n‖ * ρ ^ n) ≤
          ((‖r‖ + (n : ℝ) + 1) * B) * S := by
        calc
          _ ≤ ‖indicialValue E (r + n)‖ * (‖a n‖ * ρ ^ n) :=
            mul_le_mul_of_nonneg_right (indicial_norm_lower E r hr n halpha)
              (mul_nonneg (norm_nonneg _) (pow_nonneg hρ _))
          _ ≤ _ := hrec.trans (mul_le_mul_of_nonneg_left hpartial (by positivity))
      have hlin : ‖r‖ + (n : ℝ) + 1 ≤ (‖r‖ + 2) * n := by
        nlinarith [mul_nonneg (norm_nonneg r) (sub_nonneg.mpr hn1)]
      have hscalar : (‖r‖ + (n : ℝ) + 1) * S ≤ (n : ℝ) ^ 2 / 2 := by
        calc
          _ ≤ ((‖r‖ + 2) * n) * S := mul_le_mul_of_nonneg_right hlin hS
          _ ≤ (n : ℝ) ^ 2 / 2 := by nlinarith [mul_le_mul_of_nonneg_right hcut (le_of_lt hnpos)]
      have hrec'' : (n : ℝ) ^ 2 / 2 * (‖a n‖ * ρ ^ n) ≤ (n : ℝ) ^ 2 / 2 * B := by
        calc
          _ ≤ ((‖r‖ + (n : ℝ) + 1) * B) * S := hrec'
          _ = ((‖r‖ + (n : ℝ) + 1) * S) * B := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hscalar hB
      exact (mul_le_mul_iff_right₀ (by positivity : 0 < (n : ℝ) ^ 2 / 2)).mp hrec''

/-- Full-disc absolute convergence, deduced from the original recurrence and
holomorphy hypotheses. This is a lower bound by the original radius, and
allows terminating solutions whose radius is larger. -/
theorem coefficientSeries_summable (E : Equation) (r : ℂ)
    (hr : indicialValue E r = 0) {a : ℕ → ℂ} (ha : IsCoefficientSequence E r a)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) E.radius) :
    Summable (fun n : ℕ => ‖a n * z ^ n‖) := by
  have hzR : ‖z‖ < E.radius := by simpa using hz
  obtain ⟨ρ, hzρ, hρR⟩ := exists_between hzR
  have hρ : 0 < ρ := (norm_nonneg z).trans_lt hzρ
  obtain ⟨B, hB, hbound⟩ := weighted_coefficients_bounded E r hr ha hρ.le hρR
  have ht0 : 0 ≤ ‖z‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have ht1 : ‖z‖ / ρ < 1 := (div_lt_one hρ).mpr hzρ
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _
    ((summable_geometric_of_lt_one ht0 ht1).mul_left B)
  intro n
  rw [norm_mul, norm_pow]
  calc
    _ = (‖a n‖ * ρ ^ n) * (‖z‖ / ρ) ^ n := by
      rw [div_pow]; field_simp
    _ ≤ B * (‖z‖ / ρ) ^ n :=
      mul_le_mul_of_nonneg_right (hbound n) (pow_nonneg ht0 n)


/-- Local uniform convergence on a smaller disc follows from absolute convergence
at an intermediate positive real point. -/
theorem scalarSeries_holomorphic {R : ℝ} (a : ℕ → ℂ)
    (habs : ∀ z ∈ Metric.ball (0 : ℂ) R, Summable (fun n : ℕ => ‖a n * z ^ n‖)) :
    DifferentiableOn ℂ (series a) (Metric.ball 0 R) := by
  intro z hz
  have hzR : ‖z‖ < R := by simpa using hz
  obtain ⟨ρ, hzρ, hρR⟩ := exists_between hzR
  have hρ : 0 < ρ := (norm_nonneg z).trans_lt hzρ
  have hρmem : (ρ : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, Complex.norm_real, abs_of_pos hρ] using hρR
  have hu : Summable (fun n => ‖a n‖ * ρ ^ n) := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ] using habs (ρ : ℂ) hρmem
  have hloc : DifferentiableOn ℂ (series a) (Metric.ball 0 ρ) := by
    apply Complex.differentiableOn_tsum_of_summable_norm hu
      (fun n => ((differentiableOn_const (a n)).mul (differentiableOn_id.pow n))) Metric.isOpen_ball
    intro n w hw
    change ‖a n * w ^ n‖ ≤ ‖a n‖ * ρ ^ n
    rw [norm_mul, norm_pow]
    gcongr
    simpa using (Metric.mem_ball.mp hw).le
  exact (hloc.differentiableAt (Metric.isOpen_ball.mem_nhds (by simpa using hzρ))).differentiableWithinAt

theorem scalarSeries_hasSum_first {R : ℝ} (a : ℕ → ℂ)
    (habs : ∀ z ∈ Metric.ball (0 : ℂ) R, Summable (fun n : ℕ => ‖a n * z ^ n‖))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    HasSum (firstTerm a z) (deriv (series a) z) := by
  have hzR : ‖z‖ < R := by simpa using hz
  obtain ⟨ρ, hzρ, hρR⟩ := exists_between hzR
  have hρ : 0 < ρ := (norm_nonneg z).trans_lt hzρ
  have hρmem : (ρ : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, Complex.norm_real, abs_of_pos hρ] using hρR
  have hu : Summable (fun n => ‖a n‖ * ρ ^ n) := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ] using habs (ρ : ℂ) hρmem
  have hsum : HasSum (fun n : ℕ => deriv (fun w : ℂ => a n * w ^ n) z)
      (deriv (series a) z) := by
    apply Complex.hasSum_deriv_of_summable_norm (U := Metric.ball (0 : ℂ) ρ) hu
      (fun n => ((differentiableOn_const (a n)).mul (differentiableOn_id.pow n))) Metric.isOpen_ball
      _ (by simpa using hzρ)
    intro n w hw
    change ‖a n * w ^ n‖ ≤ ‖a n‖ * ρ ^ n
    rw [norm_mul, norm_pow]
    gcongr
    simpa using (Metric.mem_ball.mp hw).le
  have htail := (hasSum_nat_add_iff' 1).mpr hsum
  change HasSum (fun n : ℕ => (n + 1 : ℂ) * a (n + 1) * z ^ n) _
  simpa [deriv_const_mul_field, deriv_pow_field, firstTerm, mul_assoc, mul_comm, mul_left_comm]
    using htail


/-- Full absolute and differentiated convergence, with derivatives of the
actual sum, for every recurrent coefficient sequence. -/
theorem coefficientSeries_analytic (E : Equation) (r : ℂ)
    (hr : indicialValue E r = 0) {a : ℕ → ℂ} (ha : IsCoefficientSequence E r a) :
    AnalyticSeries E a := by
  have habs := fun z hz => coefficientSeries_summable E r hr ha (z := z) hz
  have hhol := scalarSeries_holomorphic a habs
  let d : ℕ → ℂ := fun n => (n + 1 : ℂ) * a (n + 1)
  have hdabs : ∀ z ∈ Metric.ball (0 : ℂ) E.radius,
      Summable (fun n : ℕ => ‖d n * z ^ n‖) := by
    intro z hz
    exact (scalarSeries_hasSum_first a habs hz).summable.norm
  have heq : ∀ z ∈ Metric.ball (0 : ℂ) E.radius,
      deriv (series a) z = series d z := by
    intro z hz
    exact (scalarSeries_hasSum_first a habs hz).tsum_eq.symm
  refine ⟨hhol, hhol.deriv Metric.isOpen_ball, ?_, ?_⟩
  · rw [series, tsum_eq_single 0]
    · simpa using ha.1
    · intro n hn
      simp [zero_pow hn]
  · intro z hz
    have hfirst := scalarSeries_hasSum_first a habs hz
    have hsecond := scalarSeries_hasSum_first d hdabs hz
    have heq' : deriv (series a) =ᶠ[𝓝 z] series d :=
      Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hz) fun w hw => heq w hw
    have hsecond' : HasSum (secondTerm a z) (deriv (deriv (series a)) z) := by
      rw [heq'.deriv_eq]
      convert hsecond using 1
      funext n
      dsimp [firstTerm, secondTerm, d]
      rw [show n + 1 + 1 = n + 2 by omega]
      push_cast
      ring
    exact ⟨habs z hz, (habs z hz).of_norm.hasSum,
      hfirst.summable.norm, hfirst, hsecond'.summable.norm, hsecond'⟩


/-- The Euler derivatives of a convergent scalar power series, with unshifted
indices. The vanishing initial terms are inserted explicitly. -/
theorem coefficientSeries_euler (E : Equation) (r : ℂ)
    (hr : indicialValue E r = 0) {a : ℕ → ℂ} (ha : IsCoefficientSequence E r a)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) E.radius) :
    HasSum (fun n : ℕ => (n : ℂ) * a n * z ^ n) (z * deriv (series a) z) ∧
    HasSum (fun n : ℕ => (n : ℂ) * ((n : ℂ) - 1) * a n * z ^ n)
      (z ^ 2 * deriv (deriv (series a)) z) := by
  have H := (coefficientSeries_analytic E r hr ha).2.2.2 z hz
  constructor
  · have ht : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * a (n + 1) * z ^ (n + 1))
        (z * deriv (series a) z) := by
      convert H.2.2.2.1.mul_left z using 1
      funext n
      simp only [firstTerm, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    apply (hasSum_nat_add_iff' 1).mp
    simpa using ht
  · have ht : HasSum (fun n : ℕ => ((n + 2 : ℕ) : ℂ) * (((n + 2 : ℕ) : ℂ) - 1) *
        a (n + 2) * z ^ (n + 2)) (z ^ 2 * deriv (deriv (series a)) z) := by
      convert H.2.2.2.2.2.mul_left (z ^ 2) using 1
      funext n
      simp only [secondTerm, Nat.cast_add, Nat.cast_ofNat, pow_add]
      ring
    apply (hasSum_nat_add_iff' 2).mp
    simpa [Finset.sum_range_succ] using ht

/-- Scalar Cauchy multiplication with the powers collected by total degree. -/
theorem cauchy_powerSeries {u v : ℕ → ℂ} {z U V : ℂ}
    (hu : HasSum (fun n : ℕ => u n * z ^ n) U)
    (hv : HasSum (fun n : ℕ => v n * z ^ n) V) :
    HasSum (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), u k * v (n - k)) * z ^ n)
      (U * V) := by
  have hh := hasSum_sum_range_mul_of_summable_norm hu.summable.norm hv.summable.norm
  rw [hu.tsum_eq, hv.tsum_eq] at hh
  convert hh using 1
  funext n
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
  have hpow : z ^ n = z ^ k * z ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk']
  rw [hpow]
  ring

private theorem sum_range_zero_add_Icc (f : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), f k = f 0 + ∑ k ∈ Finset.Icc 1 n, f k := by
  have hs : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hs, Finset.sum_insert (by simp)]

/-- Matching the coefficient of each total degree in the analytic multiplier
residual, with the exact `Icc 1 n` recurrence from the manuscript. -/
theorem multiplier_coefficient_zero (E : Equation) (r : ℂ)
    (hr : indicialValue E r = 0) {a : ℕ → ℂ} (ha : IsCoefficientSequence E r a)
    (n : ℕ) :
    (r + (n : ℂ)) * (r + (n : ℂ) - 1) * a n +
      (∑ k ∈ Finset.range (n + 1),
        taylorCoefficientValue E.p k * ((r + ((n - k : ℕ) : ℂ)) * a (n - k))) +
      (∑ k ∈ Finset.range (n + 1), taylorCoefficientValue E.q k * a (n - k)) = 0 := by
  rw [sum_range_zero_add_Icc, sum_range_zero_add_Icc]
  simp only [Nat.sub_zero]
  have hsum :
      (∑ k ∈ Finset.Icc 1 n,
        taylorCoefficientValue E.p k * ((r + ((n - k : ℕ) : ℂ)) * a (n - k))) +
      (∑ k ∈ Finset.Icc 1 n, taylorCoefficientValue E.q k * a (n - k)) =
      ∑ k ∈ Finset.Icc 1 n,
        ((r + (n : ℂ) - (k : ℂ)) * taylorCoefficientValue E.p k +
          taylorCoefficientValue E.q k) * a (n - k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.cast_sub (Finset.mem_Icc.mp hk).2]
    ring
  have hrec : indicialValue E (r + (n : ℂ)) * a n +
      ∑ k ∈ Finset.Icc 1 n,
        ((r + (n : ℂ) - (k : ℂ)) * taylorCoefficientValue E.p k +
          taylorCoefficientValue E.q k) * a (n - k) = 0 := by
    by_cases hn : n = 0
    · subst n
      simpa using congrArg (fun w : ℂ => w * a 0) hr
    · exact eq_neg_iff_add_eq_zero.mp (ha.2 n (by omega))
  unfold indicialValue pZeroValue qZeroValue at hrec
  linear_combination hrec + hsum

/-- The recurrence becomes the differential equation after absolute Cauchy
multiplication and justified termwise differentiation. -/
theorem coefficientSeries_multiplierEquation (E : Equation) (r : ℂ)
    (hr : indicialValue E r = 0) {a : ℕ → ℂ} (ha : IsCoefficientSequence E r a) :
    MultiplierEquation E r (series a) := by
  intro z hz
  have H := (coefficientSeries_analytic E r hr ha).2.2.2 z hz
  have he := coefficientSeries_euler E r hr ha hz
  have hbase := H.2.1
  have hb : HasSum (fun n : ℕ => ((r + (n : ℂ)) * a n) * z ^ n)
      (r * series a z + z * deriv (series a) z) := by
    convert (hbase.mul_left r).add he.1 using 1
    funext n
    ring
  have hc : HasSum (fun n : ℕ => ((r + (n : ℂ)) * (r + (n : ℂ) - 1) * a n) * z ^ n)
      (r * (r - 1) * series a z + (2 * r) * (z * deriv (series a) z) +
        z ^ 2 * deriv (deriv (series a)) z) := by
    convert ((hbase.mul_left (r * (r - 1))).add (he.1.mul_left (2 * r))).add he.2 using 1
    funext n
    ring
  have hpq := D13Unified.Ch09.Indicial.coefficientExpansion E z hz
  have hp := cauchy_powerSeries hpq.1 hb
  have hq := cauchy_powerSeries hpq.2 hbase
  have htotal := (hc.add hp).add hq
  have hzero : (fun n : ℕ =>
      ((r + (n : ℂ)) * (r + (n : ℂ) - 1) * a n) * z ^ n +
      (∑ k ∈ Finset.range (n + 1),
        taylorCoefficientValue E.p k * ((r + ((n - k : ℕ) : ℂ)) * a (n - k))) * z ^ n +
      (∑ k ∈ Finset.range (n + 1), taylorCoefficientValue E.q k * a (n - k)) * z ^ n) =
      fun _ => (0 : ℂ) := by
    funext n
    rw [← add_mul, ← add_mul, multiplier_coefficient_zero E r hr ha, zero_mul]
  rw [hzero] at htotal
  have hv := htotal.unique hasSum_zero
  linear_combination hv


/-- Nonresonant Frobenius construction on the original disc and the supplied
logarithm branch, including coefficient uniqueness and differentiated convergence. -/
theorem frobenius : frobeniusType := by
  intro E b r hr hnon
  obtain ⟨a, ha, huniq⟩ := coefficientUniqueness E r hnon
  refine ⟨a, ⟨ha, coefficientSeries_analytic E r hr ha, ?_⟩, ?_⟩
  · exact powerSolutionBridge E b r (series a)
      (coefficientSeries_analytic E r hr ha).1 (coefficientSeries_multiplierEquation E r hr ha)
  · intro c hc
    exact huniq c hc.1

/-- Both noninteger-separated indicial roots give independent actual functions
on their common, fixed branch domain. Convergence is derived for the supplied
recurrent sequences rather than imposed as an additional hypothesis. -/
theorem independentSolutions : independentSolutionsType := by
  intro E b r₁ r₂ h₁ h₂ hnon a₁ a₂ ha₁ ha₂
  have hsep := rootSeparation E r₁ r₂ h₁ h₂ hnon
  have hs₁ := coefficientSeries_analytic E r₁ h₁ ha₁
  have hs₂ := coefficientSeries_analytic E r₂ h₂ ha₂
  exact independentMultipliers E b r₁ r₂ hsep.1 (series a₁) (series a₂)
    hs₁.1 hs₂.1 hs₁.2.2.1 hs₂.2.2.1

end D13Unified.Ch09.Frobenius
