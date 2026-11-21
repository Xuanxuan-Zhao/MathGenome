import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.GammaRecurrence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Ratio
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Radius
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.Ring

noncomputable section
namespace SingleVariableAnalysis.DivergentAsymptotic
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace S
export Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic
  (kernelValue functionValue coefficientValue truncationValue remainderValue)
end S

def kernel : ℝ → ℝ → ℝ := S.kernelValue
def F : ℝ → ℝ := S.functionValue
def coefficient : ℕ → ℝ := S.coefficientValue
def truncation : ℕ → ℝ → ℝ := S.truncationValue
def remainder : ℕ → ℝ → ℝ := S.remainderValue

/-- The Gamma kernel at a positive integer is the ordinary monomial moment. -/
lemma moment_eq_gammaKernel (n : ℕ) :
    (fun t : ℝ => t^n * Real.exp (-t)) = gammaKernel ((n : ℝ)+1) := by
  funext t
  simp [gammaKernel, GSpec.gammaKernelValue, Real.rpow_natCast]

lemma moment_integrable (n : ℕ) :
    IntegrableOn (fun t : ℝ => t^n * Real.exp (-t)) (Ioi 0) := by
  rw [moment_eq_gammaKernel]
  exact gammaKernel_integrable (by positivity)

lemma moment_integral (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^n * Real.exp (-t)) = (n.factorial : ℝ) := by
  rw [moment_eq_gammaKernel]
  have hi := gammaKernel_integrable (s := (n : ℝ)+1) (by positivity)
  have he := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi zero_le_one))
  exact he.symm.trans (gamma_factorial_values n)

lemma denominator_ge_one {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    1 ≤ 1 + x*t := le_add_of_nonneg_right (mul_nonneg hx.le ht)

lemma quotient_continuousAt (n : ℕ) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    ContinuousAt (fun t : ℝ => t^n * Real.exp (-t) / (1+x*t)) t := by
  exact ((continuousAt_id.pow n).mul
    (Real.continuous_exp.continuousAt.comp continuousAt_id.neg)).div
    (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (denominator_ge_one hx ht.le)))

lemma quotient_bound (n : ℕ) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    ‖t^n * Real.exp (-t) / (1+x*t)‖ ≤ t^n * Real.exp (-t) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_self (by positivity) (denominator_ge_one hx ht.le)

lemma quotient_integrable (n : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t^n * Real.exp (-t) / (1+x*t)) (Ioi 0) := by
  apply (moment_integrable n).mono'
    ((show ContinuousOn (fun t : ℝ => t^n * Real.exp (-t) / (1+x*t)) (Ioi 0) from
      fun t ht => (quotient_continuousAt n hx ht).continuousWithinAt).aestronglyMeasurable
      measurableSet_Ioi)
  exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht => quotient_bound n hx ht

/-- Transfer to independent proper Darboux limits; continuity is needed for
local Riemann integrability and measure integrability controls both tails. -/
lemma hasIntegral_of_positive_integrable {f : ℝ → ℝ}
    (hc : ∀ t : ℝ, 0 < t → ContinuousAt f t)
    (hi : IntegrableOn f (Ioi 0)) :
    Riemann.Improper.HasIntegral .real f (0 : WithBot ℝ) ⊤
      (show ℝ from ∫ t in Ioi (0 : ℝ), f t) := by
  refine ⟨?_, ⟨1, WithBot.coe_lt_coe.mpr zero_lt_one, WithTop.coe_lt_top _⟩, ?_⟩
  · intro u v hu huv _
    exact (positive_continuous_darboux hc (WithBot.coe_lt_coe.mp hu) huv).choose
  · obtain ⟨hl, hr⟩ := positive_integrable_independent hc hi
    exact ⟨_, _, hl, hr, (intervalIntegral.integral_interval_add_Ioi hi
      (hi.mono_set (Ioi_subset_Ioi zero_le_one))).symm⟩

lemma kernel_eq_quotient (x : ℝ) :
    S.kernelValue x = fun t : ℝ => t^0 * Real.exp (-t) / (1+x*t) := by
  funext t
  simp [S.kernelValue]

theorem hasIntegral : Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic.hasIntegral := by
  intro x hx
  change Riemann.Improper.HasIntegral .real (S.kernelValue x) _ _ _
  unfold S.functionValue
  rw [kernel_eq_quotient]
  exact hasIntegral_of_positive_integrable (fun t ht => quotient_continuousAt 0 hx ht)
    (quotient_integrable 0 hx)

theorem independentLimits :
    Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic.independentLimits := by
  intro x hx
  rw [kernel_eq_quotient]
  exact positive_integrable_independent (fun t ht => quotient_continuousAt 0 hx ht)
    (quotient_integrable 0 hx)

theorem absoluteConvergence :
    Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic.absoluteConvergence := by
  intro x hx
  change ∃ L : ℝ, Riemann.Improper.HasIntegral .real
    (fun t => ‖S.kernelValue x t‖) (0 : WithBot ℝ) ⊤ L
  rw [kernel_eq_quotient]
  exact ⟨_, hasIntegral_of_positive_integrable
    (fun t ht => (quotient_continuousAt 0 hx ht).norm) (quotient_integrable 0 hx).norm⟩

theorem remainderHasIntegral :
    Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic.remainderHasIntegral := by
  intro N x hx
  exact hasIntegral_of_positive_integrable (fun t ht => quotient_continuousAt N hx ht)
    (quotient_integrable N hx)

/-- Integrated form of the exact finite geometric step. -/
lemma quotient_integral_step (N : ℕ) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), t^N * Real.exp (-t) / (1+x*t)) =
      (N.factorial : ℝ) - x *
        ∫ t in Ioi (0 : ℝ), t^(N+1) * Real.exp (-t) / (1+x*t) := by
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        (t^N * Real.exp (-t) - x * (t^(N+1) * Real.exp (-t) / (1+x*t))) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hd : 1+x*t ≠ 0 := ne_of_gt
        (lt_of_lt_of_le zero_lt_one (denominator_ge_one hx ht.le))
      apply (div_eq_iff hd).mpr
      rw [sub_mul, mul_assoc x, div_mul_cancel₀ _ hd, pow_succ]
      ring
    _ = _ := by
      rw [integral_sub (moment_integrable N) ((quotient_integrable (N+1) hx).const_mul x),
        integral_const_mul, moment_integral]

lemma remainder_step (N : ℕ) {x : ℝ} (hx : 0 < x) :
    S.remainderValue N x = S.coefficientValue N * x^N + S.remainderValue (N+1) x := by
  unfold S.remainderValue S.coefficientValue
  rw [quotient_integral_step N hx, pow_succ]
  have he : (-x)^N = (-1 : ℝ)^N * x^N := by rw [← mul_pow]; congr 1; ring
  rw [he]
  ring

/-- N = 0 is also true and makes induction on truncation length direct. -/
lemma expansion_all (N : ℕ) {x : ℝ} (hx : 0 < x) :
    S.functionValue x = S.truncationValue N x + S.remainderValue N x := by
  induction N with
  | zero => simp [S.functionValue, S.truncationValue, S.remainderValue, S.kernelValue]
  | succ N ih =>
    rw [S.truncationValue, Finset.sum_range_succ]
    change S.functionValue x =
      (S.truncationValue N x + S.coefficientValue N * x^N) + S.remainderValue (N+1) x
    rw [ih, remainder_step N hx]
    ring

theorem expansion : Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic.expansion := by
  intro N x _hN hx
  exact expansion_all N hx

lemma remainder_bound_all (N : ℕ) {x : ℝ} (hx : 0 < x) :
    |S.remainderValue N x| ≤ (N.factorial : ℝ) * x^N := by
  have hb : |∫ t in Ioi (0 : ℝ), t^N * Real.exp (-t) / (1+x*t)| ≤ (N.factorial : ℝ) := by
    simpa only [Real.norm_eq_abs, moment_integral] using
      (norm_integral_le_of_norm_le (moment_integrable N)
        ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => quotient_bound N hx ht))
  rw [S.remainderValue, abs_mul, abs_pow, abs_neg, abs_of_pos hx]
  calc
    _ ≤ x^N * (N.factorial : ℝ) := mul_le_mul_of_nonneg_left hb (pow_nonneg hx.le N)
    _ = _ := mul_comm _ _

theorem remainderBound : Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic.remainderBound := by
  intro N x _hN hx
  exact remainder_bound_all N hx

lemma norm_coefficient (n : ℕ) : ‖S.coefficientValue n‖ = (n.factorial : ℝ) := by
  simp [S.coefficientValue, norm_mul, norm_pow]

lemma coefficient_ratio (n : ℕ) :
    ‖S.coefficientValue (n+1)‖ / ‖S.coefficientValue n‖ = (n : ℝ)+1 := by
  rw [norm_coefficient, norm_coefficient, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

/-- The library formal multilinear representation has the same zero radius. -/
lemma formal_radius_zero : (FormalMultilinearSeries.ofScalars ℝ S.coefficientValue).radius = 0 := by
  apply FormalMultilinearSeries.ofScalars_radius_eq_zero_of_tendsto
  simpa only [coefficient_ratio] using
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

lemma norm_term (n : ℕ) (x : ℝ) :
    ‖S.coefficientValue n * x^n‖ = (n.factorial : ℝ) * |x|^n := by
  rw [norm_mul, norm_coefficient, norm_pow, Real.norm_eq_abs]

theorem termsNotTendstoZero :
    Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic.termsNotTendstoZero := by
  intro x hx hlim
  have hp : SequenceEventually (fun n => 0 < ‖S.coefficientValue n * x^n‖) := by
    refine ⟨0, fun n _ => ?_⟩
    dsimp only
    rw [norm_term]
    exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)) (pow_pos (abs_pos.mpr hx) n)
  have hg : SequenceEventually
      (fun n => ‖S.coefficientValue n * x^n‖ ≤ ‖S.coefficientValue (n+1) * x^(n+1)‖) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / |x|)
    refine ⟨N, fun n hn => ?_⟩
    have hbig : 1 ≤ ((n : ℝ)+1) * |x| := by
      have hh := (div_lt_iff₀ (abs_pos.mpr hx)).mp
        (hN.trans_le (Nat.cast_le.mpr hn))
      nlinarith [abs_pos.mpr hx]
    dsimp only
    rw [norm_term, norm_term, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
    calc
      _ ≤ (((n : ℝ)+1) * |x|) * ((n.factorial : ℝ) * |x|^n) :=
        le_mul_of_one_le_left (by positivity) hbig
      _ = _ := by ring
  exact not_zero_limit_of_eventual_growth _ hp hg
    ((realSequenceConverges_iff _ _).mpr (by simpa only [norm_zero] using hlim.norm))

theorem seriesDiverges : Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic.seriesDiverges := by
  intro x hx hc
  exact termsNotTendstoZero x hx
    ((realSequenceConverges_iff _ _).mp (real_series_term_limit _ hc))

/-- Identify the radius using the existing coefficient-root definition.
The interior condition for radius zero is empty; the exterior condition is
ordinary numerical divergence at every nonzero real argument. -/
theorem radiusZero : Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic.radiusZero := by
  change realPowerSeriesRadius S.coefficientValue = 0
  symm
  apply real_powerSeries_radius_unique S.coefficientValue 0 0
  · intro x hx
    exact (not_lt_of_ge bot_le hx).elim
  · intro x hx
    have hne : x ≠ 0 := by
      intro h
      simp [h] at hx
    intro hc
    apply seriesDiverges x hne
    change RealSeriesConverges (fun n => S.coefficientValue n * x^n)
    change RealSeriesConverges (fun n => S.coefficientValue n * (x-0)^n) at hc
    simpa only [sub_zero] using hc

/-- One additional term converts the factorial big-O bound into little-o
at every fixed order. The constants may depend on that order. -/
theorem allOrders : Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic.allOrders := by
  intro m
  have hb : Asymptotics.IsBigO (𝓝[>] (0 : ℝ))
      (fun x => S.functionValue x - S.truncationValue (m+1) x) (fun x => x^(m+1)) := by
    apply Asymptotics.IsBigO.of_bound ((m+1).factorial : ℝ)
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : 0 < x := hx
    change |S.functionValue x - S.truncationValue (m+1) x| ≤
      ((m+1).factorial : ℝ) * |x^(m+1)|
    rw [abs_pow, abs_of_pos hx']
    have he := expansion_all (m+1) hx
    have hr : S.functionValue x - S.truncationValue (m+1) x = S.remainderValue (m+1) x := by
      linarith
    rw [hr]
    exact remainder_bound_all (m+1) hx
  exact hb.trans_isLittleO
    ((Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (Nat.lt_succ_self m)).mono nhdsWithin_le_nhds)

end SingleVariableAnalysis.DivergentAsymptotic
