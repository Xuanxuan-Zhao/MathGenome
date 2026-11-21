import MathGenome.Internal.RealAnalysis.Specs.D11.Ch16.ConditionalImproperCounterexample
import MathGenome.Internal.RealAnalysis.D11.Ch16.ProperIntegralEquality
import MathGenome.Internal.RealAnalysis.D11.Ch05.MonotoneSeries
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
namespace D11.Ch16.ConditionalImproperCounterexample

abbrev stepFunction : ℝ → ℝ :=
  Specs.D11.Ch16.ConditionalImproperCounterexample.stepFunction_value

local notation "mL" => Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure ℝ)
local notation "μL" => Specs.D11.Ch02.Completion.completedMeasure_value (volume : Measure ℝ)

lemma value_below_one {x : ℝ} (hx : x < 1) : stepFunction x = 0 := by
  simp [stepFunction, Specs.D11.Ch16.ConditionalImproperCounterexample.stepFunction_value,
    Nat.floor_eq_zero.mpr hx]

lemma value_on_cell (n : ℕ) {x : ℝ} (hx : x ∈ Ico (n : ℝ) ((n : ℝ) + 1)) :
    stepFunction x = (-1 : ℝ) ^ n / (n : ℝ) := by
  have hn : ⌊x⌋₊ = n := (Nat.floor_eq_iff (le_trans (by positivity : (0 : ℝ) ≤ n) hx.1)).mpr hx
  simp [stepFunction, Specs.D11.Ch16.ConditionalImproperCounterexample.stepFunction_value, hn]

theorem exact_values : Specs.D11.Ch16.ConditionalImproperCounterexample.exact_values := by
  exact ⟨fun _ hx => value_below_one hx, fun n _ _ hx => value_on_cell n hx⟩

lemma measurable_step : Measurable stepFunction := by
  exact (measurable_of_countable (fun n : ℕ => (-1 : ℝ) ^ n / (n : ℝ))).comp
    Nat.measurable_floor

lemma abs_value (x : ℝ) : |stepFunction x| = 1 / (⌊x⌋₊ : ℝ) := by
  simp [stepFunction, Specs.D11.Ch16.ConditionalImproperCounterexample.stepFunction_value,
    abs_div, abs_pow]

lemma abs_le_one (x : ℝ) : |stepFunction x| ≤ 1 := by
  rw [abs_value]
  by_cases hn : ⌊x⌋₊ = 0
  · simp [hn]
  · have hn' : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact (div_le_one (by positivity : (0 : ℝ) < ⌊x⌋₊)).mpr hn'

lemma continuous_off_naturals {x : ℝ} (hx : x ∉ Set.range (fun n : ℕ => (n : ℝ))) :
    ContinuousAt stepFunction x := by
  by_cases hx1 : x < 1
  · have he : stepFunction =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx1] with y hy
      exact value_below_one hy
    exact continuousAt_const.congr_of_eventuallyEq he
  · have hx0 : 0 ≤ x := by linarith
    have hlo : (⌊x⌋₊ : ℝ) < x := (Nat.floor_le hx0).lt_of_ne (by
      intro h
      exact hx ⟨⌊x⌋₊, h⟩)
    have hhi : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have he : stepFunction =ᶠ[𝓝 x] fun _ => (-1 : ℝ) ^ ⌊x⌋₊ / (⌊x⌋₊ : ℝ) := by
      filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
      exact value_on_cell _ ⟨hy.1.le, hy.2⟩
    exact continuousAt_const.congr_of_eventuallyEq he

local instance completed_noAtoms : @NullSingletonClass ℝ mL μL := by
  constructor
  intro x
  change volume {x} = 0
  simp

theorem local_riemann_integrable :
    Specs.D11.Ch16.ConditionalImproperCounterexample.local_riemann_integrable := by
  intro a b _ hab
  rcases hab.eq_or_lt with h | h
  · subst b
    exact SingleVariableAnalysis.Riemann.realIntegrable_degenerate _ _
  · apply (D11.Ch16.RiemannCriterion.riemann_criterion stepFunction a b h _).mpr
    · apply measure_mono_null (t := Set.range (fun n : ℕ => (n : ℝ)))
      · intro x hx
        by_contra hn
        exact hx.2 (continuous_off_naturals hn).continuousWithinAt
      · exact (Set.countable_range _).measure_zero μL
    · constructor
      · refine ⟨-1, ?_⟩
        rintro _ ⟨x, _, rfl⟩
        exact (abs_le.mp (abs_le_one x)).1
      · refine ⟨1, ?_⟩
        rintro _ ⟨x, _, rfl⟩
        exact (abs_le.mp (abs_le_one x)).2


lemma completedSet {s : Set ℝ} (hs : MeasurableSet s) : MeasurableSet[mL] s :=
  hs.nullMeasurableSet

lemma completed_measurable_step : @Measurable ℝ ℝ mL (borel ℝ) stepFunction := by
  intro s hs
  exact completedSet (measurable_step hs)

lemma integrableOn_Ico (a b : ℝ) : IntegrableOn stepFunction (Ico a b) μL := by
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ico a b) μL :=
    integrableOn_const (by change volume (Ico a b) ≠ ∞; simp)
  exact hc.mono' completed_measurable_step.stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using abs_le_one x))

lemma cell_integral (n : ℕ) :
    (∫ x in Ico (n : ℝ) ((n : ℝ) + 1), stepFunction x ∂μL) =
      (-1 : ℝ) ^ n / (n : ℝ) := by
  rw [setIntegral_congr_fun (completedSet measurableSet_Ico) (fun x hx => value_on_cell n hx),
    setIntegral_const]
  change (volume (Ico (n : ℝ) ((n : ℝ) + 1))).toReal • _ = _
  simp

lemma split_integral {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ x in Ico a c, stepFunction x ∂μL) =
      (∫ x in Ico a b, stepFunction x ∂μL) +
      ∫ x in Ico b c, stepFunction x ∂μL := by
  rw [← Ico_union_Ico_eq_Ico hab hbc]
  exact setIntegral_union (by exact disjoint_left.mpr (fun x hx hy => not_lt.mpr hy.1 hx.2))
    (completedSet measurableSet_Ico) (integrableOn_Ico a b) (integrableOn_Ico b c)

lemma integer_integral (n : ℕ) :
    (∫ x in Ico 0 (n : ℝ), stepFunction x ∂μL) =
      ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (i : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, split_integral (b := (n : ℝ)) (by positivity) (by linarith), ih,
      cell_integral, Finset.sum_range_succ]

lemma real_endpoint_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in Icc 0 R, stepFunction x ∂μL) =
      (∑ i ∈ Finset.range ⌊R⌋₊, (-1 : ℝ) ^ i / (i : ℝ)) +
      (R - (⌊R⌋₊ : ℝ)) * ((-1 : ℝ) ^ ⌊R⌋₊ / (⌊R⌋₊ : ℝ)) := by
  rw [integral_Icc_eq_integral_Ico, split_integral (by positivity) (Nat.floor_le hR),
    integer_integral]
  congr 1
  rw [setIntegral_congr_fun (completedSet measurableSet_Ico) (fun x hx =>
    value_on_cell ⌊R⌋₊ ⟨hx.1, hx.2.trans (Nat.lt_floor_add_one R)⟩), setIntegral_const]
  change (volume (Ico (⌊R⌋₊ : ℝ) R)).toReal • _ = _
  rw [Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr (Nat.floor_le hR))]
  rfl

lemma alternating_partial_sums_converge :
    ∃ L : ℝ, Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      (-1 : ℝ) ^ i / (i : ℝ)) atTop (𝓝 L) := by
  have hanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    intro n m hnm
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hz : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero hz
  refine ⟨-l, (tendsto_add_atTop_iff_nat 1).mp ?_⟩
  convert hl.neg using 1
  funext n
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.cast_zero, div_zero, add_zero, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_succ, Nat.cast_add, Nat.cast_one]
  ring

lemma partial_cell_tends_zero : Tendsto (fun R : ℝ =>
    (R - (⌊R⌋₊ : ℝ)) * ((-1 : ℝ) ^ ⌊R⌋₊ / (⌊R⌋₊ : ℝ))) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun R : ℝ => 1 / (⌊R⌋₊ : ℝ))
  · intro R
    by_cases hR : 0 ≤ R
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le hR))]
      have hc : |(-1 : ℝ) ^ ⌊R⌋₊ / (⌊R⌋₊ : ℝ)| = 1 / (⌊R⌋₊ : ℝ) := by
        simp [abs_div, abs_pow]
      rw [hc]
      calc
        _ ≤ 1 * (1 / (⌊R⌋₊ : ℝ)) := mul_le_mul_of_nonneg_right
          (by linarith [Nat.lt_floor_add_one R]) (by positivity)
        _ = _ := one_mul _
    · have hn : ⌊R⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      simp [hn]
  · simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp
        (tendsto_nat_floor_atTop (α := ℝ))

lemma completed_integrals_converge :
    ∃ L : ℝ, Tendsto (fun R : ℝ => ∫ x in Icc 0 R, stepFunction x ∂μL)
      atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := alternating_partial_sums_converge
  refine ⟨L, ?_⟩
  have ht := (hL.comp (tendsto_nat_floor_atTop (α := ℝ))).add partial_cell_tends_zero
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  exact (real_endpoint_integral hR).symm

theorem improper_converges : Specs.D11.Ch16.ConditionalImproperCounterexample.improper_converges := by
  obtain ⟨L, hL⟩ := completed_integrals_converge
  refine ⟨L, fun ε hε => ?_⟩
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp hL ε hε
  refine ⟨max A 0, le_max_right _ _, fun R hR hRI => ?_⟩
  have heq := D11.Ch16.ProperIntegralEquality.real_integral_eq stepFunction hRI
  change |SingleVariableAnalysis.Riemann.realIntegral stepFunction hRI - L| < ε
  rw [heq, integral_indicator (completedSet measurableSet_Icc)]
  exact (Real.dist_eq _ _).symm ▸ hA R ((le_max_left _ _).trans hR)


/-- Both residue classes of the harmonic series diverge. -/
lemma reciprocal_residue_not_summable (c : ℕ) (hc : 1 ≤ c) (hc2 : c ≤ 2) :
    ¬ Summable (fun n : ℕ => 1 / ((2 * n + c : ℕ) : ℝ)) := by
  intro hs
  have htwo := hs.mul_left 2
  have hmajor : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ htwo
    intro n
    have hden : 0 < ((2 * n + c : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * n + c)
    rw [mul_one_div, div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1) hden]
    have hcr : (c : ℝ) ≤ 2 := by exact_mod_cast hc2
    push_cast
    nlinarith
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hmajor

lemma reciprocal_residue_tsum (c : ℕ) (hc : 1 ≤ c) (hc2 : c ≤ 2) :
    (∑' n : ℕ, ENNReal.ofReal (1 / ((2 * n + c : ℕ) : ℝ))) = ∞ := by
  by_contra h
  have hs := ENNReal.summable_toReal h
  apply reciprocal_residue_not_summable c hc hc2
  convert hs using 1
  funext n
  exact (ENNReal.toReal_ofReal (by positivity)).symm

/-- A lower bound from disjoint unit cells suffices; nothing is assumed about
measurability of arbitrary subsets or about signed integrability. -/
lemma divergent_of_cell_values (g : ℝ → ℝ≥0∞) (c : ℕ) (hc : 1 ≤ c) (hc2 : c ≤ 2)
    (hg : ∀ n : ℕ, ∀ x ∈ Ico ((2 * n + c : ℕ) : ℝ) (((2 * n + c : ℕ) : ℝ) + 1),
      g x = ENNReal.ofReal (1 / ((2 * n + c : ℕ) : ℝ))) :
    (∫⁻ x in Ici 0, g x ∂μL) = ∞ := by
  let E (n : ℕ) := Ico ((2 * n + c : ℕ) : ℝ) (((2 * n + c : ℕ) : ℝ) + 1)
  have hdis : Pairwise (fun n m => Disjoint (E n) (E m)) := by
    intro n m hnm
    apply disjoint_left.mpr
    intro x hxn hxm
    have hn := Nat.floor_eq_on_Ico (2 * n + c) x hxn
    have hm := Nat.floor_eq_on_Ico (2 * m + c) x hxm
    exact hnm (by omega)
  have hcell (n : ℕ) : (∫⁻ x in E n, g x ∂μL) =
      ENNReal.ofReal (1 / ((2 * n + c : ℕ) : ℝ)) := by
    rw [setLIntegral_congr_fun (completedSet measurableSet_Ico) (hg n), setLIntegral_const]
    change _ * volume (Ico _ _) = _
    simp
  apply top_unique
  calc
    ∞ = ∑' n : ℕ, ENNReal.ofReal (1 / ((2 * n + c : ℕ) : ℝ)) :=
      (reciprocal_residue_tsum c hc hc2).symm
    _ = ∫⁻ x in ⋃ n : ℕ, E n, g x ∂μL := by
      calc
        _ = ∑' n : ℕ, ∫⁻ x in E n, g x ∂μL := tsum_congr (fun n => (hcell n).symm)
        _ = _ := (lintegral_iUnion (μ := μL)
          (fun n => completedSet measurableSet_Ico) hdis g).symm
    _ ≤ ∫⁻ x in Ici 0, g x ∂μL := lintegral_mono_set (by
      intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact le_trans (by positivity : (0 : ℝ) ≤ (2 * n + c : ℕ)) hn.1)

lemma positive_lintegral_infinite :
    (∫⁻ x in Ici 0, ENNReal.ofReal (max (stepFunction x) 0) ∂μL) = ∞ := by
  apply divergent_of_cell_values _ 2 (by omega) (by omega)
  intro n x hx
  rw [value_on_cell (2 * n + 2) hx]
  simp [pow_add, pow_mul]

lemma negative_lintegral_infinite :
    (∫⁻ x in Ici 0, ENNReal.ofReal (max (-stepFunction x) 0) ∂μL) = ∞ := by
  apply divergent_of_cell_values _ 1 (by omega) (by omega)
  intro n x hx
  rw [value_on_cell (2 * n + 1) hx]
  simp [pow_add, pow_mul, neg_div]

lemma absolute_lintegral_infinite :
    (∫⁻ x in Ici 0, ENNReal.ofReal |stepFunction x| ∂μL) = ∞ := by
  apply top_unique
  rw [← positive_lintegral_infinite]
  apply lintegral_mono
  intro x
  exact ENNReal.ofReal_le_ofReal (max_le (le_abs_self _) (abs_nonneg _))

theorem divergent_parts : Specs.D11.Ch16.ConditionalImproperCounterexample.divergent_parts := by
  refine ⟨completed_measurable_step, ?_, ?_, ?_⟩
  · exact (@D11.Ch05.NonnegativeIntegral.integral_eq_lintegral ℝ mL
      ((μL).restrict (Ici 0)) _).trans absolute_lintegral_infinite
  · exact (@D11.Ch05.NonnegativeIntegral.integral_eq_lintegral ℝ mL
      ((μL).restrict (Ici 0)) _).trans positive_lintegral_infinite
  · exact (@D11.Ch05.NonnegativeIntegral.integral_eq_lintegral ℝ mL
      ((μL).restrict (Ici 0)) _).trans negative_lintegral_infinite

theorem not_scalar_integrable :
    Specs.D11.Ch16.ConditionalImproperCounterexample.not_scalar_integrable := by
  intro h
  have hi : @Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value ℝ mL
      ((μL).restrict (Ici 0)) (fun x => ENNReal.ofReal |stepFunction x|) < ∞ := by
    simpa only [Real.norm_eq_abs] using h.2
  rw [divergent_parts.2.1] at hi
  exact (lt_irrefl _ hi)

end D11.Ch16.ConditionalImproperCounterexample
