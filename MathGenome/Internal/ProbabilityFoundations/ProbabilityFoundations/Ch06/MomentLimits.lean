import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.Portmanteau
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.VaryingMapping
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.MomentLimits
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Moments and expectations under weak convergence (paper.tex 1699–1737).
The law formulation includes random variables on different probability spaces.
The lower bound is extended valued. Uniform integrability gives a common first
absolute-moment bound; bounded continuous truncations then give convergence. -/

open MeasureTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal
open Specs.ProbabilityFoundations.Ch06.MomentLimits

namespace ProbabilityFoundations.Ch06.MomentLimits
universe u
noncomputable section

/-- Portmanteau applied to the nonnegative continuous p-power. -/
theorem moment_lower_bound : momentLowerBoundType := by
  intro μs μ p hp hμ
  apply lintegral_le_liminf_of_open μs μ
    ((weaklyConverges_iff_open μs μ).mp hμ)
  exact (ENNReal.continuous_ofReal.comp
    (continuous_abs.rpow_const (fun _ => Or.inr hp.le))).lowerSemicontinuous

/-- A uniformly integrable family of laws has uniformly bounded first moments. -/
lemma uniform_integral_abs_bound {S : Type u} [MeasurableSpace S]
    (μs : ℕ → ProbabilityMeasure S) (h : S → ℝ) (hm : Measurable h)
    (hui : LawUniformIntegrable μs h) :
    ∃ B : ℝ, ∀ n, ∫ x, |h x| ∂(μs n : Measure S) ≤ B := by
  obtain ⟨R, hR, htail⟩ := hui.2 1 zero_lt_one
  refine ⟨R + 1, fun n => ?_⟩
  let A : Set S := {x | R < |h x|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (by simpa only [Real.norm_eq_abs] using hm.norm)
  have hdom : ∀ x, |h x| ≤ R + A.indicator (fun x => |h x|) x := by
    intro x
    by_cases hx : x ∈ A
    · simpa [hx] using le_add_of_nonneg_left hR (a := |h x|)
    · simpa [hx] using (not_lt.mp hx)
  calc
    _ ≤ ∫ x, R + A.indicator (fun x => |h x|) x ∂(μs n : Measure S) :=
      integral_mono (hui.1 n).abs
        ((integrable_const R).add ((hui.1 n).abs.indicator hA)) hdom
    _ = R + ∫ x in A, |h x| ∂(μs n : Measure S) := by
      rw [integral_add (integrable_const R) ((hui.1 n).abs.indicator hA),
        integral_const, integral_indicator hA]
      simp
    _ ≤ R + 1 := by
      have ht : (∫ x in A, |h x| ∂(μs n : Measure S)) < 1 := htail n
      linarith

/-- The first absolute moment of a weak limit of UI real laws is finite. -/
lemma integrable_id_of_ui (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hui : LawUniformIntegrable μs id) :
    Integrable (fun x : ℝ => x) (μ : Measure ℝ) := by
  obtain ⟨B, hB⟩ := uniform_integral_abs_bound μs id measurable_id hui
  have hport := moment_lower_bound μs μ 1 zero_lt_one hμ
  have hb : ∀ n, absoluteMoment (μs n) 1 ≤ ENNReal.ofReal B := by
    intro n
    simp only [absoluteMoment, Real.rpow_one]
    rw [← ofReal_integral_eq_lintegral_ofReal (by simpa using (hui.1 n).abs)
      (ae_of_all _ abs_nonneg)]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have hfinite : absoluteMoment μ 1 < ∞ :=
    lt_of_le_of_lt (hport.trans (liminf_le_of_frequently_le (Frequently.of_forall hb)))
      ENNReal.ofReal_lt_top
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  simpa [hasFiniteIntegral_iff_norm, absoluteMoment] using hfinite

/-- Symmetric continuous truncation. -/
def clip (R x : ℝ) : ℝ := max (-R) (min x R)

lemma clip_eq (R x : ℝ) (hx : |x| ≤ R) : clip R x = x := by
  rw [clip, min_eq_left (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]

lemma abs_clip_le (R x : ℝ) (hR : 0 ≤ R) : |clip R x| ≤ R := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

lemma abs_clip_le_abs (R x : ℝ) (hR : 0 ≤ R) : |clip R x| ≤ |x| := by
  by_cases hx : |x| ≤ R
  · rw [clip_eq R x hx]
  · exact (abs_clip_le R x hR).trans (not_le.mp hx).le

lemma abs_sub_clip_le (R x : ℝ) (hR : 0 ≤ R) : |x - clip R x| ≤ |x| := by
  unfold clip
  rcases le_total x (-R) with hx | hx
  · rw [min_eq_left (by linarith : x ≤ R), max_eq_left hx,
      abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · by_cases hxR : x ≤ R
    · rw [min_eq_left hxR, max_eq_right hx, sub_self, abs_zero]
      exact abs_nonneg x
    · rw [min_eq_right (not_le.mp hxR).le, max_eq_right (by linarith),
        abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

lemma continuous_clip (R : ℝ) : Continuous (clip R) :=
  continuous_const.max (continuous_id.min continuous_const)

lemma integrable_clip (μ : Measure ℝ) [IsFiniteMeasure μ] (R : ℝ) (hR : 0 ≤ R) :
    Integrable (clip R) μ :=
  Integrable.mono' (integrable_const R) (continuous_clip R).aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using abs_clip_le R x hR))

lemma integral_clip_error (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ => x) μ) (R : ℝ) (hR : 0 ≤ R) :
    |(∫ x, x ∂μ) - ∫ x, clip R x ∂μ| ≤ ∫ x in {x : ℝ | R < |x|}, |x| ∂μ := by
  have hA : MeasurableSet {x : ℝ | R < |x|} :=
    measurableSet_lt measurable_const (by simpa only [Real.norm_eq_abs, id_eq] using (measurable_id : Measurable (id : ℝ → ℝ)).norm)
  rw [← integral_sub hi (integrable_clip μ R hR)]
  calc
    _ ≤ ∫ x, |x - clip R x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x : ℝ => x - clip R x)
    _ ≤ ∫ x, {x : ℝ | R < |x|}.indicator (fun x => |x|) x ∂μ := by
      apply integral_mono (hi.sub (integrable_clip μ R hR)).abs (hi.abs.indicator hA)
      intro x
      by_cases hx : R < |x|
      · simpa [hx] using abs_sub_clip_le R x hR
      · simp [hx, clip_eq R x (not_lt.mp hx)]
    _ = _ := integral_indicator hA

lemma tendsto_integral_clip (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ => x) μ) :
    Tendsto (fun k : ℕ => ∫ x, clip k x ∂μ) atTop (𝓝 (∫ x, x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x : ℝ => |x|)
    (fun k => (continuous_clip k).aestronglyMeasurable) hi.abs
    (fun k => ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using abs_clip_le_abs k x (Nat.cast_nonneg k)))
  apply ae_of_all
  intro x
  obtain ⟨K, hK⟩ := exists_nat_ge |x|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop K] with k hk
  exact (clip_eq k x (hK.trans (by exact_mod_cast hk))).symm

/-- Weak convergence plus uniform absolute tails implies convergence of means. -/
lemma expectation_id_convergence (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hui : LawUniformIntegrable μs id) :
    Integrable (fun x : ℝ => x) (μ : Measure ℝ) ∧
    Tendsto (fun n => ∫ x, x ∂(μs n : Measure ℝ)) atTop
      (𝓝 (∫ x, x ∂(μ : Measure ℝ))) := by
  have hi := integrable_id_of_ui μs μ hμ hui
  refine ⟨hi, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  obtain ⟨R, hR, htail⟩ := hui.2 (ε / 3) (by positivity)
  obtain ⟨K, hK⟩ := exists_nat_ge R
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp (tendsto_integral_clip (μ : Measure ℝ) hi)) (ε / 3) (by positivity))
  let M := max K L
  have hM : R ≤ (M : ℝ) := hK.trans (by exact_mod_cast (le_max_left K L))
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (clip M) (continuous_clip M) M (fun x => by
      simpa only [Real.norm_eq_abs] using abs_clip_le M x (Nat.cast_nonneg M))
  have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) f
  filter_upwards [(Metric.tendsto_nhds.mp hw) (ε / 3) (by positivity)] with n hn
  have herror : |(∫ x, x ∂(μs n : Measure ℝ)) - ∫ x, clip M x ∂(μs n : Measure ℝ)| < ε / 3 := by
    apply lt_of_le_of_lt (integral_clip_error _ (hui.1 n) M (Nat.cast_nonneg M))
    apply lt_of_le_of_lt ?_ (htail n)
    apply setIntegral_mono_set (hui.1 n).abs.integrableOn
      (ae_of_all _ abs_nonneg)
    exact ae_of_all _ (fun x hx => lt_of_le_of_lt hM hx)
  have hlimit := hL M (le_max_right K L)
  rw [Real.dist_eq] at hn
  change |(∫ x, clip M x ∂(μs n : Measure ℝ)) - ∫ x, clip M x ∂(μ : Measure ℝ)| < ε / 3 at hn
  rw [Real.dist_eq] at hlimit ⊢
  calc
    _ ≤ |(∫ x, x ∂(μs n : Measure ℝ)) - ∫ x, clip M x ∂(μs n : Measure ℝ)| +
        |(∫ x, clip M x ∂(μs n : Measure ℝ)) - ∫ x, clip M x ∂(μ : Measure ℝ)| +
        |(∫ x, clip M x ∂(μ : Measure ℝ)) - ∫ x, x ∂(μ : Measure ℝ)| := by
      calc
        _ ≤ |(∫ x, x ∂(μs n : Measure ℝ)) - ∫ x, clip M x ∂(μs n : Measure ℝ)| +
            |(∫ x, clip M x ∂(μs n : Measure ℝ)) - ∫ x, x ∂(μ : Measure ℝ)| := abs_sub_le _ _ _
        _ ≤ _ := by
          simpa only [add_assoc] using add_le_add le_rfl (abs_sub_le
            (∫ x, clip M x ∂(μs n : Measure ℝ))
            (∫ x, clip M x ∂(μ : Measure ℝ))
            (∫ x, x ∂(μ : Measure ℝ)))
    _ < ε := by linarith

/-- Pushforward transfers the uniform tail bounds exactly. -/
lemma lawUniformIntegrable_map {S : Type u} [MeasurableSpace S]
    (μs : ℕ → ProbabilityMeasure S) (h : S → ℝ) (hm : Measurable h)
    (hui : LawUniformIntegrable μs h) :
    LawUniformIntegrable (fun n => (μs n).map h) id := by
  constructor
  · intro n
    exact (integrable_map_measure measurable_id.aestronglyMeasurable hm.aemeasurable).mpr (hui.1 n)
  · intro ε hε
    obtain ⟨R, hR, htail⟩ := hui.2 ε hε
    refine ⟨R, hR, fun n => ?_⟩
    change (∫ x in {x : ℝ | R < |x|}, |x| ∂Measure.map h (μs n : Measure S)) < ε
    rw [setIntegral_map (isOpen_lt continuous_const continuous_abs).measurableSet
      continuous_abs.aestronglyMeasurable hm.aemeasurable]
    exact htail n

/-- Mapping to the real line and truncating proves the general assertion. -/
theorem expectation_convergence : expectationConvergenceType := by
  intro S _ _ _ μs μ h hm hμ hcont hui
  have hweak := almostEverywhere_continuous_mapping μs μ h hm hμ hcont
  obtain ⟨hi, hc⟩ := expectation_id_convergence _ _ hweak
    (lawUniformIntegrable_map μs h hm hui)
  have him : Integrable h (μ : Measure S) := by
    exact (integrable_map_measure measurable_id.aestronglyMeasurable hm.aemeasurable).mp hi
  have he (ν : ProbabilityMeasure S) :
      (∫ x : ℝ, x ∂(ν.map h : Measure ℝ)) = ∫ x, h x ∂(ν : Measure S) :=
    integral_map hm.aemeasurable measurable_id.aestronglyMeasurable
  simp_rw [he] at hc
  exact ⟨him, hc⟩

/-- Uniform integrability upgrades the moment inequality to convergence. -/
theorem moment_convergence : momentConvergenceType := by
  intro μs μ p hp hμ hui
  have hcont : Continuous (fun x : ℝ => |x| ^ p) :=
    continuous_abs.rpow_const (fun _ => Or.inr hp.le)
  obtain ⟨hi, hc⟩ := expectation_convergence μs μ _ hcont.measurable hμ
    (ae_of_all _ (fun x => hcont.continuousAt)) hui
  have he (ν : ProbabilityMeasure ℝ) (hv : Integrable (fun x : ℝ => |x| ^ p) (ν : Measure ℝ)) :
      absoluteMoment ν p = ENNReal.ofReal (∫ x, |x| ^ p ∂(ν : Measure ℝ)) := by
    exact (ofReal_integral_eq_lintegral_ofReal hv
      (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg x) p))).symm
  refine ⟨hi, hc, ?_, ?_⟩
  · rw [he μ hi]
    exact ENNReal.ofReal_lt_top
  · simp_rw [he _ (hui.1 _)]
    rw [he μ hi]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc

/-- Affine domination by a nonnegative UI observable preserves uniform integrability. -/
lemma lawUniformIntegrable_of_growth {S : Type u} [MeasurableSpace S]
    (μs : ℕ → ProbabilityMeasure S) (g h : S → ℝ)
    (hg : Measurable g) (hh : Measurable h) (hg0 : ∀ x, 0 ≤ g x)
    (hui : LawUniformIntegrable μs g) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, |h x| ≤ C * (1 + g x)) : LawUniformIntegrable μs h := by
  have hi (n : ℕ) : Integrable h (μs n : Measure S) :=
    (((integrable_const 1).add (hui.1 n)).const_mul C).mono'
      hh.aestronglyMeasurable (ae_of_all _ (fun x => by
        simpa only [Real.norm_eq_abs, Pi.add_apply] using hbound x))
  refine ⟨hi, ?_⟩
  intro ε hε
  by_cases hC0 : C = 0
  · have hz : h = 0 := by
      funext x
      have hx := hbound x
      simpa [hC0] using hx
    refine ⟨0, le_rfl, fun n => ?_⟩
    simp [hz, hε]
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  obtain ⟨R, hR, htail⟩ := hui.2 (ε / (2 * C)) (by positivity)
  let Q : ℝ := max R 1
  have hQ1 : 1 ≤ Q := le_max_right _ _
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ1
  let A : Set S := {x | C * (1 + Q) < |h x|}
  let B : Set S := {x | R < |g x|}
  have hA : MeasurableSet A := isOpen_lt continuous_const continuous_abs |>.measurableSet |>.preimage hh
  have hB : MeasurableSet B :=
    measurableSet_lt measurable_const (by simpa only [Real.norm_eq_abs] using hg.norm)
  have hA_g : ∀ x ∈ A, Q < g x := by
    intro x hx
    have hb := hbound x
    change C * (1 + Q) < |h x| at hx
    nlinarith
  refine ⟨C * (1 + Q), by positivity, fun n => ?_⟩
  calc
    (∫ x in A, |h x| ∂(μs n : Measure S)) ≤
        ∫ x in A, (2 * C) * |g x| ∂(μs n : Measure S) := by
      apply setIntegral_mono_on (hi n).abs.integrableOn
        (((hui.1 n).abs.const_mul (2 * C)).integrableOn) hA
      intro x hx
      rw [abs_of_nonneg (hg0 x)]
      have hxg := hA_g x hx
      have hb := hbound x
      nlinarith
    _ = (2 * C) * ∫ x in A, |g x| ∂(μs n : Measure S) := integral_const_mul _ _
    _ ≤ (2 * C) * ∫ x in B, |g x| ∂(μs n : Measure S) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply setIntegral_mono_set (hui.1 n).abs.integrableOn (ae_of_all _ (fun x => abs_nonneg (g x)))
      apply ae_of_all
      intro x hx
      exact (le_max_left R 1).trans_lt (hA_g x hx) |>.trans_le (le_abs_self _)
    _ < ε := by
      have ht := htail n
      have hmul := (mul_lt_mul_iff_right₀ (show 0 < 2 * C by positivity)).mpr ht
      have he : ε / (2 * C) * (2 * C) = ε := div_mul_cancel₀ ε (ne_of_gt (by positivity : 0 < 2 * C))
      dsimp [B] at *
      nlinarith

/-- Continuous observables of at most p-power growth have converging expectations. -/
theorem polynomial_growth_convergence : polynomialGrowthType := by
  intro μs μ p hp hμ hui h C hh hC hb
  have hg : Continuous (fun x : ℝ => |x| ^ p) :=
    continuous_abs.rpow_const (fun _ => Or.inr hp.le)
  exact expectation_convergence μs μ h hh.measurable hμ
    (ae_of_all _ (fun _ => hh.continuousAt))
    (lawUniformIntegrable_of_growth μs _ h hg.measurable hh.measurable
      (fun x => Real.rpow_nonneg (abs_nonneg x) p) hui C hC hb)

lemma spike_weight_nonneg (n : ℕ) : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity

lemma spike_weight_le_one (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
  apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

/-- Normalization of the two-point law, including n=0 (unit mass at one). -/
lemma spike_probability (n : ℕ) : IsProbabilityMeasure (spikeMeasure n) := by
  constructor
  simp only [spikeMeasure, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (spike_weight_nonneg n) (sub_nonneg.mpr (spike_weight_le_one n))]
  simp

lemma integrable_spike (n : ℕ) (f : ℝ → ℝ) : Integrable f (spikeMeasure n) := by
  exact ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

lemma integral_spike (n : ℕ) (f : ℝ → ℝ) :
    (∫ x, f x ∂spikeMeasure n) =
      (1 / ((n : ℝ) + 1)) * f ((n : ℝ) + 1) +
      (1 - 1 / ((n : ℝ) + 1)) * f 0 := by
  have h₁ : Integrable f (ENNReal.ofReal (1 / ((n : ℝ) + 1)) •
      Measure.dirac ((n : ℝ) + 1)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have h₂ : Integrable f (ENNReal.ofReal (1 - 1 / ((n : ℝ) + 1)) • Measure.dirac 0) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [spikeMeasure, integral_add_measure h₁ h₂]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (spike_weight_nonneg n),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (spike_weight_le_one n))]

/-- Bounded first moments do not suffice for convergence of means. -/
theorem spike_counterexample : spikeCounterexampleType := by
  refine ⟨spike_probability, ?_⟩
  let μs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨spikeMeasure n, spike_probability n⟩
  refine ⟨μs, fun _ => rfl, ?_, fun n => integrable_spike n _, ?_, ?_, ?_⟩
  · apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    have ha : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hz : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * f ((n : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) := by
      apply squeeze_zero_norm (fun n => ?_) (by simpa using ha.mul_const ‖f‖)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (spike_weight_nonneg n)]
      simpa only [Real.norm_eq_abs, one_div] using
        mul_le_mul_of_nonneg_left (f.norm_coe_le_norm ((n : ℝ) + 1)) (spike_weight_nonneg n)
    have hconv := hz.add (((tendsto_const_nhds (x := (1 : ℝ))).sub ha).mul_const (f 0))
    change Tendsto (fun n => ∫ x : ℝ, f x ∂spikeMeasure n) atTop
      (𝓝 (∫ x : ℝ, f x ∂Measure.dirac 0))
    simpa only [zero_add, sub_zero, one_mul, integral_spike, integral_dirac] using hconv
  · intro n
    change (∫ x : ℝ, |x| ∂spikeMeasure n) = 1
    rw [integral_spike]
    simp only [abs_zero, mul_zero, add_zero, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
    exact div_mul_cancel₀ 1 (by positivity)
  · intro n
    change (∫ x : ℝ, x ∂spikeMeasure n) = 1
    rw [integral_spike]
    simp only [mul_zero, add_zero]
    exact div_mul_cancel₀ 1 (by positivity)
  · have he : (fun n => ∫ x : ℝ, x ∂(μs n : Measure ℝ)) = fun _ => (1 : ℝ) := by
      funext n
      change (∫ x : ℝ, x ∂spikeMeasure n) = 1
      rw [integral_spike]
      simp only [mul_zero, add_zero]
      exact div_mul_cancel₀ 1 (by positivity)
    rw [he]
    intro ht
    have := tendsto_nhds_unique tendsto_const_nhds ht
    exact one_ne_zero this

end
end ProbabilityFoundations.Ch06.MomentLimits
