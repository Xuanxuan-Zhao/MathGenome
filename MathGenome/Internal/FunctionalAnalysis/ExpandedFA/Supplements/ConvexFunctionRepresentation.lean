import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.ConvexFunctionRepresentation
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ExpandedFA.Supplements.ConvexFunctionRepresentation

open Set MeasureTheory
open Filter
open scoped Topology ENNReal NNReal
open ConvexFunctionRepresentationSpec

lemma hinge_nonneg (r : UnitInterval) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ hinge r x := by
  have hd : 0 ≤ 1 - (r : ℝ) := sub_nonneg.mpr r.property.2
  unfold hinge
  split_ifs <;> positivity

@[simp] lemma hinge_zero (r : UnitInterval) : hinge r 0 = 0 := by
  by_cases hr : (r : ℝ) = 1
  · simp [hinge, hr]
  · simp only [hinge, hr, ↓reduceIte]
    rw [max_eq_right (by linarith [r.property.1])]
    simp

@[simp] lemma hinge_one (r : UnitInterval) : hinge r 1 = 1 := by
  by_cases hr : (r : ℝ) = 1
  · simp [hinge, hr]
  · simp only [hinge, hr, ↓reduceIte]
    rw [max_eq_left (by linarith [r.property.2])]
    exact div_self (sub_ne_zero.mpr (Ne.symm hr))

lemma hinge_le_id (r : UnitInterval) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    hinge r x ≤ x := by
  by_cases hr : (r : ℝ) = 1
  · simp only [hinge, hr, ↓reduceIte]
    split_ifs with h
    · exact h ▸ le_rfl
    · exact hx.1
  · have hd : 0 < 1 - (r : ℝ) := sub_pos.mpr (lt_of_le_of_ne r.property.2 hr)
    simp only [hinge, hr, ↓reduceIte]
    apply (div_le_iff₀ hd).mpr
    apply max_le
    · nlinarith [r.property.1, hx.2]
    · exact mul_nonneg hx.1 hd.le

lemma hinge_convex (r : UnitInterval) : ConvexOn ℝ (Icc (0 : ℝ) 1) (hinge r) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  by_cases hr : (r : ℝ) = 1
  · simp only [hinge, hr, ↓reduceIte]
    by_cases hz : a * x + b * y = 1
    · rw [if_pos hz]
      by_cases hax : a = 0 ∨ x = 1
      · by_cases hby : b = 0 ∨ y = 1
        · rcases hax with rfl | rfl <;> rcases hby with rfl | rfl <;>
            simp_all <;> linarith
        · push_neg at hby
          have := mul_pos (lt_of_le_of_ne hb (Ne.symm hby.1))
            (sub_pos.mpr (lt_of_le_of_ne hy.2 hby.2))
          have := mul_nonneg ha (sub_nonneg.mpr hx.2)
          nlinarith
      · push_neg at hax
        have := mul_pos (lt_of_le_of_ne ha (Ne.symm hax.1))
          (sub_pos.mpr (lt_of_le_of_ne hx.2 hax.2))
        have := mul_nonneg hb (sub_nonneg.mpr hy.2)
        nlinarith
    · rw [if_neg hz]
      positivity
  · have hd : 0 < 1 - (r : ℝ) := sub_pos.mpr (lt_of_le_of_ne r.property.2 hr)
    simp only [hinge, hr, ↓reduceIte]
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    apply (div_le_div_iff_of_pos_right hd).mpr
    apply max_le
    · have h1 := le_max_left (x - (r : ℝ)) 0
      have h2 := le_max_left (y - (r : ℝ)) 0
      nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
    · positivity

lemma hinge_eq_zero_of_lt {r : UnitInterval} {x : ℝ} (hx : x < (r : ℝ)) :
    hinge r x = 0 := by
  have hx1 : x ≠ 1 := ne_of_lt (hx.trans_le r.property.2)
  simp [hinge, hx1, max_eq_right (sub_nonpos.mpr hx.le)]

/-- For fixed x the parameter function is continuous, even at r=1. -/
lemma continuous_hinge_parameter {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Continuous (fun r : UnitInterval => hinge r x) := by
  by_cases hx1 : x = 1
  · subst x
    simpa only [hinge_one] using (continuous_const : Continuous (fun _ : UnitInterval => (1 : ℝ)))
  apply continuous_iff_continuousAt.mpr
  intro r
  by_cases hr : (r : ℝ) = 1
  · have hlt : x < (r : ℝ) := hr ▸ lt_of_le_of_ne hx.2 hx1
    have he : ∀ᶠ s : UnitInterval in nhds r, x < (s : ℝ) :=
      continuous_subtype_val.continuousAt.eventually (lt_mem_nhds hlt)
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [he] with s hs
    exact hinge_eq_zero_of_lt hs
  · have he : ∀ᶠ s : UnitInterval in nhds r, (s : ℝ) ≠ 1 :=
      continuous_subtype_val.continuousAt.eventually (eventually_ne_nhds hr)
    have hc : ContinuousAt (fun s : UnitInterval => max (x - (s : ℝ)) 0 / (1 - (s : ℝ))) r :=
      ((continuous_const.sub continuous_subtype_val).max continuous_const).continuousAt.div
        (continuous_const.sub continuous_subtype_val).continuousAt (sub_ne_zero.mpr (Ne.symm hr))
    apply hc.congr_of_eventuallyEq
    filter_upwards [he] with s hs
    simp [hinge, hs]

lemma hinge_integrable (μ : Measure UnitInterval) [IsFiniteMeasure μ]
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : Integrable (fun r => hinge r x) μ := by
  apply Integrable.of_bound (continuous_hinge_parameter hx).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro r
  rw [Real.norm_eq_abs, abs_of_nonneg (hinge_nonneg r hx)]
  exact (hinge_le_id r hx).trans hx.2

/-- Bounded difference-quotient tests recovering the entire CDF, including
the atom at zero, without presupposing differentiability of the mixture. -/
noncomputable def cdfTest (x y : ℝ) (r : UnitInterval) : ℝ :=
  hinge r x + (1 - x) / (y - x) * (hinge r y - hinge r x)

lemma cdfTest_eq_one {x y : ℝ} (hxy : x < y) (hy : y ≤ 1)
    {r : UnitInterval} (hr : (r : ℝ) ≤ x) : cdfTest x y r = 1 := by
  have hr1 : (r : ℝ) ≠ 1 := ne_of_lt (hr.trans_lt (hxy.trans_le hy))
  simp only [cdfTest, hinge, hr1, ↓reduceIte,
    max_eq_left (sub_nonneg.mpr hr), max_eq_left (sub_nonneg.mpr (hr.trans hxy.le))]
  field_simp
  <;> ring

lemma cdfTest_bounds {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hy : y < 1)
    (r : UnitInterval) : 0 ≤ cdfTest x y r ∧ cdfTest x y r ≤ 1 := by
  by_cases hr : (r : ℝ) ≤ x
  · rw [cdfTest_eq_one hxy hy.le hr]
    exact ⟨zero_le_one, le_rfl⟩
  have hxr : x < (r : ℝ) := lt_of_not_ge hr
  have hx0 : hinge r x = 0 := hinge_eq_zero_of_lt hxr
  by_cases hry : y ≤ (r : ℝ)
  · have hy0 : hinge r y = 0 := by
      by_cases h : y = (r : ℝ)
      · have hr1 : (r : ℝ) ≠ 1 := ne_of_lt (h ▸ hy)
        simp [hinge, hr1, h]
      · exact hinge_eq_zero_of_lt (lt_of_le_of_ne hry h)
    simp [cdfTest, hx0, hy0]
  · have hry' : (r : ℝ) < y := lt_of_not_ge hry
    have hr1 : (r : ℝ) ≠ 1 := ne_of_lt (hry'.trans hy)
    have hd : 0 < 1 - (r : ℝ) := sub_pos.mpr (hry'.trans hy)
    have hdx : 0 < y - x := sub_pos.mpr hxy
    have h1x : 0 < 1 - x := sub_pos.mpr (hxy.trans hy)
    have he : cdfTest x y r = (1 - x) * (y - (r : ℝ)) / ((y - x) * (1 - (r : ℝ))) := by
      rw [cdfTest, hx0]
      simp only [hinge, hr1, ↓reduceIte,
        max_eq_left (sub_nonneg.mpr hry'.le), sub_zero, zero_add]
      exact div_mul_div_comm _ _ _ _
    rw [he]
    constructor
    · positivity
    · apply (div_le_one (mul_pos (sub_pos.mpr hxy) hd)).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hxr.le) (sub_nonneg.mpr hy.le)]

lemma tendsto_cdfTest {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) (r : UnitInterval) :
    Tendsto (fun y => cdfTest x y r) (𝓝[>] x)
      (𝓝 (if (r : ℝ) ≤ x then 1 else 0)) := by
  by_cases hr : (r : ℝ) ≤ x
  · simp only [hr, ↓reduceIte]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ge_mem_nhds hx.2)] with y hxy hy
    exact (cdfTest_eq_one hxy hy hr).symm
  · simp only [hr, ↓reduceIte]
    apply tendsto_const_nhds.congr'
    have hxr : x < (r : ℝ) := lt_of_not_ge hr
    filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hxr)] with y hy
    simp [cdfTest, hinge_eq_zero_of_lt hxr, hinge_eq_zero_of_lt hy]

lemma cdfTest_integrable (μ : Measure UnitInterval) [IsFiniteMeasure μ]
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    Integrable (cdfTest x y) μ :=
  (hinge_integrable μ hx).add
    (((hinge_integrable μ hy).sub (hinge_integrable μ hx)).const_mul _)

lemma integral_cdfTest (μ : Measure UnitInterval) [IsFiniteMeasure μ]
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    (∫ r, cdfTest x y r ∂μ) =
      mixture μ x + (1 - x) / (y - x) * (mixture μ y - mixture μ x) := by
  unfold cdfTest
  calc
    _ = (∫ r, hinge r x ∂μ) +
        (∫ r, (1 - x) / (y - x) * (hinge r y - hinge r x) ∂μ) :=
      integral_add (hinge_integrable μ hx)
        (((hinge_integrable μ hy).sub (hinge_integrable μ hx)).const_mul _)
    _ = _ := by
      rw [integral_const_mul, integral_sub (hinge_integrable μ hy) (hinge_integrable μ hx)]
      rfl

/-- Recover every cumulative mass below 1 from the represented function.
In particular x=0 recovers the lower endpoint atom. -/
lemma cumulative_recovery (μ : Measure UnitInterval) [IsFiniteMeasure μ]
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    Tendsto (fun y => mixture μ x + (1 - x) / (y - x) * (mixture μ y - mixture μ x))
      (𝓝[>] x) (𝓝 (μ.real {r : UnitInterval | (r : ℝ) ≤ x})) := by
  have he : ∀ᶠ y : ℝ in 𝓝[>] x, x < y ∧ y < 1 := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hx.2)]
      with y hy hy1
    exact ⟨hy, hy1⟩
  have hlim : Tendsto (fun y => ∫ r, cdfTest x y r ∂μ) (𝓝[>] x)
      (𝓝 (∫ r : UnitInterval, if (r : ℝ) ≤ x then (1 : ℝ) else 0 ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · filter_upwards [he] with y hy
      exact (cdfTest_integrable μ ⟨hx.1, hx.2.le⟩ ⟨hx.1.trans hy.1.le, hy.2.le⟩).aestronglyMeasurable
    · filter_upwards [he] with y hy
      apply Eventually.of_forall
      intro r
      rw [Real.norm_eq_abs, abs_of_nonneg (cdfTest_bounds hx.1 hy.1 hy.2 r).1]
      exact (cdfTest_bounds hx.1 hy.1 hy.2 r).2
    · exact integrable_const _
    · exact Eventually.of_forall (tendsto_cdfTest hx)
  have hi : (∫ r : UnitInterval, if (r : ℝ) ≤ x then (1 : ℝ) else 0 ∂μ) =
      μ.real {r : UnitInterval | (r : ℝ) ≤ x} := by
    exact integral_indicator_one (measurableSet_le measurable_subtype_coe measurable_const)
  rw [hi] at hlim
  apply hlim.congr'
  filter_upwards [he] with y hy
  exact integral_cdfTest μ ⟨hx.1, hx.2.le⟩ ⟨hx.1.trans hy.1.le, hy.2.le⟩

/-- Equality of the hinge mixture determines the measure, including both
endpoint atoms and the complete interior Borel restriction. -/
lemma mixture_injective (μ ν : Measure UnitInterval)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x ∈ Icc (0 : ℝ) 1, mixture μ x = mixture ν x) : μ = ν := by
  apply Measure.ext_of_Iic
  intro r
  by_cases hr : (r : ℝ) = 1
  · have hi : Iic r = (univ : Set UnitInterval) := by
      ext s
      simp only [mem_Iic, mem_univ, iff_true]
      show (s : ℝ) ≤ (r : ℝ)
      rw [hr]
      exact s.property.2
    simp [hi]
  · have hx : (r : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨r.property.1, lt_of_le_of_ne r.property.2 hr⟩
    have hlim := cumulative_recovery μ hx
    have hlim' := cumulative_recovery ν hx
    have hlim'' : Tendsto (fun y => mixture μ (r : ℝ) + (1 - (r : ℝ)) / (y - (r : ℝ)) *
        (mixture μ y - mixture μ (r : ℝ))) (𝓝[>] (r : ℝ))
        (𝓝 (ν.real {s : UnitInterval | (s : ℝ) ≤ (r : ℝ)})) := by
      apply hlim'.congr'
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (ge_mem_nhds hx.2)] with y hy hy1
      rw [h _ r.property, h y ⟨hx.1.trans hy.le, hy1⟩]
    have heq := tendsto_nhds_unique hlim hlim''
    change (μ (Iic r)).toReal = (ν (Iic r)).toReal at heq
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp heq

lemma representing_measure_unique {f : ℝ → ℝ} {μ ν : Measure UnitInterval}
    (hμ : Represents μ f) (hν : Represents ν f) : μ = ν := by
  letI := hμ.1
  letI := hν.1
  apply mixture_injective μ ν
  intro x hx
  exact (hμ.2.2 x hx).2.symm.trans (hν.2.2 x hx).2

lemma mixture_left_limit (μ : Measure UnitInterval) [IsProbabilityMeasure μ] :
    Tendsto (mixture μ) (𝓝[<] (1 : ℝ))
      (𝓝 (1 - μ.real {r : UnitInterval | (r : ℝ) = 1})) := by
  have he : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), x ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (le_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx hx0
    exact ⟨hx0, hx.le⟩
  have hlim : Tendsto (mixture μ) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ r : UnitInterval, if (r : ℝ) = 1 then (0 : ℝ) else 1 ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · filter_upwards [he] with x hx
      exact (hinge_integrable μ hx).aestronglyMeasurable
    · filter_upwards [he] with x hx
      apply Eventually.of_forall
      intro r
      rw [Real.norm_eq_abs, abs_of_nonneg (hinge_nonneg r hx)]
      exact (hinge_le_id r hx).trans hx.2
    · exact integrable_const _
    · apply Eventually.of_forall
      intro r
      by_cases hr : (r : ℝ) = 1
      · simp only [hr, ↓reduceIte]
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp [hinge, hr, ne_of_lt (show x < 1 from hx)]
      · simp only [hr, ↓reduceIte]
        have hc : Continuous (hinge r) := by
          unfold hinge
          simp only [hr, ↓reduceIte]
          exact ((continuous_id.sub continuous_const).max continuous_const).div_const _
        have hct : ContinuousAt (hinge r) 1 := hc.continuousAt
        simpa only [hinge_one] using hct.tendsto.mono_left nhdsWithin_le_nhds
  have hi : (∫ r : UnitInterval, if (r : ℝ) = 1 then (0 : ℝ) else 1 ∂μ) =
      1 - μ.real {r : UnitInterval | (r : ℝ) = 1} := by
    have hm : MeasurableSet {r : UnitInterval | (r : ℝ) = 1} :=
      isClosed_eq continuous_subtype_val continuous_const |>.measurableSet
    calc
      _ = μ.real ({r : UnitInterval | (r : ℝ) = 1}ᶜ) := by
        convert integral_indicator_one hm.compl using 1
        congr 1
        funext r
        simp only [Set.indicator, mem_compl_iff, mem_setOf_eq]
        split_ifs <;> rfl
      _ = _ := by rw [measureReal_compl hm, probReal_univ]
  rwa [hi] at hlim

theorem recovery : Recovery := by
  intro f μ hμ
  letI := hμ.1
  have heq (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : f x = mixture μ x := (hμ.2.2 x hx).2
  have he0 : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), y ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with y hy hy1
    exact ⟨hy.le, hy1⟩
  have hz : mixture μ 0 = 0 := by simp [mixture]
  have hset : {r : UnitInterval | (r : ℝ) ≤ 0} = {r : UnitInterval | (r : ℝ) = 0} := by
    ext r
    exact ⟨fun h => le_antisymm h r.property.1, fun h => h.le⟩
  refine ⟨?_, ?_, ?_⟩
  · have hlim := cumulative_recovery μ (show (0 : ℝ) ∈ Ico (0 : ℝ) 1 by norm_num)
    simp only [hz, sub_zero, zero_add, one_div, hset] at hlim
    apply hlim.congr'
    filter_upwards [he0] with y hy
    rw [heq y hy]
    ring
  · apply (mixture_left_limit μ).congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (le_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with y hy hy0
    exact (heq y ⟨hy0, hy.le⟩).symm
  · intro x hx
    apply (cumulative_recovery μ hx).congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (ge_mem_nhds hx.2)] with y hy hy1
    rw [heq x ⟨hx.1, hx.2.le⟩, heq y ⟨hx.1.trans hy.le, hy1⟩]

private lemma summation_by_parts (u d v : ℕ → ℝ) (hd0 : d 0 = 0)
    (n : ℕ) (h : ∀ i < n, d (i+1) * (u (i+1) - u i) = v (i+1) - v i) (t : ℝ) :
    (∑ i ∈ Finset.range n, (d (i+1) - d i) * (t - u i)) =
      d n * (t - u n) + v n - v 0 := by
  induction n with
  | zero => simp [hd0]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]
    have := h n (Nat.lt_succ_self n)
    nlinarith

/-- Exact interpolation of convex nodal data by a finite hinge mixture. -/
lemma ordered_interpolation (f : ℝ → ℝ) (hf : Normalized f)
    (n : ℕ) (hn : 0 < n) (u : ℕ → UnitInterval)
    (hu : ∀ i j, i < j → j ≤ n → (u i : ℝ) < (u j : ℝ))
    (h0 : (u 0 : ℝ) = 0) (h1 : (u n : ℝ) = 1) :
    ∃ μ : ProbabilityMeasure UnitInterval,
      ∀ j ≤ n, mixture (μ : Measure UnitInterval) (u j : ℝ) = f (u j : ℝ) := by
  let d : ℕ → ℝ := fun i => if i = 0 then 0 else
    (f (u i : ℝ) - f (u (i-1) : ℝ)) / ((u i : ℝ) - (u (i-1) : ℝ))
  let w : ℕ → ℝ := fun i => (1 - (u i : ℝ)) * (d (i+1) - d i)
  have hd0 : d 0 = 0 := by simp [d]
  have hd (i : ℕ) : d (i+1) =
      (f (u (i+1) : ℝ) - f (u i : ℝ)) / ((u (i+1) : ℝ) - (u i : ℝ)) := by simp [d]
  have hdiff (i : ℕ) (hi : i < n) :
      d (i+1) * ((u (i+1) : ℝ) - (u i : ℝ)) = f (u (i+1) : ℝ) - f (u i : ℝ) := by
    rw [hd, div_mul_cancel₀ _ (sub_ne_zero.mpr (hu i (i+1) (Nat.lt_succ_self i) hi).ne')]
  have hw (i : ℕ) (hi : i < n) : 0 ≤ w i := by
    apply mul_nonneg (sub_nonneg.mpr (u i).property.2)
    apply sub_nonneg.mpr
    cases i with
    | zero =>
      rw [hd0, hd]
      apply div_nonneg
      · rw [h0, hf.2.2.1, sub_zero]
        exact hf.1 _ (u 1).property
      · exact sub_nonneg.mpr (hu 0 1 (by omega) hi).le
    | succ i =>
      rw [hd, hd]
      exact hf.2.1.slope_mono_adjacent (u i).property (u (i+1+1)).property
        (hu i (i+1) (by omega) (by omega)) (hu (i+1) (i+1+1) (by omega) hi)
  have hvalue (j : ℕ) (hj : j ≤ n) :
      (∑ i ∈ Finset.range n, w i * hinge (u i) (u j : ℝ)) = f (u j : ℝ) := by
    calc
      _ = ∑ i ∈ Finset.range j, w i * hinge (u i) (u j : ℝ) := by
        symm
        apply Finset.sum_subset (Finset.range_mono hj)
        intro i hi hij
        have hin : i < n := Finset.mem_range.mp hi
        have hji : j ≤ i := by simpa using hij
        have hr1 : (u i : ℝ) ≠ 1 := by
          rw [← h1]
          exact (hu i n hin le_rfl).ne
        have hle : (u j : ℝ) ≤ (u i : ℝ) := by
          rcases hji.eq_or_lt with rfl | hji
          · exact le_rfl
          · exact (hu j i hji hin.le).le
        simp [hinge, hr1, max_eq_right (sub_nonpos.mpr hle)]
      _ = ∑ i ∈ Finset.range j, (d (i+1) - d i) * ((u j : ℝ) - (u i : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        have hin : i < n := hij.trans_le hj
        have hle := (hu i j hij hj).le
        have hr1 : (u i : ℝ) ≠ 1 := by rw [← h1]; exact (hu i n hin le_rfl).ne
        simp only [w, hinge, hr1, ↓reduceIte, max_eq_left (sub_nonneg.mpr hle)]
        field_simp
        <;> ring
      _ = f (u j : ℝ) := by
        rw [summation_by_parts (fun i => (u i : ℝ)) d (fun i => f (u i : ℝ))
          hd0 j (fun i hi => hdiff i (hi.trans_le hj)) (u j : ℝ)]
        simp [h0, hf.2.2.1]
  have hsum : (∑ i ∈ Finset.range n, w i) = 1 := by
    simpa only [h1, hinge_one, mul_one, hf.2.2.2] using hvalue n le_rfl
  let μ : Measure UnitInterval := ∑ i ∈ Finset.range n, (w i).toNNReal • Measure.dirac (u i)
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _)]
    change (∑ i ∈ Finset.range n, (↑(w i).toNNReal : ℝ≥0∞) * 1) = 1
    simp only [mul_one]
    change (∑ i ∈ Finset.range n, ENNReal.ofReal (w i)) = 1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => hw i (Finset.mem_range.mp hi)), hsum,
      ENNReal.ofReal_one]
  refine ⟨⟨μ, hprob⟩, ?_⟩
  intro j hj
  change (∫ r, hinge r (u j : ℝ) ∂μ) = _
  dsimp only [μ]
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_nnreal_measure, integral_dirac]
    change (∑ i ∈ Finset.range n, ((w i).toNNReal : ℝ) * hinge (u i) (u j : ℝ)) = _
    convert hvalue j hj using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.toNNReal_of_nonneg (hw i (Finset.mem_range.mp hi))]
    rfl
  · intro i hi
    exact hinge_integrable _ (u j).property

/- For sorted nodes 0=x₀<...<xₙ=1, use masses
(1-xᵢ)(sᵢ-sᵢ₋₁), where sᵢ are the adjacent secant slopes and s₋₁=0.
No continuity at 1 may be added. -/
lemma finite_interpolation (f : ℝ → ℝ) (hf : Normalized f) (s : Finset UnitInterval) :
    ∃ μ : ProbabilityMeasure UnitInterval,
      ∀ x ∈ s, mixture (μ : Measure UnitInterval) (x : ℝ) = f (x : ℝ) := by
  classical
  let z : UnitInterval := ⟨0, by norm_num⟩
  let o : UnitInterval := ⟨1, by norm_num⟩
  let t : Finset UnitInterval := insert z (insert o s)
  have hz : z ∈ t := by simp [t]
  have ho : o ∈ t := by simp [t]
  have hzo : z ≠ o := by intro h; have := congrArg Subtype.val h; norm_num [z, o] at this
  have hcard : 2 ≤ t.card := Finset.one_lt_card.mpr ⟨z, hz, o, ho, hzo⟩
  let n : ℕ := t.card - 1
  have hcard' : t.card = n + 1 := by dsimp [n]; omega
  let e : Fin (n+1) ≃o t := t.orderIsoOfFin hcard'
  let u : ℕ → UnitInterval := fun i => if hi : i ≤ n then (e ⟨i, by omega⟩).val else z
  have hu_eq (i : ℕ) (hi : i ≤ n) : u i = (e ⟨i, by omega⟩).val := by simp [u, hi]
  have hmono (i j : ℕ) (hij : i < j) (hj : j ≤ n) : (u i : ℝ) < (u j : ℝ) := by
    rw [hu_eq i (hij.le.trans hj), hu_eq j hj]
    exact e.strictMono (show (⟨i, by omega⟩ : Fin (n+1)) < ⟨j, by omega⟩ from hij)
  have h0 : (u 0 : ℝ) = 0 := by
    rw [hu_eq 0 (Nat.zero_le n)]
    apply le_antisymm _ (by exact ((e ⟨0, by omega⟩).val).property.1)
    have he := e.monotone (Fin.zero_le (e.symm ⟨z, hz⟩))
    rw [e.apply_symm_apply] at he
    exact he
  have h1 : (u n : ℝ) = 1 := by
    rw [hu_eq n le_rfl]
    apply le_antisymm (by exact ((e ⟨n, by omega⟩).val).property.2)
    have he := e.monotone (Fin.le_last (e.symm ⟨o, ho⟩))
    rw [e.apply_symm_apply] at he
    exact he
  obtain ⟨μ, hμ⟩ := ordered_interpolation f hf n (by dsimp [n]; omega) u hmono h0 h1
  refine ⟨μ, ?_⟩
  intro x hx
  have hxt : x ∈ t := by simp [t, hx]
  let j : Fin (n+1) := e.symm ⟨x, hxt⟩
  have hj : (j : ℕ) ≤ n := by have := j.isLt; omega
  have hux : u j = x := by
    rw [hu_eq j hj]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hxt⟩)
  simpa only [hux] using hμ j hj

lemma exists_representing_measure (f : ℝ → ℝ) (hf : Normalized f) :
    ∃ μ : Measure UnitInterval, Represents μ f := by
  let t : UnitInterval → Set (ProbabilityMeasure UnitInterval) :=
    fun x => {μ | mixture (μ : Measure UnitInterval) (x : ℝ) = f (x : ℝ)}
  have hclosed (x : UnitInterval) : IsClosed (t x) := by
    exact isClosed_eq
      (ProbabilityMeasure.continuous_integral_continuousMap
        (⟨fun r => hinge r (x : ℝ), continuous_hinge_parameter x.property⟩ :
          C(UnitInterval, ℝ))) continuous_const
  have hfinite (s : Finset UnitInterval) : (⋂ x ∈ s, t x).Nonempty := by
    obtain ⟨μ, hμ⟩ := finite_interpolation f hf s
    refine ⟨μ, ?_⟩
    simpa only [mem_iInter, t, mem_setOf_eq] using hμ
  obtain ⟨μ, hμ⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  refine ⟨μ, inferInstance, inferInstance, ?_⟩
  intro x hx
  refine ⟨hinge_integrable _ hx, ?_⟩
  exact (mem_iInter.mp hμ ⟨x, hx⟩).symm

theorem representation : Representation := by
  intro f hf
  obtain ⟨μ, hμ⟩ := exists_representing_measure f hf
  exact ⟨μ, hμ, fun ν hν => representing_measure_unique hν hμ⟩

theorem converse : Converse := by
  intro μ hμ
  letI : IsProbabilityMeasure μ := hμ
  refine ⟨⟨hμ, inferInstance, fun x hx => ⟨hinge_integrable μ hx, rfl⟩⟩, ?_⟩
  refine ⟨?_, ⟨convex_Icc _ _, ?_⟩, ?_, ?_⟩
  · intro x hx
    exact integral_nonneg (fun r => hinge_nonneg r hx)
  · intro x hx y hy a b ha hb hab
    have hz : a • x + b • y ∈ Icc (0 : ℝ) 1 := (convex_Icc _ _) hx hy ha hb hab
    change (∫ r, hinge r (a • x + b • y) ∂μ) ≤
      a • (∫ r, hinge r x ∂μ) + b • (∫ r, hinge r y ∂μ)
    calc
      _ ≤ ∫ r, a • hinge r x + b • hinge r y ∂μ :=
        integral_mono (hinge_integrable μ hz)
          (((hinge_integrable μ hx).smul a).add ((hinge_integrable μ hy).smul b))
          (fun r => (hinge_convex r).2 hx hy ha hb hab)
      _ = (∫ r, a • hinge r x ∂μ) + (∫ r, b • hinge r y ∂μ) :=
        integral_add ((hinge_integrable μ hx).smul a) ((hinge_integrable μ hy).smul b)
      _ = _ := by rw [integral_smul, integral_smul]
  · simp [mixture]
  · simp [mixture]

/-- An arbitrary function on the actual interval has an ambient extension;
no continuity, measurability, or values outside the interval are imposed. -/
noncomputable def intervalExtend (f : UnitInterval → ℝ) (x : ℝ) : ℝ :=
  if hx : x ∈ Icc (0 : ℝ) 1 then f ⟨x, hx⟩ else 0

@[simp] lemma intervalExtend_coe (f : UnitInterval → ℝ) (x : UnitInterval) :
    intervalExtend f (x : ℝ) = f x := by simp [intervalExtend, x.property]

lemma normalized_intervalExtend {f : UnitInterval → ℝ} (hf : IntervalNormalized f) :
    Normalized (intervalExtend f) := by
  refine ⟨?_, ⟨convex_Icc _ _, ?_⟩, ?_, ?_⟩
  · intro x hx
    simpa only [intervalExtend, dif_pos hx] using hf.1 ⟨x, hx⟩
  · intro x hx y hy a b ha hb hab
    have hz : a * x + b * y ∈ Icc (0 : ℝ) 1 := (convex_Icc _ _) hx hy ha hb hab
    simpa only [smul_eq_mul, intervalExtend, dif_pos hx, dif_pos hy, dif_pos hz] using
      hf.2.1 ⟨x, hx⟩ ⟨y, hy⟩ a b ha hb hab
  · simpa [intervalExtend] using hf.2.2.1
  · simpa [intervalExtend] using hf.2.2.2

theorem subtype_representation : SubtypeRepresentation := by
  intro f hf
  obtain ⟨μ, hμ, huniq⟩ := representation (intervalExtend f) (normalized_intervalExtend hf)
  refine ⟨μ, ⟨hμ.1, hμ.2.1, ?_⟩, ?_⟩
  · intro x
    simpa only [intervalExtend_coe] using hμ.2.2 (x : ℝ) x.property
  · intro ν hν
    apply huniq
    refine ⟨hν.1, hν.2.1, ?_⟩
    intro x hx
    simpa only [intervalExtend, dif_pos hx] using hν.2.2 ⟨x, hx⟩

theorem subtype_converse : SubtypeConverse := by
  intro μ hμ
  obtain ⟨hr, hn⟩ := converse μ hμ
  refine ⟨⟨hr.1, hr.2.1, fun x => hr.2.2 (x : ℝ) x.property⟩,
    ⟨fun x => hn.1 (x : ℝ) x.property, ?_, hn.2.2.1, hn.2.2.2⟩⟩
  intro x y a b ha hb hab
  exact hn.2.1.2 x.property y.property ha hb hab

end ExpandedFA.Supplements.ConvexFunctionRepresentation
