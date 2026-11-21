import MathGenome.Internal.RealAnalysis.D11.Ch12.BvDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvOneSided
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-! One-sided limits and countable discontinuities, paper.tex:3892.

We use the metric-space BV limit and countability theorems. In particular the
global limit proof uses finite variation directly, with no presupposed limits
or normalized Jordan decomposition. All results apply to both real and complex
functions (and more generally to complete normed additive groups).
-/

namespace D11.Ch12
open Set Filter
open scoped Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E]

/-- Supremum over all classical finite increasing partitions on ℝ. -/
noncomputable def globalVariation (F : ℝ → E) : ℝ≥0∞ :=
  ⨆ a : ℝ, ⨆ b : ℝ, variation F a b

/-- Finite global partition variation; no limits are assumed. -/
def GloballyBV (F : ℝ → E) : Prop := globalVariation F < ⊤

theorem globalVariation_eq_eVariationOn (F : ℝ → E) :
    globalVariation F = eVariationOn F univ := by
  simp only [globalVariation, variation_eq_eVariationOn]
  apply le_antisymm
  · exact iSup_le fun a => iSup_le fun b => eVariationOn.mono F (subset_univ _)
  · rw [eVariationOn]
    apply iSup_le
    rintro ⟨n, u, hu, _⟩
    apply le_trans (eVariationOn.sum_le_of_monotoneOn_Iic (hu.monotoneOn _) ?_)
    · exact le_iSup_of_le (u 0) (le_iSup_of_le (u n) le_rfl)
    · intro i hi
      exact ⟨hu (Nat.zero_le _), hu hi⟩

theorem globallyBV_iff_boundedVariationOn (F : ℝ → E) :
    GloballyBV F ↔ BoundedVariationOn F univ := by
  simp [GloballyBV, globalVariation_eq_eVariationOn, BoundedVariationOn, lt_top_iff_ne_top]

/-- Interior left/right limits and the corresponding endpoint limits. -/
theorem bv_one_sided_limits [CompleteSpace E] (F : ℝ → E) {a b : ℝ}
    (_hab : a < b) (hf : BV F a b) :
    (∀ x ∈ Ioc a b, ∃ l : E, Tendsto F (𝓝[<] x) (𝓝 l)) ∧
    (∀ x ∈ Ico a b, ∃ r : E, Tendsto F (𝓝[>] x) (𝓝 r)) := by
  have hb := (bv_iff_boundedVariationOn F a b).mp hf
  constructor
  · intro x hx
    simpa only [nhdsWithin_inter_of_mem (Icc_mem_nhdsLT_of_mem hx)] using
      hb.exists_tendsto_left x
  · intro x hx
    simpa only [nhdsWithin_inter_of_mem (Icc_mem_nhdsGT_of_mem hx)] using
      hb.exists_tendsto_right x

/-- Countability includes relative discontinuities at either endpoint. -/
theorem bv_countable_discontinuities (F : ℝ → E) {a b : ℝ}
    (_hab : a ≤ b) (hf : BV F a b) :
    {x ∈ Icc a b | ¬ ContinuousWithinAt F (Icc a b) x}.Countable := by
  have hb : BoundedVariationOn (fun x : Icc a b => F x) univ := by
    rw [BoundedVariationOn, variation_restrict]
    exact ne_of_lt hf
  apply (hb.countable_not_continuousAt.image (fun x : Icc a b => (x : ℝ))).mono
  rintro x ⟨hx, hdisc⟩
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  exact fun hc => hdisc ((continuousWithinAt_iff_continuousAt_domRestrict F hx).mpr hc)

theorem globallyBV_limits_at_infinity [CompleteSpace E] (F : ℝ → E)
    (hf : GloballyBV F) :
    (∃ l : E, Tendsto F atBot (𝓝 l)) ∧
    (∃ r : E, Tendsto F atTop (𝓝 r)) := by
  have hb := (globallyBV_iff_boundedVariationOn F).mp hf
  exact ⟨by simpa using hb.exists_tendsto_atBot, by simpa using hb.exists_tendsto_atTop⟩

theorem globallyBV_countable_discontinuities (F : ℝ → E) (hf : GloballyBV F) :
    {x | ¬ ContinuousAt F x}.Countable :=
  ((globallyBV_iff_boundedVariationOn F).mp hf).countable_not_continuousAt

/-- Both canonical one-sided limits are genuine limits at every real point. -/
theorem globallyBV_one_sided_limits [CompleteSpace E] (F : ℝ → E)
    (hf : GloballyBV F) :
    ∀ x : ℝ, Tendsto F (𝓝[<] x) (𝓝 (F.leftLim x)) ∧
      Tendsto F (𝓝[>] x) (𝓝 (F.rightLim x)) := by
  have hb := (globallyBV_iff_boundedVariationOn F).mp hf
  exact fun x => ⟨hb.tendsto_leftLim x, hb.tendsto_rightLim x⟩

/-- Replacing F by its genuine right limit changes only countably many values. -/
theorem globallyBV_right_limit_replacement [CompleteSpace E] (F : ℝ → E)
    (hf : GloballyBV F) :
    (∀ x : ℝ, Tendsto F (𝓝[>] x) (𝓝 (F.rightLim x))) ∧
    {x | F.rightLim x ≠ F x}.Countable := by
  have hb := (globallyBV_iff_boundedVariationOn F).mp hf
  refine ⟨hb.tendsto_rightLim, (globallyBV_countable_discontinuities F hf).mono ?_⟩
  intro x hx hc
  exact hx hc.continuousWithinAt.rightLim_eq

end D11.Ch12
