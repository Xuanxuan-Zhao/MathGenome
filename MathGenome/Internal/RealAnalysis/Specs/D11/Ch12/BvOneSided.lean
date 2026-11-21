import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvDefinition
import Mathlib.Analysis.Normed.Group.Uniform

/-! Independent statements for paper.tex:3892, one-sided limits of BV functions.

The complete normed additive group formulation includes both ℝ and ℂ. Compact
interval functions use the ambient representation established for all interval
functions by `interval_domain_type` in the upstream Spec. Discontinuity at an
endpoint is relative to the closed interval. The ranges `Ioc` and `Ico` include
the relevant endpoints and exclude the endpoint with no corresponding side.

Global BV is defined by the supremum of the *classical partition variations*,
without any continuity, normalization, or assumed limit. Each finite increasing
partition occurs in its endpoint interval. Conversely every interval partition
is a global finite increasing partition. Thus this is the literal global scope.
-/

open Set Filter
open scoped Topology ENNReal

namespace Specs.D11.Ch12

abbrev globalVariation_type := {E : Type*} → [NormedAddCommGroup E] →
  (ℝ → E) → ℝ≥0∞

noncomputable def globalVariation_value : globalVariation_type :=
  fun F => ⨆ a : ℝ, ⨆ b : ℝ, variation_value F a b

abbrev GloballyBV_type := {E : Type*} → [NormedAddCommGroup E] → (ℝ → E) → Prop

def GloballyBV_value : GloballyBV_type := fun F => globalVariation_value F < ⊤

def global_variation_bridge_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E),
    globalVariation_value F = eVariationOn F univ

def global_bv_bridge_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E),
    GloballyBV_value F ↔ BoundedVariationOn F univ

/-- Finite limits in the scalar space, including the left limit at b and the
right limit at a. The unrestricted strict one-sided filters make these actual
one-sided limits, rather than limits along a possibly empty set. -/
def compact_one_sided_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E) {a b : ℝ}, a < b → BV_value F a b →
      (∀ x ∈ Ioc a b, ∃ l : E, Tendsto F (𝓝[<] x) (𝓝 l)) ∧
      (∀ x ∈ Ico a b, ∃ r : E, Tendsto F (𝓝[>] x) (𝓝 r))

def compact_countable_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) {a b : ℝ},
    a ≤ b → BV_value F a b →
      {x ∈ Icc a b | ¬ ContinuousWithinAt F (Icc a b) x}.Countable

/-- No limit at infinity is part of the hypothesis. -/
def global_limits_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E), GloballyBV_value F →
      (∃ l : E, Tendsto F atBot (𝓝 l)) ∧
      (∃ r : E, Tendsto F atTop (𝓝 r))

def global_countable_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E),
    GloballyBV_value F → {x | ¬ ContinuousAt F x}.Countable

def global_one_sided_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E), GloballyBV_value F →
      ∀ x : ℝ, Tendsto F (𝓝[<] x) (𝓝 (F.leftLim x)) ∧
        Tendsto F (𝓝[>] x) (𝓝 (F.rightLim x))

/-- The chosen `rightLim` is proved to be a limit at every point, so the
countability assertion is about genuine right limits, not fallback values. -/
def right_limit_replacement_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E), GloballyBV_value F →
      (∀ x : ℝ, Tendsto F (𝓝[>] x) (𝓝 (F.rightLim x))) ∧
      {x | F.rightLim x ≠ F x}.Countable

end Specs.D11.Ch12
