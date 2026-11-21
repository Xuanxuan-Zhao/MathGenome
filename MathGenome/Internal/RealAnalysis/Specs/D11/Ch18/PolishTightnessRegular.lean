import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.PolishCompactTightness

/-!
Independent statements for paper.tex:5402–5411,
`d11:18:polish-tightness-regular`.

The measurable structure is exactly the Borel sigma-algebra of the given
complete separable metric space. Only finite total mass is assumed. In
particular, neither local compactness nor a regularity/tightness instance is
an input. Errors are arbitrary positive real numbers. Empty spaces and the
zero measure are included.
-/

namespace Specs.D11.Ch18.PolishTightnessRegular

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

/-- Compact tightness of every finite Borel measure under the source hypotheses. -/
def compact_tightness : Prop :=
  ∀ {X : Type u} [MetricSpace X] [CompleteSpace X] [SeparableSpace X]
    (μ : @Measure X (borel X)), μ univ < ∞ →
      ∀ (ε : ℝ), 0 < ε →
        ∃ K : Set X, IsCompact K ∧ μ (univ \ K) < ENNReal.ofReal ε

/-- Every Borel set has compact inner and open outer approximations with both
strict difference estimates. -/
def polish_tightness_regular : Prop :=
  ∀ {X : Type u} [MetricSpace X] [CompleteSpace X] [SeparableSpace X]
    (μ : @Measure X (borel X)), μ univ < ∞ →
      ∀ (E : Set X), MeasurableSet[borel X] E →
        ∀ (ε : ℝ), 0 < ε →
          ∃ K U : Set X, IsCompact K ∧ IsOpen U ∧ K ⊆ E ∧ E ⊆ U ∧
            μ (E \ K) < ENNReal.ofReal ε ∧ μ (U \ E) < ENNReal.ofReal ε

end Specs.D11.Ch18.PolishTightnessRegular
